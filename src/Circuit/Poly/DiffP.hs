{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Bridging parameterised reverse-mode AD ('DiffP') and polynomial monomial
-- lenses.
--
-- A 'DiffP p a b' is a /parametric/ lens: for every parameter value @p@ it
-- gives an ordinary lens @Mono a a -> Mono b b@, and it additionally produces
-- a parameter gradient @dp@. In 'Poly' this is naturally expressed via the
-- copower 'Depend': a parameter-indexed family of lenses.
--
-- This gives the "shared parameter" reading of 'DiffP' a home in 'Poly': the
-- parameter is the index of a lens family, not an extra layer. The
-- paired-parameter reading ('Circuit.Diff.Param.splitP', 'joinP') remains
-- available for independent-layer composition.
module Circuit.Poly.DiffP
  ( -- * DiffP as a parameter-indexed lens family
    diffPAt,
    diffPAsFamily,
    diffPParamGrad,

    -- * Recover a DiffP from its Poly decomposition
    diffPFromFamily,

    -- * Star-based feedback trace
    traceDiffPFrom,
    traceDiffPD,
    traceDiffPMatrix,
  )
where

import Circuit.Bimonoid (MergeZero, Zero (..))
import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Diff.Param (DiffP (..))
import Circuit.Mat.Dense (Matrix, fromLists, matVec, starMatrix, toLists)
import Circuit.Poly (Mono, Morphism (..), Poly (..), applyLens, lens)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Free.Carriers (FieldStar (..))
import Prelude hiding (id, (.))

-- | The lens at a fixed parameter value.
--
-- Forward: @a -> b@. Backward: @a -> db -> da@.
diffPAt :: DiffP p a b -> p -> Morphism (Mono a a) (Mono b b)
diffPAt (DiffP f) p = lens get put
  where
    get a = fst (f p a)
    put a db = fst (snd (f p a) db)

-- | The parameter gradient extracted from a 'DiffP'.
--
-- For a parameter @p@, input @a@ and output cotangent @db@, return @dp@.
diffPParamGrad :: DiffP p a b -> p -> a -> b -> p
diffPParamGrad (DiffP f) p a db = snd (snd (f p a) db)

-- | View a 'DiffP' as a 'Poly' morphism @Const p * Mono a a -> Mono b b@.
--
-- The parameter is carried by the constant functor; choosing a position @p@
-- selects one lens from the family.
diffPAsFamily :: DiffP p a b -> Morphism ('Prod ('Const p) (Mono a a)) (Mono b b)
diffPAsFamily d = Depend (diffPAt d)

-- | Recover a 'DiffP' from its fixed-parameter lens family and parameter
-- gradient. This is the inverse of the 'diffPAt'/'diffPParamGrad' split.
diffPFromFamily ::
  (p -> Morphism (Mono a a) (Mono b b)) ->
  (p -> a -> b -> p) ->
  DiffP p a b
diffPFromFamily family grad = DiffP $ \p a ->
  let (b, put) = applyLens (family p) a
   in (b, \db -> (put db, grad p a db))

-- | Cartesian strength for 'DiffP'.
--
-- Threads a plain morphism through the feedback channel, copying the
-- parameter gradient unchanged.
instance (MergeZero (->) p) => Strength (,) (DiffP p) where
  strength (DiffP f) = DiffP $ \p0 (a, b) ->
    let (c, back) = f p0 b
     in ( (a, c),
          \(da, dc) ->
            let (db, dp) = back dc
             in ((da, db), dp)
        )

-- | Star-based trace for 'DiffP'.
--
-- The forward pass iterates the state channel to a fixed point; the backward
-- pass solves the feedback adjoint using the Kleene star of the channel
-- self-coupling.  This is the Schur-complement view of backpropagation
-- through feedback: for a body @s' = f(s, i), o = g(s, i)@ linearised at
-- the fixed point, the closed gradient is
--
-- > do/di = D + C · star(A) · B
--
-- where @A = ∂s'/∂s@, @B = ∂s'/∂i@, @C = ∂o/∂s@, @D = ∂o/∂i@.
-- The same star appears in the parameter gradient.
traceDiffPFrom ::
  (NHR.StarSemiring j, MergeZero (->) o) =>
  -- | forward seed for the state channel
  j ->
  -- | number of forward iterations
  Int ->
  DiffP p (j, i) (j, o) ->
  DiffP p i o
traceDiffPFrom j0 n (DiffP body) = DiffP $ \p0 i ->
  let stepFwd j = let ((j', _), _) = body p0 (j, i) in j'
      a = iterate stepFwd j0 !! n
      ((_, o), backward) = body p0 (a, i)
      -- Probe the feedback self-coupling @A@ with a unit feedback cotangent.
      ((aJ, _), _) = backward (NHM.one, zero ())
      aStar = NHR.star aJ
      pullback do_ =
        let -- Cross-coupling @B · do_@ for this particular output cotangent.
            cdc = fst (fst (backward (NHA.zero, do_)))
            dj = aStar NHM.* cdc
            ((_, di), dp) = backward (dj, do_)
         in (di, dp)
   in (o, pullback)

-- | 'traceDiffPFrom' specialised to a scalar 'Double' state channel.
--
-- The primal is iterated until @|s' - s| <= tol@ or @maxIter@ is reached.
-- The feedback Jacobian @A@ is then probed and guarded: @|A| >= 1@ is
-- rejected with an error, because outside the contractive regime the star
-- @1/(1-A)@ either diverges or inverts the sign.  This closes the §7
-- silent-failure gap for the scalar case.
traceDiffPD ::
  (MergeZero (->) o) =>
  -- | forward seed for the state channel
  Double ->
  -- | residual tolerance for the primal fixed point
  Double ->
  -- | maximum number of forward iterations
  Int ->
  DiffP p (Double, i) (Double, o) ->
  DiffP p i o
traceDiffPD j0 tol maxIter (DiffP body) = DiffP $ \p0 i ->
  let stepFwd j = let ((j', _), _) = body p0 (j, i) in j'
      go 0 j = j
      go n j =
        let j' = stepFwd j
         in if abs (j' - j) <= tol then j' else go (n - 1) j'
      a = go maxIter j0
      aNext = stepFwd a
      ((_, o), backward) = body p0 (a, i)
      -- Probe the feedback self-coupling @A@ with a unit feedback cotangent.
      ((aJ, _), _) = backward (1.0, zero ())
      aStar = recip (1 - aJ)
      pullback do_ =
        let -- Cross-coupling @B · do_@ for this particular output cotangent.
            cdc = fst (fst (backward (0.0, do_)))
            dj = aStar * cdc
            ((_, di), dp) = backward (dj, do_)
         in (di, dp)
   in if abs (aNext - a) > tol
        then error ("traceDiffPD: primal fixed point did not converge within " ++ show maxIter ++ " iterations")
        else
          if abs aJ >= 1.0
            then error ("traceDiffPD: feedback Jacobian |" ++ show aJ ++ "| >= 1 is outside the contractive regime")
            else (o, pullback)

-- | Star-based trace for a vector-channel 'DiffP'.
--
-- The state channel is a list @[[Double]]@ of fixed dimension.  The forward pass
-- iterates to a fixed point; the backward pass probes the feedback Jacobian
-- column by column, builds a 'Matrix', and solves the adjoint with
-- 'starMatrix'.  Each column is wrapped in 'FieldStar' so the matrix star is
-- honest @(I − A)⁻¹@.
--
-- This is the multi-agent extension of 'traceDiffPD': instead of a scalar
-- self-coupling @a@, the feedback Jacobian is a matrix @A@, and the star is
-- the Neumann series @(I − A)⁻¹@.
traceDiffPMatrix ::
  (MergeZero (->) o) =>
  -- | forward seed for the state channel (its length is the channel dimension)
  [Double] ->
  -- | residual tolerance for the primal fixed point
  Double ->
  -- | maximum number of forward iterations
  Int ->
  DiffP p ([Double], i) ([Double], o) ->
  DiffP p i o
traceDiffPMatrix x0 tol maxIter (DiffP body) = DiffP $ \p0 i ->
  let dim = length x0
      stepFwd xs = let ((xs', _), _) = body p0 (xs, i) in xs'
      zeroV = replicate dim 0.0
      oneV k = [if j == k then 1.0 else 0.0 | j <- [0 .. dim - 1]]
      diffV = zipWith (-)
      normInf v = maximum (map abs v)
      go 0 xs = xs
      go n xs =
        let xs' = stepFwd xs
         in if normInf (diffV xs' xs) <= tol then xs' else go (n - 1) xs'
      a = go maxIter x0
      aNext = stepFwd a
      ((_, o), backward) = body p0 (a, i)
      -- Probe the feedback self-coupling @A@: column k is the feedback
      -- cotangent vector produced by a unit cotangent on channel k.
      cols = [fst (fst (backward (oneV k, zero ()))) | k <- [0 .. dim - 1]]
      -- Assemble rows: row i is [col_0 !! i, ..., col_{dim-1} !! i].
      aMat = fromLists [[FieldStar (cols !! j !! k) | j <- [0 .. dim - 1]] | k <- [0 .. dim - 1]]
      aStar = fromLists (map (map unFieldStar) (toLists (starMatrix aMat)))
      pullback do_ =
        let -- Cross-coupling @B · do_@ for this particular output cotangent.
            cdc = fst (fst (backward (zeroV, do_)))
            dj = matVec aStar cdc
            ((_, di), dp) = backward (dj, do_)
         in (di, dp)
   in if normInf (diffV aNext a) > tol
        then error ("traceDiffPMatrix: primal fixed point did not converge within " ++ show maxIter ++ " iterations")
        else (o, pullback)
