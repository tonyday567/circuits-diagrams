{-# LANGUAGE DataKinds #-}

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
-- paired-parameter reading ('Circuit.AD.Param.splitP', 'joinP') remains
-- available for independent-layer composition.
module Circuit.Poly.DiffP
  ( -- * DiffP as a parameter-indexed lens family
    diffPAt,
    diffPAsFamily,
    diffPParamGrad,

    -- * Recover a DiffP from its Poly decomposition
    diffPFromFamily,
  )
where

import Circuit.AD.Param (DiffP (..))
import Circuit.Poly (Mono, Morphism, Poly (..), Morphism (..), applyLens, lens)
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
