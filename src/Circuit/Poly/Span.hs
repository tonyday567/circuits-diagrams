{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The span fragment of polynomial functors.
--
-- The standard 'Circuit.Poly' encoding uses type families 'Pos' and 'Dir'.
-- 'Sum' has no 'Dir' row because directions over a sum are position-dependent,
-- and GHC cannot match on the result of a type family inside a GADT or type
-- family equation.
--
-- This module experiments with the alternative: represent a polynomial as a
-- span @Dir -> Pos@.  The position-dependency is carried by an explicit
-- projection function rather than by a dependent type family.  'Sum' becomes
-- the coproduct of spans, so it /does/ admit a netlist view in this encoding.
--
-- The cost is that correctness of the netlist view for 'Prod' becomes a fibre
-- condition: a direction function supplied to 'fromNetC' must return 'Nothing'
-- outside the fibre of the chosen position.  In the double-category picture
-- those fibre conditions are the lower-dimensional cells (companions,
-- conjoints, and the Beck–Chevalley cube).
--
-- The span fragment is the six constructors @CY@, @CConst@, @CExp@, @CSum@,
-- @CProd@ and @CTensor@.  'CComp' is included in the grammar but not in the
-- span fragment: it has a 'NetlistC' view, but no 'SpanC' projection.  See
-- 'loom/cube.md' for the research direction that 'CComp' belongs to.
--
-- The 'ETC' constructor is the netlist view inlined into the value; it is not
-- structural like 'ESC' or 'EPC'.  This makes tensor round-trips exact in the
-- spike, but it is an asymmetry of the encoding, not a mathematical fact about
-- tensors.
module Circuit.Poly.Span
  ( -- * Span descriptions
    Span (..),
    PosC,
    DirC,

    -- * Values
    EvalC (..),

    -- * Span projection (six span constructors)
    SpanC (..),
    onFibreC,

    -- * Netlist view (all seven constructors)
    NetlistC (..),
    netRoundTripC,

    -- * Sum / product distributivity
    prodSumDistrLC,
    prodSumDistrRC,
    distrPosLC,
    distrDirLC,

    -- * Composition product (outside the span fragment)
    nestedToCompC,
    compToNestedC,
    compAssocLC,
    compAssocRC,
  )
where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Void (Void, absurd)
import Prelude

-- | Promoted description of a polynomial as a span @Dir -> Pos@.
--
-- Unlike 'Circuit.Poly.Poly', this grammar does not need a position-indexed
-- 'Dir' family; the projection is supplied by the 'SpanC' class at the term
-- level.
--
-- 'CComp' is in the grammar but outside the span fragment: it has a netlist
-- view, but no span projection.  See 'SpanC' and the module header.
data Span
  = CY
  | CConst Type
  | CExp Type
  | CSum Span Span
  | CProd Span Span
  | CTensor Span Span
  | CComp Span Span

-- | Position set of a span polynomial.
type family PosC (c :: Span) :: Type where
  PosC 'CY = ()
  PosC ('CConst a) = a
  PosC ('CExp a) = ()
  PosC ('CSum p q) = Either (PosC p) (PosC q)
  PosC ('CProd p q) = (PosC p, PosC q)
  PosC ('CTensor p q) = (PosC p, PosC q)
  PosC ('CComp p q) = (PosC p, DirC p -> PosC q)

-- | Total direction space of a span polynomial.
--
-- For 'CProd', the total direction space includes the /other/ position so that
-- the projection to the product of positions is a pure function.  In the
-- double-category picture this is the universal property of the product of
-- spans.
type family DirC (c :: Span) :: Type where
  DirC 'CY = ()
  DirC ('CConst a) = Void
  DirC ('CExp a) = a
  DirC ('CSum p q) = Either (DirC p) (DirC q)
  DirC ('CProd p q) = Either (DirC p, PosC q) (PosC p, DirC q)
  DirC ('CTensor p q) = (DirC p, DirC q)
  DirC ('CComp p q) = (DirC p, DirC q)

-- | Values of a span polynomial functor evaluated at @x@.
--
-- 'ETC' stores the tensor netlist directly: a pair of positions and a curried
-- direction function.  This is not structural like 'ESC' or 'EPC', and it makes
-- the tensor round-trip exact in the spike.  See the module header.
data EvalC (c :: Span) (x :: Type) where
  EYC :: x -> EvalC 'CY x
  EKC :: c -> EvalC ('CConst c) x
  EEC :: (a -> x) -> EvalC ('CExp a) x
  ESC :: Either (EvalC p x) (EvalC q x) -> EvalC ('CSum p q) x
  EPC :: (EvalC p x, EvalC q x) -> EvalC ('CProd p q) x
  ETC :: PosC p -> PosC q -> (DirC p -> DirC q -> x) -> EvalC ('CTensor p q) x
  ECC ::
    (PosC p, DirC p -> PosC q) ->
    ((DirC p, DirC q) -> x) ->
    EvalC ('CComp p q) x

instance Functor (EvalC c) where
  fmap f = \case
    EYC x -> EYC (f x)
    EKC c -> EKC c
    EEC g -> EEC (f . g)
    ESC e -> ESC (bimap (fmap f) (fmap f) e)
    EPC (u, v) -> EPC (fmap f u, fmap f v)
    ETC i j g -> ETC i j (\d e -> f (g d e))
    ECC pos g -> ECC pos (f . g)

-- | Span polynomials: those constructors that admit a projection @Dir -> Pos@.
--
-- 'CComp' is deliberately /not/ an instance.  A single direction @(dp, dq)@
-- does not determine the hang map @'DirC' p -> 'PosC' q@, so there is no
-- function @'DirC' ('CComp' p q) -> 'PosC' ('CComp' p q)@ to write.  This is
-- a mathematical impossibility, not a Haskell limitation; it is documented at
-- the type level by the missing instance.
class SpanC (c :: Span) where
  projC :: DirC c -> PosC c

instance SpanC 'CY where
  projC () = ()

instance SpanC ('CConst a) where
  projC = absurd

instance SpanC ('CExp a) where
  projC _ = ()

instance (SpanC p, SpanC q) => SpanC ('CSum p q) where
  projC = bimap (projC @p) (projC @q)

instance
  (SpanC p, SpanC q) =>
  SpanC ('CProd p q)
  where
  projC = \case
    Left (d, j) -> (projC @p d, j)
    Right (i, e) -> (i, projC @q e)

instance (SpanC p, SpanC q) => SpanC ('CTensor p q) where
  projC = bimap (projC @p) (projC @q)

-- | Polynomials that admit a netlist view in the span encoding.
--
-- The netlist view is @EvalC p x ≅ (PosC p, DirC p -> Maybe x)@, where
-- 'Nothing' means "outside the fibre of the chosen position".
--
-- 'fromNetC' assumes the supplied function respects the fibre.  If it returns
-- 'Nothing' on a direction that is inside the fibre, 'fromNetC' raises an
-- internal error: that is the encoding's assertion of the Beck–Chevalley
-- condition, not user-facing junk.
--
-- Every constructor is an instance, including 'CComp', because a value of any
-- constructor can be stored together with its position and direction function.
-- 'CComp' is not a 'SpanC', so its netlist view is not a span netlist view.
class NetlistC (c :: Span) where
  toNetC :: EvalC c x -> (PosC c, DirC c -> Maybe x)
  fromNetC :: PosC c -> (DirC c -> Maybe x) -> EvalC c x

-- | Internal assertion: a direction that should be in the fibre must carry a
-- value.
expectJust :: Maybe a -> a
expectJust = fromMaybe (error "Span.fromNetC: direction inside fibre returned Nothing")

instance NetlistC 'CY where
  toNetC (EYC x) = ((), \() -> Just x)
  fromNetC () h = EYC (expectJust (h ()))

instance NetlistC ('CConst a) where
  toNetC (EKC c) = (c, absurd)
  fromNetC c _ = EKC c

instance NetlistC ('CExp a) where
  toNetC (EEC g) = ((), Just . g)
  fromNetC () h = EEC (\a -> expectJust (h a))

instance (NetlistC p, NetlistC q) => NetlistC ('CSum p q) where
  toNetC (ESC (Left u)) =
    let (i, f) = toNetC u
     in ( Left i,
          \case
            Left d -> f d
            Right _ -> Nothing
        )
  toNetC (ESC (Right v)) =
    let (j, g) = toNetC v
     in ( Right j,
          \case
            Left _ -> Nothing
            Right e -> g e
        )

  fromNetC (Left i) h = ESC (Left (fromNetC i (\d -> h (Left d))))
  fromNetC (Right j) h = ESC (Right (fromNetC j (\e -> h (Right e))))

instance
  (NetlistC p, NetlistC q, Eq (PosC p), Eq (PosC q)) =>
  NetlistC ('CProd p q)
  where
  toNetC (EPC (u, v)) =
    let (i, f) = toNetC u
        (j, g) = toNetC v
     in ( (i, j),
          \case
            Left (d, j') -> if j' == j then f d else Nothing
            Right (i', e) -> if i' == i then g e else Nothing
        )

  fromNetC (i, j) h =
    EPC
      ( fromNetC i (\d -> h (Left (d, j))),
        fromNetC j (\e -> h (Right (i, e)))
      )

instance NetlistC ('CTensor p q) where
  toNetC (ETC i j g) = ((i, j), Just . uncurry g)
  fromNetC (i, j) h = ETC i j (\d e -> expectJust (h (d, e)))

instance NetlistC ('CComp p q) where
  toNetC (ECC pos g) = (pos, Just . g)
  fromNetC pos h = ECC pos (\de -> expectJust (h de))

-- | Reassemble a value after taking it apart.
--
-- This is the executable form of the round-trip law
-- @'fromNetC' ('toNetC' v) ≡ v@.  It is exact for every constructor.  The
-- reverse direction @'toNetC' ('fromNetC' i h) ≡ (i, h)@ holds exactly when @h@
-- respects the fibre, and fails otherwise.
netRoundTripC :: (NetlistC c) => EvalC c x -> EvalC c x
netRoundTripC v = uncurry fromNetC (toNetC v)

-- | Test whether a direction lies in the fibre of a given position.
--
-- This is the lowest-dimensional fibre law, equivalent to the Beck–Chevalley
-- condition for the identity cell.
onFibreC :: forall c. (Eq (PosC c), SpanC c) => PosC c -> DirC c -> Bool
onFibreC i d = projC @c d == i

-- ** Composition product isomorphisms

-- | Composition-product view of a nested span evaluation.
--
-- Correctness iso (right):
-- @'EvalC' p ('EvalC' q x) ≅ 'EvalC' ('CComp' p q) x@.
--
-- This is the span analogue of 'Circuit.Poly.nestedToComp', but it works
-- through the 'Maybe' netlist view.  Off-fibre directions in the outer
-- polynomial have no canonical @q@-position, so the hang map is only
-- defined on the fibre; this is the same cube boundary as the missing 'SpanC'
-- instance for 'CComp'.
nestedToCompC ::
  (NetlistC p, NetlistC q) =>
  EvalC p (EvalC q x) ->
  EvalC ('CComp p q) x
nestedToCompC v =
  let (i, g) = toNetC v
      cell dp = toNetC (expectJust (g dp))
      hang dp = fst (cell dp)
   in ECC (i, hang) (\(dp, dq) -> expectJust (snd (cell dp) dq))

-- | Nested span evaluation from a composition-product value.
--
-- Correctness iso (left): inverse of 'nestedToCompC'.
compToNestedC ::
  (NetlistC p, NetlistC q) =>
  EvalC ('CComp p q) x ->
  EvalC p (EvalC q x)
compToNestedC (ECC (i, hang) k) =
  fromNetC i (\dp -> Just (fromNetC (hang dp) (\dq -> Just (k (dp, dq)))))

-- | Left associator for the composition product:
-- @((p ◁ q) ◁ r) -> (p ◁ (q ◁ r))@.
compAssocLC ::
  EvalC ('CComp ('CComp p q) r) x ->
  EvalC ('CComp p ('CComp q r)) x
compAssocLC (ECC ((i, f), g) k) =
  ECC
    ( i,
      \dp ->
        let j = f dp
            h dq = g (dp, dq)
         in (j, h)
    )
    (\(dp, (dq, dr)) -> k ((dp, dq), dr))

-- | Right associator for the composition product.
compAssocRC ::
  EvalC ('CComp p ('CComp q r)) x ->
  EvalC ('CComp ('CComp p q) r) x
compAssocRC (ECC (i, h) k) =
  let f dp = fst (h dp)
      g (dp, dq) = snd (h dp) dq
   in ECC ((i, f), g) (\((dp, dq), dr) -> k (dp, (dq, dr)))

-- ** Sum / product distributivity

-- | Left distributivity of 'CProd' over 'CSum':
-- @'CProd' ('CSum' p q) r -> 'CSum' ('CProd' p r) ('CProd' q r)@.
prodSumDistrLC ::
  EvalC ('CProd ('CSum p q) r) x ->
  EvalC ('CSum ('CProd p r) ('CProd q r)) x
prodSumDistrLC (EPC (ESC (Left u), w)) = ESC (Left (EPC (u, w)))
prodSumDistrLC (EPC (ESC (Right v), w)) = ESC (Right (EPC (v, w)))

-- | Right distributivity of 'CProd' over 'CSum':
-- @'CSum' ('CProd' p r) ('CProd q r) -> 'CProd' ('CSum' p q) r@.
prodSumDistrRC ::
  EvalC ('CSum ('CProd p r) ('CProd q r)) x ->
  EvalC ('CProd ('CSum p q) r) x
prodSumDistrRC (ESC (Left (EPC (u, w)))) = EPC (ESC (Left u), w)
prodSumDistrRC (ESC (Right (EPC (v, w)))) = EPC (ESC (Right v), w)

-- | Position isomorphism for the left distributivity of 'CProd' over 'CSum'.
distrPosLC ::
  PosC ('CProd ('CSum p q) r) ->
  PosC ('CSum ('CProd p r) ('CProd q r))
distrPosLC (Left i, j) = Left (i, j)
distrPosLC (Right k, j) = Right (k, j)

-- | Direction isomorphism for the left distributivity of 'CProd' over 'CSum'.
distrDirLC ::
  DirC ('CProd ('CSum p q) r) ->
  DirC ('CSum ('CProd p r) ('CProd q r))
distrDirLC = \case
  Left (Left dp, j) -> Left (Left (dp, j))
  Left (Right dq, j) -> Right (Left (dq, j))
  Right (Left i, e) -> Left (Right (i, e))
  Right (Right k, e) -> Right (Right (k, e))
