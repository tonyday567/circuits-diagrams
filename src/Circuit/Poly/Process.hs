{-# LANGUAGE DataKinds #-}

-- | Bridge between polynomial dynamical systems ('Circuit.Poly.System') and
-- 'Circuit.Process.Process' machines.
--
-- A 'System' over a monomial interface @Mono i o@ is a Moore machine: the
-- current state determines the output @i@, and the next input direction @o@
-- determines the next state. 'Circuit.Process.Process' is the same shape, so
-- the two views round-trip exactly.
module Circuit.Poly.Process
  ( systemAsProcess,
    runSystem,
    iterateSystem,
    after,
    systemAsLens,
    lensAsSystem,
    duplicateSystem,
    Coalgebra (..),
    Step,
    coalgebraToSystem,
    composeCoalgebra,
    systemToCoalgebraMono,
    branchSystem,
    runSystemSum,
    branchSystemHet,
    runSystemSumHet,
    SumStep (..),
  )
where

import Circuit.Poly
  ( Eval (..),
    Mono,
    Morphism (..),
    Netlist,
    Poly (..),
    System (..),
    SystemEval,
    applyLens,
    fromEvalSystem,
    lens,
    nestedToComp,
    runMorphism,
    toEvalSystem,
  )
import Circuit.Process (Process (..))
import Prelude hiding (id, (.))

-- | Run a monomial system at a state, exposing the output position and the
-- state-transition function.
runSystem :: System (->) s (Mono i o) -> s -> (i, o -> s)
runSystem sys s = case toEvalSystem sys s of EP (EK i, EE f) -> (i, f)

-- | Convert a monomial 'System' into a 'Process' machine with a given initial
-- state.
--
-- The first input is consumed for the state transition from the supplied
-- initial state, matching the coalgebra intuition of a 'System'.
systemAsProcess :: System (->) s (Mono i o) -> s -> Process o i
systemAsProcess sys s0 =
  Process
    (\o -> snd (runSystem sys s0) o)
    (\s o -> snd (runSystem sys s) o)
    (\s -> fst (runSystem sys s))

-- | Run a system for as many steps as there are inputs, emitting one output
-- per input. The output is the state /after/ consuming the input, matching
-- the 'Circuit.Process.Process' semantics of 'systemAsProcess'.
iterateSystem :: System (->) s (Mono i o) -> s -> [o] -> [i]
iterateSystem _ _ [] = []
iterateSystem sys s (o : os) =
  let s' = snd (runSystem sys s) o
      (i, _) = runSystem sys s'
   in i : iterateSystem sys s' os

-- | State after consuming a list of inputs.
after :: System (->) s (Mono i o) -> s -> [o] -> s
after _ s [] = s
after sys s (o : os) = after sys (snd (runSystem sys s) o) os

-- | The coalgebra-as-lens isomorphism.
--
-- A monomial system @System (->) s (Mono o i)@ is exactly a lens
-- @S y^S -> Mono o i@: the current state @s@ determines the output position
-- @o@, and each input direction @i@ determines the next state @s@.
--
-- This is the bridge to Spivak's presentation: @System s p ≅ Poly(S y^S, p)@.
systemAsLens :: System (->) s (Mono o i) -> Morphism (Mono s s) (Mono o i)
systemAsLens sys = lens get put
  where
    get s = fst (runSystem sys s)
    put s i = snd (runSystem sys s) i

-- | Inverse of 'systemAsLens': build a system from a lens @S y^S -> Mono o i@.
lensAsSystem :: Morphism (Mono s s) (Mono o i) -> System (->) s (Mono o i)
lensAsSystem m = fromEvalSystem $ \s ->
  case applyLens m s of
    (o, put) -> EP (EK o, EE put)

-- | Comultiplication for an /observable/ system: the output position is the
-- state. The result is a system over the two-step interface
-- @Mono s o ◁ Mono s o@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original system for two steps.
--
-- This is the concrete coalgebra witnessing that a Moore machine is a comonoid
-- in @(Poly, Y, ◁)@ once state is exposed as position.
duplicateSystem :: System (->) s (Mono s o) -> System (->) s ('Comp (Mono s o) (Mono s o))
duplicateSystem sys =
  fromEvalSystem $ \s ->
    let (s0, step) = runSystem sys s
        nextEval o =
          let (s1, step1) = runSystem sys (step o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build a system whose interface is the coproduct of two monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
branchSystem ::
  (s -> Bool) ->
  System (->) s (Mono o i) ->
  System (->) s (Mono o i) ->
  System (->) s ('Sum (Mono o i) (Mono o i))
branchSystem cond sysL sysR =
  fromEvalSystem $ \s ->
    if cond s
      then ES (Left (toEvalSystem sysL s))
      else ES (Right (toEvalSystem sysR s))

-- | Run a system with a homogeneous sum-of-monomials interface.
--
-- Both branches have the same direction type @i@, so the live branch is fully
-- determined by the output position.  The transition function is therefore
-- total: it takes an @i@ and dispatches to the branch that was selected.
runSystemSum ::
  System (->) s ('Sum (Mono o i) (Mono o i)) ->
  s ->
  (Either o o, i -> s)
runSystemSum sys s = case toEvalSystem sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface system.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build a system whose interface is the coproduct of two /different/
-- monomial interfaces.  The carrier state selects the active branch at each
-- step.
--
-- This is the real level-2 test: the two branches have different direction
-- types, so the runner must use the output position to decide which input
-- constructor is valid.  The GADT in 'runSystemSumHet' makes that dependency
-- total.
branchSystemHet ::
  (s -> Bool) ->
  System (->) s (Mono o1 i1) ->
  System (->) s (Mono o2 i2) ->
  System (->) s ('Sum (Mono o1 i1) (Mono o2 i2))
branchSystemHet cond sysL sysR =
  fromEvalSystem $ \s ->
    if cond s
      then ES (Left (toEvalSystem sysL s))
      else ES (Right (toEvalSystem sysR s))

-- | Run a heterogeneous sum-interface system.
--
-- Returns a 'SumStep' that exposes the selected branch and its transition
-- function.  Because the branch is statically known in the GADT, there is no
-- wrong-branch input to raise an error on.
runSystemSumHet ::
  System (->) s ('Sum (Mono o1 i1) (Mono o2 i2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runSystemSumHet sys s = case toEvalSystem sys s of
  ES (Left (EP (EK o, EE f))) -> SumStepL o f
  ES (Right (EP (EK o, EE f))) -> SumStepR o f

-- | A step observation in @q@, parameterized by state. 'Eval' is already the
-- GADT that pairs each position with its branch-appropriate direction consumer,
-- so it avoids the flat 'Dir q' family that makes sums impossible.
type Step s q = Eval q s

-- | Spivak's @[p,q]@-coalgebra. State @s@ is runtime, not a type index.
--
-- * 'act' gives the wiring pattern as a polynomial morphism.
-- * 'upd' takes a state and an input observation in @p@ and returns an output
--   observation in @q@, i.e. a 'Step' pairing the presented position with its
--   own direction consumer.
data Coalgebra s p q = Coalgebra
  { act :: s -> Morphism p q,
    upd :: s -> Eval p s -> Step s q
  }

-- | Run a @Coalgebra s 'Y q@ as a 'System' over @q@.
coalgebraToSystem :: (SystemEval q) => Coalgebra s 'Y q -> System (->) s q
coalgebraToSystem coal = fromEvalSystem $ \s -> upd coal s (EY s)

-- | Convert a monomial 'System' into a @Coalgebra s 'Y (Mono o i)@.
--
-- The @Y -> Mono o i@ morphism is built from the constant output position and
-- the trivial backward map on the unit direction space of @Y@.
systemToCoalgebraMono :: System (->) s (Mono o i) -> Coalgebra s 'Y (Mono o i)
systemToCoalgebraMono sys =
  Coalgebra
    { act = \s -> let (o, _) = runSystem sys s in Point (EP (EK o, EE (\_ -> ()))),
      upd = \s _ -> toEvalSystem sys s
    }

-- | Sequential composition of two closed coalgebras via the composition product.
--
-- The first coalgebra's interface becomes the outer factor, the second's the
-- inner factor. The composite state is the product of the two carriers.
--
-- This is the operation whose associativity is O4.
composeCoalgebra ::
  (Netlist p, Netlist q) =>
  Coalgebra s 'Y p ->
  Coalgebra t 'Y q ->
  Coalgebra (s, t) 'Y (Comp p q)
composeCoalgebra coalP coalQ =
  Coalgebra
    { act = \(s, t) ->
        let pPoint = runMorphism (act coalP s) (EY ())
            qPoint = runMorphism (act coalQ t) (EY ())
         in Point (nestedToComp (fmap (const qPoint) pPoint)),
      upd = \(s, t) _ ->
        let pVal = upd coalP s (EY s)
            qVal = upd coalQ t (EY t)
         in nestedToComp (fmap (\s' -> fmap (s',) qVal) pVal)
    }
