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
    duplicateSystem,
  )
where

import Circuit.Poly (Eval (..), Mono, Netlist, Poly (..), System, nestedToComp)
import Circuit.Process (Process (..))
import Prelude hiding (id, (.))

-- | Run a monomial system at a state, exposing the output position and the
-- state-transition function.
runSystem :: System s (Mono i o) -> s -> (i, o -> s)
runSystem sys s = case sys s of EP (EK i, EE f) -> (i, f)

-- | Convert a monomial 'System' into a 'Process' machine with a given initial
-- state.
--
-- The first input is consumed for the state transition from the supplied
-- initial state, matching the coalgebra intuition of a 'System'.
systemAsProcess :: System s (Mono i o) -> s -> Process o i
systemAsProcess sys s0 =
  Process
    (\o -> snd (runSystem sys s0) o)
    (\s o -> snd (runSystem sys s) o)
    (\s -> fst (runSystem sys s))

-- | Run a system for as many steps as there are inputs, emitting one output
-- per input. The output is the state /after/ consuming the input, matching
-- the 'Circuit.Process.Process' semantics of 'systemAsProcess'.
iterateSystem :: System s (Mono i o) -> s -> [o] -> [i]
iterateSystem _ _ [] = []
iterateSystem sys s (o : os) =
  let s' = snd (runSystem sys s) o
      (i, _) = runSystem sys s'
   in i : iterateSystem sys s' os

-- | Comultiplication for an /observable/ system: the output position is the
-- state. The result is a system over the two-step interface
-- @Mono s o ◁ Mono s o@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original system for two steps.
--
-- This is the concrete coalgebra witnessing that a Moore machine is a comonoid
-- in @(Poly, Y, ◁)@ once state is exposed as position.
duplicateSystem :: System s (Mono s o) -> System s ('Comp (Mono s o) (Mono s o))
duplicateSystem sys s =
  let (s0, step) = runSystem sys s
      nextEval o =
        let (s1, step1) = runSystem sys (step o)
         in EP (EK s1, EE step1)
   in nestedToComp (EP (EK s0, EE nextEval))
