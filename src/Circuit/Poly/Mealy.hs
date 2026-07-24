{-# LANGUAGE DataKinds #-}

-- | Bridge between polynomial dynamical systems ('Circuit.Poly.System') and
-- 'Data.Mealy.Mealy' machines.
--
-- A 'System' over a monomial interface @Mono i o@ is a Moore machine: the
-- current state determines the output @i@, and the next input direction @o@
-- determines the next state. 'Data.Mealy' is the same shape, so the two views
-- round-trip exactly.
module Circuit.Poly.Mealy
  ( systemAsMealy,
    runSystem,
  )
where

import Circuit.Poly (Eval (..), Mono, System)
import Data.Mealy (Mealy (..))
import Prelude hiding (id, (.))

-- | Run a monomial system at a state, exposing the output position and the
-- state-transition function.
runSystem :: System s (Mono i o) -> s -> (i, o -> s)
runSystem sys s = case sys s of EP (EK i, EE f) -> (i, f)

-- | Convert a monomial 'System' into a 'Mealy' machine with a given initial
-- state.
--
-- The first input is consumed for the state transition from the supplied
-- initial state, matching the coalgebra intuition of a 'System'.
systemAsMealy :: System s (Mono i o) -> s -> Mealy o i
systemAsMealy sys s0 =
  Mealy
    (\o -> snd (runSystem sys s0) o)
    (\s o -> snd (runSystem sys s) o)
    (\s -> fst (runSystem sys s))
