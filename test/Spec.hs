{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Main (main) where

import Circuit.AD.Param (DiffP (..))
import Circuit.Poly
import Circuit.Poly.DiffP
  ( diffPAsFamily,
    diffPAt,
    diffPFromFamily,
    diffPParamGrad,
  )
import Circuit.Poly.Mealy (systemAsMealy)
import Data.Mealy (scan)
import Data.Void (absurd)
import Prelude hiding (id, (.))
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

-- | Compare two monomial morphisms by applying them at a concrete position
-- and checking both the output position and pullback at sample cotangents.
monoEq ::
  (Eq b, Eq da) =>
  Morphism (Mono a da) (Mono b db) ->
  Morphism (Mono a da) (Mono b db) ->
  a ->
  [db] ->
  Bool
monoEq f g a dbs =
  let (b1, put1) = applyLens f a
      (b2, put2) = applyLens g a
   in b1 == b2 && all (\db -> put1 db == put2 db) dbs

-- | Compare two DiffP values extensionally.
diffPEq ::
  (Eq a, Eq b, Eq p) =>
  DiffP p a b ->
  DiffP p a b ->
  p ->
  a ->
  [b] ->
  Bool
diffPEq d1 d2 p a dbs =
  let (b1, back1) = runDiffP d1 p a
      (b2, back2) = runDiffP d2 p a
   in b1 == b2 && all (\db -> back1 db == back2 db) dbs

-- | Concrete monomial lenses for oracles.
--
-- intLens: show an Int, put adds the cotangent to the source.
intLens :: Morphism (Mono Int Int) (Mono String Int)
intLens = lens show (\n d -> n + d)

-- transLens1: translate by 1. Bijection, so well-behaved.
transLens1 :: Morphism (Mono Int Int) (Mono Int Int)
transLens1 = lens (+ 1) (\_ d -> d - 1)

-- transLens2: translate by 10.
transLens2 :: Morphism (Mono Int Int) (Mono Int Int)
transLens2 = lens (+ 10) (\_ d -> d - 10)

-- negLens: negate. Bijection.
negLens :: Morphism (Mono Int Int) (Mono Int Int)
negLens = lens negate (\_ d -> negate d)

main :: IO ()
main = do
  putStrLn "Circuit.Poly oracle tests"

  ----------------------------------------------------------------------
  -- Phase 1: lens laws
  ----------------------------------------------------------------------
  putStrLn "Phase 1: lens laws"
  do
    let s = 40 :: Int
        (b, put) = applyLens transLens1 s
    assert "lens get-put: put (get s) == s" $ put b == s
    let v = 2 :: Int
        s' = put v
        (b', _) = applyLens transLens1 s'
    assert "lens put-get: get (put s v) == v" $ b' == v
    let v' = 7 :: Int
        s'' = snd (applyLens transLens1 s') v'
    assert "lens put-put: put (put s v) v' == put s v'" $
      s'' == snd (applyLens transLens1 s) v'

  ----------------------------------------------------------------------
  -- Phase 1: category laws on monomial lenses
  ----------------------------------------------------------------------
  putStrLn "Phase 1: category laws"
  do
    let a = 40 :: Int
    assert "identity left: id . f == f" $
      monoEq (Compose Id intLens) intLens a [0, 1, 5]
    assert "identity right: f . id == f" $
      monoEq (Compose intLens Id) intLens a [0, 1, 5]

  do
    let a = 40 :: Int
        f = transLens1
        g = transLens2
        h = negLens
    assert "associativity: (h . g) . f == h . (g . f)" $
      monoEq (Compose (Compose h g) f) (Compose h (Compose g f)) a [0, 1, 5]

  ----------------------------------------------------------------------
  -- Phase 1: cartesian structure
  ----------------------------------------------------------------------
  putStrLn "Phase 1: cartesian structure"
  do
    let a = 40 :: Int
    assert "fst . pair f g == f" $
      monoEq (Compose Fst (Pair intLens transLens1)) intLens a [0, 1]
    assert "snd . pair f g == g" $
      monoEq (Compose Snd (Pair intLens transLens1)) transLens1 a [0, 1]

  ----------------------------------------------------------------------
  -- Phase 1: netlist round-trips
  ----------------------------------------------------------------------
  putStrLn "Phase 1: netlist round-trips"
  do
    let yv = EY 'a' :: Eval 'Y Char
    assert "netRoundTrip Y" $ case netRoundTrip yv of EY c -> c == 'a'

  do
    let cv = EK True :: Eval ('Const Bool) Bool
    assert "netRoundTrip Const" $ case netRoundTrip cv of EK b -> b

  do
    let ev = EE (\case 'a' -> 1; 'b' -> 2; _ -> 3) :: Eval ('Exp Char) Int
    assert "netRoundTrip Exp" $ case netRoundTrip ev of
      EE f -> f 'a' == 1 && f 'b' == 2 && f 'c' == 3

  do
    let pv = EP (EE (\c -> c : "!"), EE (\c -> c : "?")) ::
             Eval ('Prod ('Exp Char) ('Exp Char)) String
    assert "netRoundTrip Prod" $ case netRoundTrip pv of
      EP (EE f, EE g) -> f 'x' == "x!" && g 'y' == "y?"

  do
    let tv = ET ((), ()) (\(d1, d2) -> d1 ++ d2) ::
             Eval ('Tensor ('Exp String) ('Exp String)) String
    assert "netRoundTrip Tensor" $ case netRoundTrip tv of
      ET ((), ()) f -> f ("hello ", "world") == "hello world"

  ----------------------------------------------------------------------
  -- Phase 1: tensor laws
  ----------------------------------------------------------------------
  putStrLn "Phase 1: tensor laws"
  do
    let mono = EP (EK 5, EE (\dn -> show dn ++ "!")) :: Eval (Mono Int Int) String
        yt = tensorUnitorL' mono
    assert "tensor left unitor round-trip" $ case tensorUnitorL yt of
      EP (EK n, EE f) -> n == 5 && f 7 == "7!"

  do
    let monoInt = EP (EK 5, EE (\dn -> dn + 1)) :: Eval (Mono Int Int) Int
        ty = tensorUnitorR' monoInt
    assert "tensor right unitor round-trip" $ case tensorUnitorR ty of
      EP (EK n, EE f) -> n == 5 && f 3 == 4

  do
    let ab = ET ((), ()) (\(a, b) -> a ++ b) ::
             Eval ('Tensor ('Exp String) ('Exp String)) String
    assert "tensor braiding self-inverse" $ case
      runMorphism (Compose TensorBraid TensorBraid) ab of
      ET ((), ()) f -> f ("hello ", "world") == "hello world"

  do
    let abc = ET (((), ()), ()) (\((a, b), c) -> a ++ b ++ c) ::
             Eval ('Tensor ('Tensor ('Exp String) ('Exp String)) ('Exp String)) String
    assert "tensor associator round-trip" $ case
      runMorphism (Compose TensorAssocR TensorAssocL) abc of
      ET (((), ()), ()) f -> f (("x", "y"), "z") == "xyz"

  ----------------------------------------------------------------------
  -- Phase 1: composition product iso
  ----------------------------------------------------------------------
  putStrLn "Phase 1: composition product iso"
  do
    let nested = EP (EK 5, EE (\dn -> EP (EK (show dn ++ "!"), EE (\c -> [c] ++ "?")))) ::
             Eval (Mono Int Int) (Eval (Mono String Char) String)
    assert "nestedToComp . compToNested" $ case
      nestedToComp (compToNested (nestedToComp nested)) of
      EC ((n, ()), hang) k ->
        n == 5 && fst (hang (Right 7)) == "7!" && k (Right 7, Right 'a') == "a?"

  do
    let dyn = EE (\n -> EE (\m -> n + m)) :: Eval ('Exp Int) (Eval ('Exp Int) Int)
    assert "compToNested . nestedToComp" $ case
      compToNested (nestedToComp dyn) of EE f -> case f 10 of EE g -> g 20 == 30

  ----------------------------------------------------------------------
  -- Phase 2: DiffP bridge as parameter-indexed lens family
  ----------------------------------------------------------------------
  putStrLn "Phase 2: DiffP bridge"
  do
    let d = DiffP (\p0 a0 -> (a0 + p0, \dy -> (dy, p0 + dy))) :: DiffP Int Int Int
    assert "diffPFromFamily . (diffPAt, diffPParamGrad) round-trip" $
      diffPEq (diffPFromFamily (diffPAt d) (diffPParamGrad d)) d 10 3 [0, 1, 5]

  do
    -- diffPAt fixes the parameter and yields an ordinary monomial lens.
    let d = DiffP (\p0 a0 -> (a0 + p0, \dy -> (dy, p0 + dy))) :: DiffP Int Int Int
        p = 10 :: Int
        a = 3 :: Int
        (b, put) = applyLens (diffPAt d p) a
    assert "diffPAt forward" $ b == a + p
    assert "diffPAt backward" $ put 5 == 5

  do
    -- diffPParamGrad extracts the parameter cotangent.
    let d = DiffP (\p0 a0 -> (a0 + p0, \dy -> (dy, p0 + dy))) :: DiffP Int Int Int
    assert "diffPParamGrad" $ diffPParamGrad d 10 3 5 == 15

  do
    -- Quadratic loss: loss(p, a) = (p - a)^2 / 2
    -- Backward: db * (a - p) to input, db * (p - a) to parameter.
    let quadLoss :: DiffP Double Double Double
        quadLoss = DiffP $ \p a ->
          let err = p - a
              loss = err * err / 2
           in (loss, \db -> (db * (-err), db * err))
        target = 0.0
        lr = 0.5
        gdStep p =
          let (_, back) = runDiffP quadLoss p target
              (_, dp) = back 1.0
           in p - lr * dp
        trajectory = take 5 (iterate gdStep 10.0)
        expected = [10.0 * (0.5 ^ n) | n <- [0 .. 4 :: Int]]
    assert "quadratic bowl gradient descent trajectory" $
      all (\(x, y) -> abs (x - y) < 1e-10) (zip trajectory expected)

  ----------------------------------------------------------------------
  -- Phase 3: Mealy integration
  ----------------------------------------------------------------------
  putStrLn "Phase 3: Mealy integration"
  do
    -- A polynomial system that sums its inputs.
    let sumSystem :: System Int (Mono Int Int)
        sumSystem s = EP (EK s, EE (\o -> s + o))
        sumMealy = systemAsMealy sumSystem 0
    assert "systemAsMealy sum" $ scan sumMealy [1, 2, 3, 4] == [1, 3, 6, 10]

  do
    -- A polynomial system that counts inputs.
    let countSystem :: System Int (Mono Int ())
        countSystem s = EP (EK s, EE (\() -> s + 1))
        countMealy = systemAsMealy countSystem 0
    assert "systemAsMealy count" $ scan countMealy [(), (), ()] == [1, 2, 3]

  ----------------------------------------------------------------------
  -- Phase 4: composition product monoidal structure
  ----------------------------------------------------------------------
  putStrLn "Phase 4: composition product monoidal structure"
  do
    -- Left unitor Y ◁ p ≅ p, tested on a monomial.
    let mono = EP (EK 5, EE (\dn -> show dn ++ "!")) :: Eval (Mono Int Int) String
    assert "compUnitorL . compUnitorL'" $
      case runMorphism CompUnitL (runMorphism CompUnitL' mono) of
        EP (EK n, EE f) -> n == 5 && f 7 == "7!" && f 42 == "42!"

  do
    -- Other direction: CompUnitL' . CompUnitL preserves the CompUnitL image.
    let compYMono :: Eval ('Comp 'Y (Mono Int Int)) String
        compYMono =
          EC ((), \_ -> (5, ()))
            (\case ((), Right n) -> show n ++ "!"; ((), Left v) -> absurd v)
        mono = runMorphism CompUnitL compYMono
        compYMono' = runMorphism CompUnitL' mono
        mono' = runMorphism CompUnitL compYMono'
    assert "compUnitorL' . compUnitorL (via CompUnitL)" $
      case (mono, mono') of
        (EP (EK n, EE f), EP (EK n', EE f')) ->
          n == n' && f 7 == f' 7 && f 42 == f' 42

  do
    -- Right unitor p ◁ Y ≅ p, tested on a monomial.
    let mono = EP (EK 7, EE (\dn -> dn * 2)) :: Eval (Mono Int Int) Int
    assert "compUnitorR . compUnitorR'" $
      case runMorphism CompUnitR (runMorphism CompUnitR' mono) of
        EP (EK n, EE f) -> n == 7 && f 3 == 6 && f 10 == 20

  do
    -- Other direction: CompUnitR' . CompUnitR preserves the CompUnitR image.
    let compMonoY :: Eval ('Comp (Mono Int Int) 'Y) Int
        compMonoY =
          EC ((3, ()), \_ -> ())
            (\case (Right n, ()) -> n * 3; (Left v, ()) -> absurd v)
        mono = runMorphism CompUnitR compMonoY
        compMonoY' = runMorphism CompUnitR' mono
        mono' = runMorphism CompUnitR compMonoY'
    assert "compUnitorR' . compUnitorR (via CompUnitR)" $
      case (mono, mono') of
        (EP (EK n, EE f), EP (EK n', EE f')) ->
          n == n' && f 3 == f' 3 && f 10 == f' 10

  do
    -- Associator round-trip on the left-associated side.
    let compLeft :: Eval ('Comp ('Comp (Mono Int Int) (Mono Int Int)) (Mono Int Int)) String
        compLeft =
          EC
            ( ((5, ()), \case Right n -> (n + 1, ()); Left v -> absurd v),
              \case (Right n, Right m) -> (n + m, ()); _ -> (0, ())
            )
            (\case ((Right n, Right m), Right o) -> show (n + m + o); _ -> "bad")
        compLeftRound = runMorphism CompAssocR (runMorphism CompAssocL compLeft)
        result = runMorphism CompAssocL compLeft
        result' = runMorphism CompAssocL compLeftRound
    assert "compAssocR . compAssocL (via CompAssocL)" $
      case (result, result') of
        (EC (i, h) k, EC (i', h') k') ->
          let posEq = i == i' && all (\n -> fst (h (Right n)) == fst (h' (Right n))) [1, 2, 3]
              hangEq = all (\(n, m) -> snd (h (Right n)) (Right m) == snd (h' (Right n)) (Right m)) [(n, m) | n <- [1, 2], m <- [3, 4]]
              dirEq = all (\(n, m, o) -> k (Right n, (Right m, Right o)) == k' (Right n, (Right m, Right o))) [(n, m, o) | n <- [1, 2], m <- [3, 4], o <- [5, 6]]
           in posEq && hangEq && dirEq

  do
    -- Associator round-trip on the right-associated side.
    let compRight :: Eval ('Comp (Mono Int Int) ('Comp (Mono Int Int) (Mono Int Int))) String
        compRight =
          EC
            ( (5, ()),
              \case
                Right n -> ((n + 1, ()), \case Right m -> (n + m, ()); Left v -> absurd v)
                Left v -> absurd v
            )
            (\case (Right n, (Right m, Right o)) -> show (n + m + o); _ -> "bad")
        compRightRound = runMorphism CompAssocL (runMorphism CompAssocR compRight)
        result = runMorphism CompAssocR compRight
        result' = runMorphism CompAssocR compRightRound
    assert "compAssocL . compAssocR (via CompAssocR)" $
      case (result, result') of
        (EC ((i, f), g) k, EC ((i', f'), g') k') ->
          let posEq = i == i' && all (\n -> f (Right n) == f' (Right n)) [1, 2, 3]
              midEq = all (\(n, m) -> g (Right n, Right m) == g' (Right n, Right m)) [(n, m) | n <- [1, 2], m <- [3, 4]]
              dirEq = all (\(n, m, o) -> k ((Right n, Right m), Right o) == k' ((Right n, Right m), Right o)) [(n, m, o) | n <- [1, 2], m <- [3, 4], o <- [5, 6]]
           in posEq && midEq && dirEq

  do
    -- Functorial action of the composition product on monomial morphisms.
    let compMono :: Eval ('Comp (Mono Int Int) (Mono Int Int)) Int
        compMono =
          EC
            (((1, ()), \case Right n -> (n * 2, ()); Left v -> absurd v))
            (\case (Right n, Right m) -> n + m; _ -> 0)
        result = runMorphism (CompT transLens1 transLens2) compMono
    assert "CompT functoriality" $
      case result of
        EC ((b, ()), hang) k ->
          let (d, ()) = hang (Right 5)
           in b == 2 && d == 5 * 2 - 2 + 10 && k (Right 5, Right 7) == 5 + 7 - 11

  putStrLn "All tests passed"
