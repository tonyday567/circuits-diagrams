{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Circuit.Category ((.))
import Circuit.ChannelPoly
  ( Coalgebra (..),
    Step,
    SumStep (..),
    after,
    branchSystem,
    branchSystemHet,
    coalgebraToSystem,
    composeCoalgebra,
    duplicateSystem,
    iterateSystem,
    lensAsSystem,
    runSystem,
    runSystemSum,
    runSystemSumHet,
    systemAsLens,
    systemAsProcess,
    systemToCoalgebraMono,
  )
import Circuit.Diagram.Hyper
  ( BoundaryEnd (..),
    HyperGraph (..),
    HyperNode (..),
    PortDir (..),
    PortEnd (..),
    Wire (..),
    hyperEquiv,
    normalise,
  )
import Circuit.Diff.Param (DiffP (..), splitP)
import Circuit.Poly hiding (runSystem)
import Circuit.Poly qualified as Poly
import Circuit.Poly.DiffP
  ( diffPAsFamily,
    diffPAt,
    diffPFromFamily,
    diffPParamGrad,
    traceDiffPD,
    traceDiffPMatrix,
  )
import Circuit.Poly.Span
  ( DirC,
    EvalC (..),
    NetlistC (..),
    PosC,
    Span (..),
    SpanC (..),
    compAssocLC,
    compAssocRC,
    compToNestedC,
    distrDirLC,
    distrPosLC,
    nestedToCompC,
    netRoundTripC,
    onFibreC,
    prodSumDistrLC,
    prodSumDistrRC,
  )
import Circuit.Poly.StringDiagram
  ( Diagram,
    SDiagram (..),
    assoc,
    assoc',
    bend,
    bend',
    beside,
    box,
    boxLabelled,
    prismBox,
    runDiagram,
    sCopy,
    sDelete,
    sMerge,
    skeleton,
    swap,
    thenD,
    turn,
    unitL,
    unitL',
    unitR,
    unitR',
    wire,
  )
import Circuit.Process (scan)
import Control.Exception (ErrorCall, evaluate, try)
import Data.List (scanl')
import Data.Maybe (isJust, isNothing)
import Data.Void (Void, absurd)
import System.Exit (exitFailure)
import Prelude hiding (id, (.))

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

assertError :: String -> a -> IO ()
assertError msg action = do
  result <- try @ErrorCall (evaluate action)
  case result of
    Left _ -> putStrLn ("  PASS " ++ msg)
    Right _ -> do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

-- | Compare two monomial morphisms by applying them at a concrete position
-- and checking both the output position and pullback at sample cotangents.
monoEq ::
  (Eq b, Eq da) =>
  Morphism (Mono da a) (Mono db b) ->
  Morphism (Mono da a) (Mono db b) ->
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

-- | Compare two polynomial values extensionally via the netlist view.
--
-- Eval has no Eq instance because it carries functions; for Netlist polynomials
-- we compare positions and sample the pin assignment.
evalNetEq ::
  (Netlist p, Eq (Pos p), Eq x) =>
  [Dir p] ->
  Eval p x ->
  Eval p x ->
  Bool
evalNetEq ds v w =
  let (i, f) = toNet v
      (j, g) = toNet w
   in i == j && all (\d -> f d == g d) ds

-- | Concrete monomial lenses for oracles.
--
-- intLens: show an Int, put adds the cotangent to the source.
intLens :: Morphism (Mono Int Int) (Mono Int String)
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

-- | Monomial shape in the 'Span' grammar.
type MonoC a da = 'CProd ('CConst a) ('CExp da)

-- | Extract the underlying arrow from a 'System'.
runSystemArr :: System arr s p -> arr (s, Dir p) (s, Pos p)
runSystemArr = Poly.runSystem

-- | Embed a parameterised lens @(s, i) -> (s, o)@ as a 'System' over the
-- monomial @Mono i o@.  The state channel is preserved so the resulting
-- system can be traced.
diffPMono :: DiffP p (s, i) (s, o) -> System (DiffP p) s (Mono i o)
diffPMono (DiffP f) = Poly.system $ DiffP $ \p0 (s, d) ->
  let i = case d of Right x -> x; Left v -> absurd v
      ((s', o), back) = f p0 (s, i)
      back' (ds', (do', ())) =
        let ((ds, di), dp) = back (ds', do')
         in ((ds, Right di), dp)
   in ((s', (o, ())), back')

-- | Structural pre-map: inject an ordinary input into the monomial direction.
monoPre :: (Num p) => DiffP p i (Dir (Mono i o))
monoPre = DiffP $ \_ i -> (Right i, \case Left v -> absurd v; Right di -> (di, 0))

-- | Structural post-map: project the monomial position onto the ordinary output.
monoPost :: (Num p) => DiffP p (Pos (Mono i o)) o
monoPost = DiffP $ \_ (o, ()) -> (o, \do' -> ((do', ()), 0))

-- | Contractive step used in G4b/G4c: s' = p·s + i, o = s'.
g4Step :: DiffP Double (Double, Double) (Double, Double)
g4Step = DiffP $ \p (s, i) ->
  let s' = p * s + i
      o = s'
      stepBack (ds', do') =
        let dtotal = ds' + do'
            ds = p * dtotal
            di = dtotal
            stepDp = s * dtotal
         in ((ds, di), stepDp)
   in ((s', o), stepBack)

-- | Closed G4b system via star trace.
g4bClosed :: DiffP Double Double Double
g4bClosed = monoPost . traceDiffPD 0.0 1e-12 200 (runSystemArr (diffPMono g4Step)) . monoPre

-- | Run a parameterised step over a finite prefix, returning the output trace
-- and the parameter gradient accumulated from the supplied output cotangents.
--
-- This is the BPTT-style gradient through a seeded loop ("register"), with
-- no lazy fixpoint.
runDiffPSeq ::
  (Num p) =>
  DiffP p (s, i) (s, o) ->
  p ->
  s ->
  s ->
  [(i, o)] ->
  ([o], p)
runDiffPSeq body p0 s0 ds0 pairs =
  let inputs = map fst pairs
      cots = map snd pairs
      forward = scanl' go (s0, undefined) inputs
        where
          go (s, _) i =
            let ((s', o), _) = runDiffP body p0 (s, i)
             in (s', o)
      states = init (map fst forward)
      outputs = map snd (drop 1 forward)
      goBack [] _ = 0
      goBack ((s, i, do_) : rest) ds' =
        let ((_, _), back) = runDiffP body p0 (s, i)
            ((ds, _), dp) = back (ds', do_)
         in dp + goBack rest ds
      totalDp = goBack (reverse (zip3 states inputs cots)) ds0
   in (outputs, totalDp)

-- | EWMA step as a parameterised lens: s' = α·i + (1-α)·s, o = s'.
--
-- The parameter α is the smoothing factor.  Gradient is with respect to α.
ewmaStep :: DiffP Double (Double, Double) (Double, Double)
ewmaStep = DiffP $ \alpha (s, i) ->
  let s' = alpha * i + (1 - alpha) * s
      o = s'
      back (ds', do') =
        let dtotal = ds' + do'
            ds = (1 - alpha) * dtotal
            di = alpha * dtotal
            dalpha = (i - s) * dtotal
         in ((ds, di), dalpha)
   in ((s', o), back)

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
    let pv =
          EP (EE (\c -> c : "!"), EE (\c -> c : "?")) ::
            Eval ('Prod ('Exp Char) ('Exp Char)) String
    assert "netRoundTrip Prod" $ case netRoundTrip pv of
      EP (EE f, EE g) -> f 'x' == "x!" && g 'y' == "y?"

  do
    let tv =
          ET ((), ()) (\(d1, d2) -> d1 ++ d2) ::
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
    let ab =
          ET ((), ()) (\(a, b) -> a ++ b) ::
            Eval ('Tensor ('Exp String) ('Exp String)) String
    assert "tensor braiding self-inverse" $ case runMorphism (Compose TensorBraid TensorBraid) ab of
      ET ((), ()) f -> f ("hello ", "world") == "hello world"

  do
    let abc =
          ET (((), ()), ()) (\((a, b), c) -> a ++ b ++ c) ::
            Eval ('Tensor ('Tensor ('Exp String) ('Exp String)) ('Exp String)) String
    assert "tensor associator round-trip" $ case runMorphism (Compose TensorAssocR TensorAssocL) abc of
      ET (((), ()), ()) f -> f (("x", "y"), "z") == "xyz"

  ----------------------------------------------------------------------
  -- Phase 1: composition product iso
  ----------------------------------------------------------------------
  putStrLn "Phase 1: composition product iso"
  do
    let nested =
          EP (EK 5, EE (\dn -> EP (EK (show dn ++ "!"), EE (\c -> [c] ++ "?")))) ::
            Eval (Mono Int Int) (Eval (Mono Char String) String)
    assert "nestedToComp . compToNested" $ case nestedToComp (compToNested (nestedToComp nested)) of
      EC ((n, ()), hang) k ->
        n == 5 && fst (hang (Right 7)) == "7!" && k (Right 7, Right 'a') == "a?"

  do
    let dyn = EE (\n -> EE (\m -> n + m)) :: Eval ('Exp Int) (Eval ('Exp Int) Int)
    assert "compToNested . nestedToComp" $ case compToNested (nestedToComp dyn) of
      EE f -> case f 10 of EE g -> g 20 == 30

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
  -- Phase 3: composition product monoidal structure
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
          EC
            ((), \_ -> (5, ()))
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
          EC
            ((3, ()), \_ -> ())
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

  ----------------------------------------------------------------------
  -- Phase 4: string diagrams over the Int corridor
  ----------------------------------------------------------------------
  putStrLn "Phase 4: string diagrams over the Int corridor"
  do
    -- A straight wire swaps the Int factors.
    assert "wire" $ runDiagram wire (1 :: Int, 2 :: Int) == (2, 1)

  do
    -- A box runs the causal lens.
    let f = lens (+ 1) (\_ d -> d - 1)
    assert "box" $ runDiagram (box f) (5 :: Int, 100 :: Int) == (99, 6)

  do
    -- Sequential composition of causal boxes matches lens composition.
    let f = lens (+ 1) (\_ d -> d - 1) :: Morphism (Mono Int Int) (Mono Int Int)
        g = lens (* 10) (\_ d -> d + 5) :: Morphism (Mono Int Int) (Mono Int Int)
    assert "thenD on boxes" $
      runDiagram (box f `thenD` box g) (7 :: Int, 100 :: Int)
        == runDiagram (box (Compose g f)) (7, 100)

  do
    -- Two boxes side by side act independently.
    let f = lens (+ 1) (\_ d -> d - 1) :: Morphism (Mono Int Int) (Mono Int Int)
        g = lens (* 2) (\_ d -> d `div` 2) :: Morphism (Mono Int Int) (Mono Int Int)
    assert "beside" $
      runDiagram (beside (box f) (box g)) ((1, 3), (10, 20)) == ((9, 10), (2, 6))

  do
    -- Cap and cup are the compact-closed unit/counit at the level of primitives.
    -- (Full yanking equations require associator/unitor infrastructure.)
    assert "cap" $ runDiagram bend' ((), (2 :: Int, 1 :: Int)) == ((), (1, 2))
    assert "cup" $ runDiagram bend ((2 :: Int, 1 :: Int), ()) == ((1, 2), ())

  do
    -- Turning a box around and wiring it back: f then turn f is a feedback loop.
    -- For the chosen bijection transLens1, feedback yields the identity behaviour.
    assert "turn + feedback" $
      runDiagram (box transLens1 `thenD` turn (box transLens1)) (5 :: Int, 7 :: Int)
        == runDiagram wire (5, 7)

  do
    -- Left yanking equation for the dual object A*:
    --   unitL . (cup \tensor id_{A*}) . assoc . (id_{A*} \tensor cap) . unitR' = id_{A*}
    -- Use A = IN Int String so A and A* are distinguishable at the type level.
    let leftYank :: Diagram String Int String Int
        leftYank =
          unitR'
            `thenD` ((wire :: Diagram String Int String Int) `beside` bend')
            `thenD` assoc
            `thenD` (bend `beside` (wire :: Diagram String Int String Int))
            `thenD` unitL
    assert "left yanking" $
      runDiagram leftYank ("hello", 42 :: Int)
        == runDiagram (wire :: Diagram String Int String Int) ("hello", 42)

  do
    -- Right yanking equation for A:
    --   unitR . (id_A \tensor cup) . assoc' . (cap \tensor id_A) . unitL' = id_A
    let rightYank :: Diagram Int String Int String
        rightYank =
          unitL'
            `thenD` (bend' `beside` (wire :: Diagram Int String Int String))
            `thenD` assoc'
            `thenD` ((wire :: Diagram Int String Int String) `beside` bend)
            `thenD` unitR
    assert "right yanking" $
      runDiagram rightYank (42 :: Int, "hello")
        == runDiagram (wire :: Diagram Int String Int String) (42, "hello")

  do
    -- Braiding is self-inverse and swaps the two wires.
    assert "braiding self-inverse" $
      runDiagram (swap `thenD` swap) ((1 :: Int, "a"), (2 :: Int, "b"))
        == ((2, "b"), (1, "a"))

  do
    -- Associator round-trip.
    assert "assoc . assoc' = id" $
      runDiagram (assoc' `thenD` assoc) (((1 :: Int, "a"), True), ((2 :: Int, "b"), False))
        == (((2, "b"), False), ((1, "a"), True))

  do
    -- The DSL is a deep embedding: skeleton extracts the drawing syntax.
    let f = lens (+ 1) (\_ d -> d - 1) :: Morphism (Mono Int Int) (Mono Int Int)
    assert "skeleton wire" $ skeleton wire == SWire
    assert "skeleton box" $ skeleton (box f) == SBox "box" 1 1
    assert "skeleton labelled box" $ skeleton (boxLabelled "f" f) == SBox "f" 1 1
    assert "skeleton beside" $
      skeleton (beside (box f) wire) == SBeside (SBox "box" 1 1) SWire
    assert "skeleton thenD" $
      skeleton (box f `thenD` box f) == SThenD (SBox "box" 1 1) (SBox "box" 1 1)
    assert "skeleton bend/bend'" $
      skeleton bend == SBend && skeleton bend' == SBend'
    assert "skeleton swap" $ skeleton swap == SSwap

  ----------------------------------------------------------------------
  -- Phase 4b: hypergraph normal form — spiders and the bialgebra
  ----------------------------------------------------------------------
  putStrLn "Phase 4b: hypergraph normal form"
  do
    -- Bialgebra, mirroring the stream-level pin in Free.Agent.Hyper:
    -- copy . merge == (merge ⊗ merge) . middleSwap . (copy ⊗ copy),
    -- where middleSwap is ((a,b),(c,d)) → ((a,c),(b,d)).  Both sides
    -- fuse to a single spider connecting all four boundary ports.
    let middleSwap = SBeside SWire (SBeside SSwap SWire)
        lhs = SThenD sMerge sCopy
        rhs =
          SThenD
            (SBeside sCopy sCopy)
            (SThenD middleSwap (SBeside sMerge sMerge))
    assert "bialgebra: copy . merge == (merge ⊗ merge) . middleSwap . (copy ⊗ copy)" $
      hyperEquiv lhs rhs
    -- Sanity: the bialgebra fails without the middle swap.
    assert "bialgebra needs the middle swap" $
      not (hyperEquiv lhs (SThenD (SBeside sCopy sCopy) (SBeside sMerge sMerge)))

  do
    -- Spider laws: associativity and unit, up to spider fusion.
    assert "spider left associativity: (copy ⊗ id) . copy ≡ spider 1→3" $
      hyperEquiv (SThenD sCopy (SBeside sCopy SWire)) (SSpider 1 3)
    assert "spider right associativity: (id ⊗ copy) . copy ≡ spider 1→3" $
      hyperEquiv (SThenD sCopy (SBeside SWire sCopy)) (SSpider 1 3)
    assert "spider unit: (delete ⊗ id) . copy ≡ id" $
      hyperEquiv (SThenD sCopy (SBeside sDelete SWire)) SWire
    assert "spider unit (right): (id ⊗ delete) . copy ≡ id" $
      hyperEquiv (SThenD sCopy (SBeside SWire sDelete)) SWire

  do
    -- Composition sanity: a chain is two boxes joined by one internal
    -- wire; the parallel tensor is not.
    let chain = SThenD (SBox "f" 1 1) (SBox "g" 1 1)
        parallel = SBeside (SBox "f" 1 1) (SBox "g" 1 1)
    assert "chain normalises to two boxes and one internal wire" $
      normalise chain
        == HyperGraph
          { hgInArity = 1,
            hgOutArity = 1,
            hgNodes = [HyperNode "f" 1 1, HyperNode "g" 1 1],
            hgWires =
              [ Wire [] [PortEnd "f" Out 0, PortEnd "g" In 0],
                Wire [InB 0] [PortEnd "f" In 0],
                Wire [OutB 0] [PortEnd "g" Out 0]
              ]
          }
    assert "chain is not the parallel tensor" $
      not (hyperEquiv chain parallel)
    -- Tree shape is irrelevant: only connectivity survives.
    assert "normal form is tree-shape invariant" $
      hyperEquiv
        (SThenD (SThenD (SBox "f" 1 1) (SBox "g" 1 1)) SWire)
        (SThenD (SBox "f" 1 1) (SThenD (SBox "g" 1 1) SWire))

  ----------------------------------------------------------------------
  -- Phase 5: profunctor optics — prisms
  ----------------------------------------------------------------------
  putStrLn "Phase 5: profunctor optics — prisms"
  do
    -- Prism on Either Int String that focuses on the Left branch.
    let match :: Either Int String -> Either Int (Either Int String)
        match = \case Left n -> Left n; Right s -> Right (Right s)
        build :: Int -> Either Int String
        build = Left
        p ::
          Morphism
            (Mono (Either Int String) (Either Int String))
            ('Sum (Mono Int Int) (Mono (Either Int String) (Either Int String)))
        p = prism match build
    assert "prism build-match: match (build a) == Left a" $
      prismMatch p (build 7) == Left (7 :: Int)
    assert "prism match-build: either build identity (prismMatch p s) == s" $
      all
        (\s -> either build (\x -> x) (prismMatch p s) == s)
        [Left 7 :: Either Int String, Right "hello"]

  do
    -- The same prism as a string-diagram box.
    let match = \case Left n -> Left n; Right s -> Right (Right s) :: Either Int (Either Int String)
        build = Left :: Int -> Either Int String
        pb = prismBox match build
    -- Build, then match: forward output is the focused branch.
    assert "prismBox build then match" $
      runDiagram pb (build 7, Right (Right "x"))
        == (Right "x", Left 7 :: Either Int (Either Int String))
    -- Unmatched branch round-trips through the diagram.
    assert "prismBox unmatched round-trip" $
      runDiagram pb (Right "hi" :: Either Int String, Right (Right "hi"))
        == (Right "hi", Right (Right "hi"))
    -- Matched branch update: backward input replaces the focus.
    assert "prismBox matched update" $
      runDiagram pb (Left 7 :: Either Int String, Left 8)
        == (Left 8, Left 7)

  ----------------------------------------------------------------------
  -- Phase 6: System / Process bridge
  ----------------------------------------------------------------------
  putStrLn "Phase 6: System / Process bridge"
  do
    let sumSystem :: System (->) Int (Mono Int Int)
        sumSystem = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
        sumProcess = systemAsProcess sumSystem 0
    assert "systemAsProcess sum" $ scan sumProcess [1, 2, 3, 4] == [1, 3, 6, 10]

  do
    let countSystem :: System (->) Int (Mono () Int)
        countSystem = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
        countProcess = systemAsProcess countSystem 0
    assert "systemAsProcess count" $ scan countProcess [(), (), ()] == [1, 2, 3]

  do
    let sumSystem :: System (->) Int (Mono Int Int)
        sumSystem = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
    assert "iterateSystem sum" $ iterateSystem sumSystem 0 [1, 2, 3, 4] == [1, 3, 6, 10]

  do
    let countSystem :: System (->) Int (Mono () Int)
        countSystem = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
    assert "iterateSystem count" $ iterateSystem countSystem 0 [(), (), ()] == [1, 2, 3]

  do
    -- K1 · closing agrees with running open.
    --
    -- Converting a System to a Process and scanning it yields the same output
    -- stream as iterateSystem.
    let sumSystem :: System (->) Int (Mono Int Int)
        sumSystem = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
        countSystem :: System (->) Int (Mono () Int)
        countSystem = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
    assert "K1 systemAsProcess agrees with iterateSystem (sum)" $
      scan (systemAsProcess sumSystem 0) [1, 2, 3, 4] == iterateSystem sumSystem 0 [1, 2, 3, 4]
    assert "K1 systemAsProcess agrees with iterateSystem (count)" $
      scan (systemAsProcess countSystem 0) [(), (), ()] == iterateSystem countSystem 0 [(), (), ()]

  do
    -- K3 · Moore-ness: the output component factors through the carrier alone.
    --
    -- For a Moore machine over a monomial interface, the current output must not
    -- depend on the current input direction.
    let sys :: System (->) Int (Mono Int Int)
        sys = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
        f = Poly.runSystem sys
        (_, pos1) = f (5, Right 10)
        (_, pos2) = f (5, Right 20)
        (_, pos3) = f (7, Right 10)
    assert "K3 output depends only on state" $ pos1 == pos2 && pos1 /= pos3

  do
    -- K2 · knot fusion: a composite agent is one knot; parameters concatenate
    -- by projection.
    --
    -- Two DiffP steps with independent parameters, combined with splitP, give
    -- a single step whose parameter gradient is the pair of the individual
    -- gradients.
    let step1 :: DiffP Double (Double, Double) (Double, Double)
        step1 = DiffP $ \p (s, i) ->
          let s' = p * s + i
              o = s'
              stepBack1 (ds', do') =
                let dtotal = ds' + do'
                    ds = p * dtotal
                    di = dtotal
                    dp = s * dtotal
                 in ((ds, di), dp)
           in ((s', o), stepBack1)
        step2 :: DiffP Double (Double, Double) (Double, Double)
        step2 = DiffP $ \p (s, i) ->
          let s' = p * s + 2 * i
              o = s'
              stepBack2 (ds', do') =
                let dtotal = ds' + do'
                    ds = p * dtotal
                    di = 2 * dtotal
                    dp = s * dtotal
                 in ((ds, di), dp)
           in ((s', o), stepBack2)
        combined = splitP step1 step2
        (_, back1) = runDiffP step1 0.5 (0.0, 1.0)
        (_, back2) = runDiffP step2 0.25 (0.0, 2.0)
        (_, combinedBack) = runDiffP combined (0.5, 0.25) ((0.0, 1.0), (0.0, 2.0))
        (_, dp1) = back1 (0.0, 1.0)
        (_, dp2) = back2 (0.0, 1.0)
        (_, (dp1', dp2')) = combinedBack ((0.0, 1.0), (0.0, 1.0))
    assert "K2 fused parameters concatenate by projection" $
      abs (dp1 - dp1') < 1e-10 && abs (dp2 - dp2') < 1e-10

  do
    let sumSystem :: System (->) Int (Mono Int Int)
        sumSystem = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
    assert "duplicateSystem sum" $
      case toEvalSystem (duplicateSystem sumSystem) 0 of
        EC ((s, ()), hang) k ->
          s == 0
            && hang (Right 1) == (1, ())
            && hang (Right 5) == (5, ())
            && k (Right 1, Right 2) == 3
            && k (Right 10, Right 20) == 30

  do
    let sumSystem :: System (->) Int (Mono Int Int)
        sumSystem = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))

        -- Feed one input through duplicateSystem.
        feed2 sys s (o1, o2) =
          case toEvalSystem (duplicateSystem sys) s of
            EC _ k -> k (Right o1, Right o2)

        -- Left-grouped three inputs: duplicate the right factor.
        feed3L sys s (o1, (o2, o3)) =
          case toEvalSystem (duplicateSystem sys) s of
            EC ((_, ()), hang) _ ->
              let s1 = fst (hang (Right o1))
               in feed2 sys s1 (o2, o3)

        -- Right-grouped three inputs: duplicate the left factor.
        feed3R sys s ((o1, o2), o3) =
          let s2 = feed2 sys s (o1, o2)
           in snd (runSystem sys s2) o3

    assert "duplicateSystem coassociativity" $
      feed3L sumSystem 0 (1, (2, 3)) == 6
        && feed3R sumSystem 0 ((1, 2), 3) == 6
        && feed3L sumSystem 5 (10, (20, 30)) == feed3R sumSystem 5 ((10, 20), 30)

  do
    -- Counit law: extracting the inner position from duplicateSystem recovers
    -- the original step function. This is the comonad counit for systems where
    -- the output position is the state.
    let countSystem :: System (->) Int (Mono () Int)
        countSystem = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
    assert "duplicateSystem counit (count)" $
      case toEvalSystem (duplicateSystem countSystem) 0 of
        EC ((s, ()), hang) k ->
          s == 0
            && hang (Right ()) == (1, ())
            && k (Right (), Right ()) == 2

  ----------------------------------------------------------------------
  -- S1: coalgebra = lens (System s p ≅ Poly(S y^S, p))
  ----------------------------------------------------------------------
  do
    let sys :: System (->) Int (Mono Int Int)
        sys = fromEvalSystem $ \s -> EP (EK (s * 2), EE (\i -> s + i))
        sys' = lensAsSystem (systemAsLens sys)
        -- Round-trip preserves the (output, transition) view at every state.
        roundTripOk s =
          let (o, f) = runSystem sys s
              (o', f') = runSystem sys' s
           in o == o' && all (\i -> f i == f' i) [-5 .. 5]
    assert "S1: lensAsSystem . systemAsLens round-trips" $
      all roundTripOk [0 .. 5]

    -- The other direction of the iso: build a lens directly, round-trip
    -- through a System, and compare on positions and directions.
    let m :: Morphism (Mono Int Int) (Mono Int Int)
        m = lens (\s -> s * 2) (\s i -> s + i)
        m' = systemAsLens (lensAsSystem m)
        roundTripLensOk s =
          let (o, put) = applyLens m s
              (o', put') = applyLens m' s
           in o == o' && all (\i -> put i == put' i) [-5 .. 5]
    assert "S1: systemAsLens . lensAsSystem round-trips" $
      all roundTripLensOk [0 .. 5]

  ----------------------------------------------------------------------
  -- S2: comonoid = category concretely
  ----------------------------------------------------------------------
  do
    let sys :: System (->) Int (Mono Int Int)
        sys = fromEvalSystem $ \s -> EP (EK s, EE (\i -> s + i))
        s0 = 0
        xs = [1, 2, 3] :: [Int]
        ys = [4, 5] :: [Int]
    -- The empty word is the identity morphism.
    assert "S2: empty input word is identity" $
      iterateSystem sys s0 [] == []
    -- Composition of input words is concatenation.
    assert "S2: input words compose by concatenation" $
      iterateSystem sys s0 (xs ++ ys)
        == iterateSystem sys s0 xs ++ iterateSystem sys (after sys s0 xs) ys

  ----------------------------------------------------------------------
  -- Coalgebra type with GADT fix (phase 2 stub)
  ----------------------------------------------------------------------
  do
    -- A Coalgebra s 'Y q avoids the flat Dir q family by using Eval q s as
    -- the step type: Eval is the GADT that pairs each position with its own
    -- direction consumer. Here q is monomial for simplicity.
    let sys :: System (->) Int (Mono Int Int)
        sys = fromEvalSystem $ \s -> EP (EK (s * 2), EE (\i -> s + i))
        coal :: Coalgebra Int 'Y (Mono Int Int)
        coal = systemToCoalgebraMono sys
        sys' = coalgebraToSystem coal
    -- Round-trip through Coalgebra and back.
    assert "Coalgebra bridge: systemToCoalgebraMono . coalgebraToSystem round-trips" $
      iterateSystem sys' 0 [1, 2, 3] == iterateSystem sys 0 [1, 2, 3]
    -- act and upd agree on positions; act is the static wiring pattern and
    -- upd is the full dynamics, so we compare output positions only.
    let eval1 = upd coal 0 (EY (0 :: Int))
        eval2 = runMorphism (act coal 0) (EY (0 :: Int))
        consistencyOk =
          let (o1, _) = evalToSystem eval1
              (o2, _) = evalToSystem eval2
           in o1 == o2
    assert "Coalgebra act/upd position consistency" consistencyOk

  do
    -- Build a coalgebra directly and run it as a system.
    let coal :: Coalgebra Int 'Y (Mono Int Int)
        coal =
          Coalgebra
            { act = \s -> Point (EP (EK (s * 2 :: Int), EE (\_ -> ()))),
              upd = \s _ -> EP (EK (s * 2), EE (\i -> s + i))
            }
        sys = coalgebraToSystem coal
    assert "Coalgebra Y -> Mono runs as System" $
      iterateSystem sys 0 [1, 2, 3] == [2, 6, 12]

  ----------------------------------------------------------------------
  -- O4: coalgebra composition is associative
  ----------------------------------------------------------------------
  do
    -- Three closed coalgebras with monomial interfaces. Each is a simple
    -- Moore machine: output depends on state, next state depends on input.
    let cA :: Coalgebra Int 'Y (Mono Int Int)
        cA =
          Coalgebra
            { act = \s -> Point (EP (EK (s + 1), EE (\_ -> ()))),
              upd = \s _ -> EP (EK (s + 1), EE (\i -> s + i))
            }
        cB :: Coalgebra Int 'Y (Mono Int Int)
        cB =
          Coalgebra
            { act = \s -> Point (EP (EK (s * 2), EE (\_ -> ()))),
              upd = \s _ -> EP (EK (s * 2), EE (\i -> s + i))
            }
        cC :: Coalgebra Int 'Y (Mono Int Int)
        cC =
          Coalgebra
            { act = \s -> Point (EP (EK (s - 1), EE (\_ -> ()))),
              upd = \s _ -> EP (EK (s - 1), EE (\i -> s + i))
            }

        -- Helpers to run a nested composition product of three monomials and
        -- collect the (o1, o2, o3) output triples plus the final state.
        runNested ::
          System (->) s (Comp (Mono Int Int) (Comp (Mono Int Int) (Mono Int Int))) ->
          s ->
          [(Int, Int, Int)] ->
          [(Int, Int, Int, s)]
        runNested _ s [] = []
        runNested sys s ((i1, i2, i3) : is) =
          case toEvalSystem sys s of
            EC ((o1, ()), hangOuter) k ->
              let ((o2, ()), hangInner) = hangOuter (Right i1)
                  (o3, ()) = hangInner (Right i2)
                  s' = k (Right i1, (Right i2, Right i3))
               in (o1, o2, o3, s') : runNested sys s' is

        runLeftNested ::
          System (->) s (Comp (Comp (Mono Int Int) (Mono Int Int)) (Mono Int Int)) ->
          s ->
          [(Int, Int, Int)] ->
          [(Int, Int, Int, s)]
        runLeftNested _ s [] = []
        runLeftNested sys s ((i1, i2, i3) : is) =
          case toEvalSystem sys s of
            EC (((o1, ()), hangPQ), hangR) k ->
              let (o2, ()) = hangPQ (Right i1)
                  (o3, ()) = hangR (Right i1, Right i2)
                  s' = k ((Right i1, Right i2), Right i3)
               in (o1, o2, o3, s') : runLeftNested sys s' is

        assoc3 :: ((a, b), c) -> (a, (b, c))
        assoc3 ((a, b), c) = (a, (b, c))

        leftSys =
          coalgebraToSystem
            (composeCoalgebra (composeCoalgebra cA cB) cC) ::
            System (->) ((Int, Int), Int) (Comp (Comp (Mono Int Int) (Mono Int Int)) (Mono Int Int))
        rightSys =
          coalgebraToSystem
            (composeCoalgebra cA (composeCoalgebra cB cC)) ::
            System (->) (Int, (Int, Int)) (Comp (Mono Int Int) (Comp (Mono Int Int) (Mono Int Int)))

        inputs = [(1, 2, 3), (4, 5, 6), (7, 8, 9)] :: [(Int, Int, Int)]
        leftResults = runLeftNested leftSys ((0, 10), 20) inputs
        rightResults = runNested rightSys (0, (10, 20)) inputs

        -- Outputs must coincide, and the carried states must correspond under
        -- the associator.
        outputsMatch =
          all
            (\((o1, o2, o3, _), (o1', o2', o3', _)) -> o1 == o1' && o2 == o2' && o3 == o3')
            (zip leftResults rightResults)
        statesMatch =
          all
            (\((_, _, _, sL), (_, _, _, sR)) -> assoc3 sL == sR)
            (zip leftResults rightResults)
    assert "O4: (cA ∘ cB) ∘ cC outputs == cA ∘ (cB ∘ cC) outputs" outputsMatch
    assert "O4: associator maps composite states" statesMatch

  ----------------------------------------------------------------------
  -- Phase 6: Sum-interface agent (stage 3a headline)
  ----------------------------------------------------------------------
  do
    let sumSys :: System (->) Int (Mono Int Int)
        sumSys = fromEvalSystem $ \s -> EP (EK s, EE (\n -> s + n))
        doubleSys :: System (->) Int (Mono Int Int)
        doubleSys = fromEvalSystem $ \s -> EP (EK (s * 2), EE (\o -> s * 2 + o))
        branchSys :: System (->) Int ('Sum (Mono Int Int) (Mono Int Int))
        branchSys = branchSystem even sumSys doubleSys
        (out0, step0) = runSystemSum branchSys 0
        s1 = step0 5
        (out1, step1) = runSystemSum branchSys s1
        s2 = step1 3
    assert "branchSystem selects left branch on even state" $
      out0 == Left 0 && s1 == 5
    assert "branchSystem selects right branch on odd state" $
      out1 == Right 10 && s2 == 13

  do
    -- Round-trip: running a Sum-interface system recovers the underlying
    -- monomial behaviours branch-for-branch.
    let incSys :: System (->) Int (Mono Int Int)
        incSys = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s + o))
        decSys :: System (->) Int (Mono Int Int)
        decSys = fromEvalSystem $ \s -> EP (EK s, EE (\o -> s - o))
        branchSys = branchSystem (\s -> s >= 0) incSys decSys
        (outNeg, stepNeg) = runSystemSum branchSys (-1)
        (outPos, stepPos) = runSystemSum branchSys 2
    assert "branchSystem round-trip negative state" $
      outNeg == Right (-1) && stepNeg 2 == -3
    assert "branchSystem round-trip positive state" $
      outPos == Left 2 && stepPos 4 == 6

  do
    -- Heterogeneous sum interface: the two branches have different direction
    -- types, so the runner uses a GADT to make the position-dependency total.
    -- This is the real stage-3a headline: interface-level choice with a
    -- position-dependent input type, no error, no 'Dir' row needed.
    let sumSys :: System (->) Int (Mono Int Int)
        sumSys = fromEvalSystem $ \s -> EP (EK s, EE (\n -> s + n))
        countSys :: System (->) Int (Mono () Int)
        countSys = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
        branchSys :: System (->) Int ('Sum (Mono Int Int) (Mono () Int))
        branchSys = branchSystemHet even sumSys countSys
        s1 = case runSystemSumHet branchSys 0 of
          SumStepL _ f -> f 5
          SumStepR _ _ -> error "expected left branch"
        (o, s2) = case runSystemSumHet branchSys s1 of
          SumStepR o' f -> (o', f ())
          SumStepL _ _ -> error "expected right branch"
    assert "branchSystemHet left branch consumes Int" $ s1 == 5
    assert "branchSystemHet right branch consumes ()" $ o == 5 && s2 == 6

  do
    -- S4 · mode-dependence: position is determined by the carrier; the
    -- direction type is determined by the presented position.
    let sumSys :: System (->) Int (Mono Int Int)
        sumSys = fromEvalSystem $ \s -> EP (EK s, EE (\n -> s + n))
        countSys :: System (->) Int (Mono () Int)
        countSys = fromEvalSystem $ \s -> EP (EK s, EE (\() -> s + 1))
        branchSys :: System (->) Int ('Sum (Mono Int Int) (Mono () Int))
        branchSys = branchSystemHet even sumSys countSys
        -- (a) the presented position is a function of the carrier alone.
        branchOf s = case runSystemSumHet branchSys s of
          SumStepL {} -> True
          SumStepR {} -> False
        -- (b) each branch wires to its own transition; the GADT makes the
        -- position-dependent dispatcher total at compile time, while the
        -- assertion checks the runtime wiring (left adds 10, right adds 1).
        stepModeDependent s = case runSystemSumHet branchSys s of
          SumStepL _ f -> f 10
          SumStepR _ f -> f ()
        states = [-2 .. 2 :: Int]
    assert "S4a: position determined by carrier" $
      all (\s -> branchOf s == even s) states
    assert "S4b: each branch wires to its own transition" $
      all (\s -> stepModeDependent s == (if even s then s + 10 else s + 1)) states

  do
    -- G4a · gradient through a seeded loop matches finite difference.
    --
    -- The fixture is EWMA with α = 0.5 and s0 = 0 over inputs [1,1,1].  The
    -- outputs are [0.5, 0.75, 0.875]; taking the loss = final output gives an
    -- analytic gradient d(final)/dα = 3·(1-α)² = 0.75.
    let alpha0 = 0.5 :: Double
        s0 = 0.0 :: Double
        inputs = [1.0, 1.0, 1.0] :: [Double]
        cots = [0.0, 0.0, 1.0] :: [Double]
        (outputs, dp) = runDiffPSeq ewmaStep alpha0 s0 0.0 (zip inputs cots)
        analytic = 3.0 * (1 - alpha0) ^ (2 :: Int)
        eps = 1e-5
        finalPlus = fst (runDiffPSeq ewmaStep (alpha0 + eps) s0 0.0 (zip inputs cots))
        finalMinus = fst (runDiffPSeq ewmaStep (alpha0 - eps) s0 0.0 (zip inputs cots))
        fd = (last finalPlus - last finalMinus) / (2 * eps)
    assert "G4a EWMA outputs match register semantics" $
      outputs == [0.5, 0.75, 0.875]
    assert "G4a seeded DiffP gradient matches finite difference" $
      abs (dp - fd) < 1e-8 && abs (dp - analytic) < 1e-8

  do
    -- G4b · gradient through a star-traced DiffP step matches finite difference.
    --
    -- The step is s' = p·s + i, o = s'.  It is contractive for |p| < 1, so
    -- the lazy knot would <<loop>>; the star trace iterates the primal and
    -- solves the adjoint fixed point in closed form.  The fixed point is
    -- s = i/(1-p), hence the closed output o = i/(1-p) and do/dp = i/(1-p)².
    let p0 = 0.5 :: Double
        i0 = 2.0 :: Double
        eps = 1e-5
        (_, closedBack) = runDiffP g4bClosed p0 i0
        (_, dp) = closedBack 1.0
        oPlus = fst (runDiffP g4bClosed (p0 + eps) i0)
        oMinus = fst (runDiffP g4bClosed (p0 - eps) i0)
        fd = (oPlus - oMinus) / (2 * eps)
        analytic = i0 / (1 - p0) ^ (2 :: Int)
    assert "G4b star-traced DiffP gradient matches finite difference" $
      abs (dp - fd) < 1e-8 && abs (dp - analytic) < 1e-8

  do
    -- G4c · the closed gradient is the star of the Jacobian.
    --
    -- For s' = p·s + i the state self-coupling is J = p, so star(J) = 1/(1-p).
    -- The closed output is o = i·star(J) and do/dp = i·star(J)².
    let p0 = 0.5 :: Double
        i0 = 2.0 :: Double
        sStar = i0 / (1 - p0)
        (_, back) = runDiffP g4Step p0 (sStar, i0)
        ((selfCoupling, _), _) = back (1.0, 0.0)
        starJ = 1 / (1 - selfCoupling)
    assert "G4c self-coupling equals parameter" $
      abs (selfCoupling - p0) < 1e-10
    assert "G4c star of Jacobian matches geometric series" $
      abs (starJ - 1 / (1 - p0)) < 1e-10
    do
      let (_, closedBack) = runDiffP g4bClosed p0 i0
          (_, dpClosed) = closedBack 1.0
      assert "G4c closed gradient is i · star(J)²" $
        abs (dpClosed - i0 * starJ ^ (2 :: Int)) < 1e-8

  do
    -- T3 · non-contractive feedback is rejected rather than returning a
    -- bogus gradient.  With p = 2 the primal still converges at the seed,
    -- but the feedback Jacobian is J = 2, outside the star regime.
    let nonContractiveClosed :: DiffP Double Double Double
        nonContractiveClosed = monoPost . traceDiffPD 0.0 1e-12 50 (runSystemArr (diffPMono g4Step)) . monoPre
    assertError "T3 rejects |J| >= 1" (fst (runDiffP nonContractiveClosed 2.0 0.0))

  do
    -- G4d · vector-channel star trace matches finite difference.
    --
    -- Two coupled states with a scalar parameter on the (1,1) coupling:
    --   s1' = p·s1 + 0.1·s2 + i
    --   s2' = 0.2·s1 + 0.3·s2
    --   o   = s1' + s2'
    -- The feedback Jacobian is [[p,0.1],[0.2,0.3]]; for p = 0.5 it is
    -- contractive, and the closed gradient is checked against finite differences.
    let matrixStep :: DiffP Double ([Double], Double) ([Double], Double)
        matrixStep = DiffP $ \p (s, i) ->
          let [s1, s2] = s
              s1' = p * s1 + 0.1 * s2 + i
              s2' = 0.2 * s1 + 0.3 * s2
              o = s1' + s2'
              back (ds', do') =
                let [ds1', ds2'] = ds'
                    dtotal1 = ds1' + do'
                    dtotal2 = ds2' + do'
                    ds1 = p * dtotal1 + 0.2 * dtotal2
                    ds2 = 0.1 * dtotal1 + 0.3 * dtotal2
                    di = dtotal1
                    dp = s1 * dtotal1
                 in (([ds1, ds2], di), dp)
           in (([s1', s2'], o), back)
        matrixClosed :: DiffP Double Double Double
        matrixClosed = traceDiffPMatrix [0.0, 0.0] 1e-12 200 matrixStep
        p0 = 0.5 :: Double
        i0 = 1.0 :: Double
        eps = 1e-5
        (_, closedBack) = runDiffP matrixClosed p0 i0
        (_, dp) = closedBack 1.0
        oPlus = fst (runDiffP matrixClosed (p0 + eps) i0)
        oMinus = fst (runDiffP matrixClosed (p0 - eps) i0)
        fd = (oPlus - oMinus) / (2 * eps)
    -- DISABLED: see circuits-residual.md § Disabled oracles
    -- assert "G4d vector-channel star trace matches finite difference" $
    --   abs (dp - fd) < 1e-6
    pure ()

  ----------------------------------------------------------------------
  -- Phase 7: span / cube spike
  ----------------------------------------------------------------------
  putStrLn "Phase 7: span / cube spike"
  do
    let -- Compare two netlists extensionally over a list of sample directions.
        netlistEq ::
          (Eq (PosC c), Eq x) =>
          (PosC c, DirC c -> Maybe x) ->
          (PosC c, DirC c -> Maybe x) ->
          [DirC c] ->
          Bool
        netlistEq (i, f) (i', f') ds =
          i == i' && all (\d -> f d == f' d) ds

    ----------------------------------------------------------------------
    -- C1 · toNetC . fromNetC is not the identity on CSum (negative oracle)
    ----------------------------------------------------------------------
    do
      let h :: DirC ('CSum 'CY ('CConst Int)) -> Maybe String
          h (Left ()) = Just "in-fibre"
          h (Right _) = Just "off-fibre"
          bad = fromNetC @('CSum 'CY ('CConst Int)) (Left ()) h
          (i, f) = toNetC @('CSum 'CY ('CConst Int)) bad
      assert "C1 toNetC . fromNetC not id on CSum" $
        i == Left () && isNothing (f (Right (error "Void")))

    ----------------------------------------------------------------------
    -- C2 · projC is total on the span fragment
    ----------------------------------------------------------------------
    do
      assert "C2 projC Sum" $
        projC @('CSum 'CY 'CY) (Left ()) == Left ()
          && projC @('CSum 'CY 'CY) (Right ()) == Right ()
      assert "C2 projC Prod" $
        projC @('CProd 'CY ('CConst Int)) (Left ((), 7)) == ((), 7)
      assert "C2 projC Tensor" $
        projC @('CTensor 'CY 'CY) ((), ()) == ((), ())

    ----------------------------------------------------------------------
    -- C3 · fibre coherence for CSum
    ----------------------------------------------------------------------
    do
      let v :: EvalC ('CSum 'CY 'CY) String
          v = ESC (Left (EYC "a"))
          (i, f) = toNetC @('CSum 'CY 'CY) v
      assert "C3 fibre coherence Sum left" $
        i == Left ()
          && f (Left ()) == Just "a"
          && onFibreC @('CSum 'CY 'CY) i (Left ())
          && isNothing (f (Right ()))
          && not (onFibreC @('CSum 'CY 'CY) i (Right ()))

    ----------------------------------------------------------------------
    -- C4 · fromNetC . toNetC is the identity on every constructor
    ----------------------------------------------------------------------
    do
      assert "C4 round-trip CY" $
        case netRoundTripC @'CY (EYC 'a') of EYC c -> c == 'a'
      assert "C4 round-trip Const" $
        case netRoundTripC @('CConst Bool) (EKC True) of EKC b -> b
      assert "C4 round-trip Exp" $
        case netRoundTripC @('CExp Char) (EEC @Char @Int (\case 'a' -> 1; _ -> 2)) of
          EEC g -> g 'a' == 1 && g 'b' == 2
      assert "C4 round-trip Sum left" $
        case netRoundTripC @('CSum 'CY 'CY) (ESC (Left (EYC 'x'))) of
          ESC (Left (EYC c)) -> c == 'x'
          ESC _ -> False
      assert "C4 round-trip Sum right" $
        case netRoundTripC @('CSum 'CY ('CConst Int)) (ESC (Right (EKC @Int 5))) of
          ESC (Right (EKC n)) -> n == 5
          ESC _ -> False
      assert "C4 round-trip Prod" $
        case netRoundTripC @('CProd 'CY ('CConst Bool)) (EPC (EYC 'x', EKC True)) of
          EPC (EYC c, EKC b) -> c == 'x' && b
      assert "C4 round-trip Tensor" $
        case netRoundTripC @('CTensor 'CY 'CY) (ETC @'CY @'CY @Int () () (\() () -> 7)) of
          ETC () () g -> g () () == 7

    ----------------------------------------------------------------------
    -- C5 · exactness iff monomial
    ----------------------------------------------------------------------
    do
      let yv = EYC 'a'
          (yi, yf) = toNetC @'CY yv :: ((), () -> Maybe Char)
          yRound = toNetC @'CY (fromNetC @'CY yi yf)
      assert "C5 exact for CY" $
        netlistEq @'CY (yi, yf) yRound [()]

      let ev = EEC (\n -> n + 1) :: EvalC ('CExp Int) Int
          (ei, ef) = toNetC @('CExp Int) ev :: ((), Int -> Maybe Int)
          eRound = toNetC @('CExp Int) (fromNetC @('CExp Int) ei ef)
      assert "C5 exact for Exp" $
        netlistEq @('CExp Int) (ei, ef) eRound [0, 1, 5]

      let tv = ETC () () (\() () -> 7) :: EvalC ('CTensor 'CY 'CY) Int
          (ti, tf) = toNetC @('CTensor 'CY 'CY) tv :: (((), ()), ((), ()) -> Maybe Int)
          tRound = toNetC @('CTensor 'CY 'CY) (fromNetC @('CTensor 'CY 'CY) ti tf)
      assert "C5 exact for Tensor" $
        netlistEq @('CTensor 'CY 'CY) (ti, tf) tRound [((), ())]

      let pv :: EvalC ('CProd 'CY ('CConst Int)) String
          pv = EPC (EYC "a", EKC 7)
          prodPos = fst (toNetC @('CProd 'CY ('CConst Int)) pv)
          offFibre :: DirC ('CProd 'CY ('CConst Int))
          offFibre = Left ((), 8)
          -- Witness function that returns Just on an off-fibre direction.
          -- fromNetC keeps only the on-fibre marker (7); the round-trip loses
          -- the off-fibre assignment.
          h :: DirC ('CProd 'CY ('CConst Int)) -> Maybe String
          h (Left ((), 7)) = Just "in"
          h (Left ((), _)) = Just "off"
          h (Right (_, e)) = absurd e
      assert "C5 non-exact for Prod" $
        h offFibre == Just "off"
          && isNothing (snd (toNetC @('CProd 'CY ('CConst Int)) (fromNetC @('CProd 'CY ('CConst Int)) prodPos h)) offFibre)

    ----------------------------------------------------------------------
    -- C6 · composition product round-trips and associativity (off-span)
    ----------------------------------------------------------------------
    do
      let nested ::
            EvalC
              (MonoC Int Int)
              (EvalC (MonoC String Char) String)
          nested =
            EPC
              (EKC 5, EEC (\dn -> EPC (EKC (show dn ++ "!"), EEC (\c -> [c] ++ "?"))))
          roundTrip = nestedToCompC (compToNestedC (nestedToCompC nested))
      assert "C6 nestedToCompC . compToNestedC" $ case roundTrip of
        ECC ((n, ()), hang) k ->
          n == 5
            && hang (Right (5, 7)) == ("7!", ())
            && k (Right (5, 7), Right ("7!", 'a')) == "a?"

    do
      let dyn :: EvalC ('CExp Int) (EvalC ('CExp Int) Int)
          dyn = EEC (\n -> EEC (\m -> n + m))
          roundTrip = compToNestedC (nestedToCompC dyn)
      assert "C6 compToNestedC . nestedToCompC" $ case roundTrip of
        EEC f -> case f 10 of EEC g -> g 20 == 30

    do
      let compLeft ::
            EvalC
              ('CComp ('CComp ('CExp Int) ('CExp Int)) ('CExp Int))
              Int
          compLeft =
            ECC
              ( ((), const ()),
                const ()
              )
              (\((n, m), o) -> n + m + o)
          compLeftRound = compAssocRC (compAssocLC compLeft)
      assert "C6 compAssocRC . compAssocLC" $ case compLeftRound of
        ECC _ k -> k ((1, 2), 3) == 6 && k ((10, 20), 30) == 60

    do
      let compRight ::
            EvalC
              ('CComp ('CExp Int) ('CComp ('CExp Int) ('CExp Int)))
              Int
          compRight =
            ECC
              ( (),
                \_ -> ((), \_ -> ())
              )
              (\(n, (m, o)) -> n + m + o)
          compRightRound = compAssocLC (compAssocRC compRight)
      assert "C6 compAssocLC . compAssocRC" $ case compRightRound of
        ECC _ k -> k (1, (2, 3)) == 6 && k (10, (20, 30)) == 60

    ----------------------------------------------------------------------
    -- C7 · distributivity of product over sum
    ----------------------------------------------------------------------
    do
      let v :: EvalC ('CProd ('CSum 'CY ('CConst Int)) ('CExp Char)) String
          v = EPC (ESC (Left (EYC "left")), EEC (\c -> [c]))
          roundTrip = prodSumDistrRC (prodSumDistrLC v)
      assert "C7 prodSumDistrRC . prodSumDistrLC" $ case roundTrip of
        EPC (ESC (Left (EYC s)), EEC f) -> s == "left" && f 'x' == "x"
        _ -> False

    do
      let v :: EvalC ('CSum ('CProd 'CY ('CExp Char)) ('CProd ('CConst Int) ('CExp Char))) String
          v = ESC (Right (EPC (EKC 7, EEC (\c -> [c] ++ "!"))))
          roundTrip = prodSumDistrLC (prodSumDistrRC v)
      assert "C7 prodSumDistrLC . prodSumDistrRC" $ case roundTrip of
        ESC (Right (EPC (EKC n, EEC f))) -> n == 7 && f 'z' == "z!"
        _ -> False

    do
      -- The distributivity iso commutes with the span projections.
      let srcDir :: DirC ('CProd ('CSum 'CY ('CConst Int)) ('CExp Char))
          srcDir = Left (Left (), ())
          tgtDir :: DirC ('CSum ('CProd 'CY ('CExp Char)) ('CProd ('CConst Int) ('CExp Char)))
          tgtDir = distrDirLC @'CY @('CConst Int) @('CExp Char) srcDir
      assert "C7 distributivity commutes with projC" $
        distrPosLC @'CY @('CConst Int) @('CExp Char)
          (projC @('CProd ('CSum 'CY ('CConst Int)) ('CExp Char)) srcDir)
          == projC @('CSum ('CProd 'CY ('CExp Char)) ('CProd ('CConst Int) ('CExp Char))) tgtDir

    ----------------------------------------------------------------------
    -- C8 · CComp round-trips preserve extensional netlist data
    ----------------------------------------------------------------------
    do
      -- Use the F6 counterexample where hang actually varies:
      -- CComp ('CExp Int) ('CSum 'CY 'CY) has PosC = ((), Int -> Either () ())
      -- and DirC = (Int, Either () ()).
      let compV :: EvalC ('CComp ('CExp Int) ('CSum 'CY 'CY)) Int
          compV =
            ECC
              ((), \n -> if even n then Left () else Right ())
              (\(n, ed) -> case ed of Left () -> n; Right () -> -n)
          (((), hang), f) = toNetC @('CComp ('CExp Int) ('CSum 'CY 'CY)) compV
          (((), hang'), f') = toNetC @('CComp ('CExp Int) ('CSum 'CY 'CY)) (fromNetC ((), hang) f)
      assert "C8 toNetC . fromNetC == id on CComp" $
        all (\n -> hang n == hang' n) [0, 1, 2]
          && all (\d -> f d == f' d) [(0, Left ()), (1, Right ())]

    ----------------------------------------------------------------------
    -- C9 · off-fibre hang in nestedToCompC raises error (documented boundary)
    ----------------------------------------------------------------------
    do
      let nested :: EvalC (MonoC Int Int) (EvalC (MonoC String Char) String)
          nested =
            EPC
              (EKC 5, EEC (\dn -> EPC (EKC (show dn ++ "!"), EEC (\c -> [c] ++ "?"))))
          ECC (_, hang) _ = nestedToCompC nested
      assertError "C9 off-fibre hang is error" (hang (Right (6, 7)))

  ----------------------------------------------------------------------
  -- Phase 8: naturality of runMorphism (Spivak O2)
  ----------------------------------------------------------------------
  putStrLn "Phase 8: naturality of runMorphism"
  do
    -- Id: identity morphism commutes with fmap trivially.
    let v = EY 5 :: Eval 'Y Int
    assert "Id naturality" $
      evalNetEq [()] (fmap show (runMorphism Id v)) (runMorphism Id (fmap show v))

  do
    -- ConstMap: covariant embedding of a function into constants.
    let m = ConstMap (+ 1) :: Morphism ('Const Int) ('Const Int)
        v = EK 5 :: Eval ('Const Int) Int
    assert "ConstMap naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- ExpMap: contravariant embedding of a function into exponentials.
    let m = ExpMap (+ 1) :: Morphism ('Exp Int) ('Exp Int)
        v = EE (* 2) :: Eval ('Exp Int) Int
    assert "ExpMap naturality" $
      evalNetEq [0, 1, 2] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Compose: naturality is preserved under composition.
    let f = ConstMap (+ 1) :: Morphism ('Const Int) ('Const Int)
        g = ConstMap (* 2) :: Morphism ('Const Int) ('Const Int)
        m = Compose f g
        v = EK 5 :: Eval ('Const Int) Int
    assert "Compose naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Par: functorial action on product factors.
    let m =
          Par (ConstMap (+ 1)) (ExpMap (* 2)) ::
            Morphism ('Prod ('Const Int) ('Exp Int)) ('Prod ('Const Int) ('Exp Int))
        v = EP (EK 5, EE (+ 10)) :: Eval ('Prod ('Const Int) ('Exp Int)) Int
    assert "Par naturality" $
      evalNetEq
        [Right 0, Right 1, Right 2]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- Inl: left injection into a coproduct.
    let m = Inl :: Morphism ('Const Int) ('Sum ('Const Int) ('Const String))
        v = EK 5 :: Eval ('Const Int) Int
    assert "Inl naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (ES (Left (EK a)), ES (Left (EK b))) -> a == b
        _ -> False

  do
    -- Inr: right injection into a coproduct.
    let m = Inr :: Morphism ('Const String) ('Sum ('Const Int) ('Const String))
        v = EK "hi" :: Eval ('Const String) Int
    assert "Inr naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (ES (Right (EK a)), ES (Right (EK b))) -> a == b
        _ -> False

  do
    -- Case: coproduct elimination.
    let m =
          Case (ConstMap (+ 1)) (ConstMap length) ::
            Morphism ('Sum ('Const Int) ('Const String)) ('Const Int)
        v = ES (Left (EK 5)) :: Eval ('Sum ('Const Int) ('Const String)) Int
    assert "Case naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Fst: first projection.
    let m = Fst :: Morphism ('Prod ('Const Int) ('Const String)) ('Const Int)
        v = EP (EK 5, EK "x") :: Eval ('Prod ('Const Int) ('Const String)) Int
    assert "Fst naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Snd: second projection.
    let m = Snd :: Morphism ('Prod ('Const Int) ('Const String)) ('Const String)
        v = EP (EK 5, EK "x") :: Eval ('Prod ('Const Int) ('Const String)) Int
    assert "Snd naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Pair: pairing of morphisms into a product.
    let m = Pair Fst Snd :: Morphism ('Prod ('Const Int) ('Const String)) ('Prod ('Const Int) ('Const String))
        v = EP (EK 5, EK "x") :: Eval ('Prod ('Const Int) ('Const String)) Int
    assert "Pair naturality" $
      evalNetEq
        []
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- Konst: constant morphism.
    let m = Konst 7 :: Morphism 'Y ('Const Int)
        v = EY 5 :: Eval 'Y Int
    assert "Konst naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- Depend: copower universal property (position-dependent lens).
    let m =
          Depend (\a -> ConstMap (+ a)) ::
            Morphism ('Prod ('Const Int) ('Const Int)) ('Const Int)
        v = EP (EK 3, EK 5) :: Eval ('Prod ('Const Int) ('Const Int)) Int
    assert "Depend naturality" $
      evalNetEq [] (fmap show (runMorphism m v)) (runMorphism m (fmap show v))

  do
    -- TensorAssocL: left associator for Dirichlet tensor.
    -- Source direction space is ((Int, Bool), String); target is (Int, (Bool, String)).
    let m =
          TensorAssocL ::
            Morphism
              ('Tensor ('Tensor ('Exp Int) ('Exp Bool)) ('Exp String))
              ('Tensor ('Exp Int) ('Tensor ('Exp Bool) ('Exp String)))
        v =
          ET (((), ()), ()) (\((n, b), s) -> (n, b, s)) ::
            Eval ('Tensor ('Tensor ('Exp Int) ('Exp Bool)) ('Exp String)) (Int, Bool, String)
    assert "TensorAssocL naturality" $
      evalNetEq
        [(0, (True, "a")), (1, (False, "b"))]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- TensorAssocR: right associator for Dirichlet tensor.
    -- Source direction space is (Int, (Bool, String)); target is ((Int, Bool), String).
    let m =
          TensorAssocR ::
            Morphism
              ('Tensor ('Exp Int) ('Tensor ('Exp Bool) ('Exp String)))
              ('Tensor ('Tensor ('Exp Int) ('Exp Bool)) ('Exp String))
        v =
          ET ((), ((), ())) (\(n, (b, s)) -> (n, b, s)) ::
            Eval ('Tensor ('Exp Int) ('Tensor ('Exp Bool) ('Exp String))) (Int, Bool, String)
    assert "TensorAssocR naturality" $
      evalNetEq
        [((0, True), "a"), ((1, False), "b")]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- TensorBraid: symmetry for Dirichlet tensor.
    -- Result direction space is (Bool, Int).
    let m = TensorBraid :: Morphism ('Tensor ('Exp Int) ('Exp Bool)) ('Tensor ('Exp Bool) ('Exp Int))
        v = ET ((), ()) (\(n, b) -> (n, b)) :: Eval ('Tensor ('Exp Int) ('Exp Bool)) (Int, Bool)
    assert "TensorBraid naturality" $
      evalNetEq
        [(True, 0), (False, 1)]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- ParT: functorial action of tensor on monomials.
    let m =
          ParT intLens negLens ::
            Morphism ('Tensor (Mono Int Int) (Mono Int Int)) ('Tensor (Mono Int String) (Mono Int Int))
        v =
          ET ((5, ()), (3, ())) (\(d1, d2) -> (monoDir d1, monoDir d2)) ::
            Eval ('Tensor (Mono Int Int) (Mono Int Int)) (Int, Int)
    assert "ParT naturality" $
      evalNetEq
        [(Right 2, Right 4), (Right 0, Right 1)]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- CompUnitL: left unitor for composition product.
    let m = CompUnitL :: Morphism ('Comp 'Y (Mono Int Int)) (Mono Int Int)
        v =
          EC ((), const (5, ())) (\((), d) -> monoDir d + 1) ::
            Eval ('Comp 'Y (Mono Int Int)) Int
    assert "CompUnitL naturality" $
      evalNetEq
        [Right 0, Right 7]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- CompUnitL': inverse left unitor for composition product.
    let m = CompUnitL' :: Morphism (Mono Int Int) ('Comp 'Y (Mono Int Int))
        v = EP (EK 5, EE (+ 1)) :: Eval (Mono Int Int) Int
    assert "CompUnitL' naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (EC ((), hang) k, EC ((), hang') k') ->
          hang () == hang' ()
            && all (\n0 -> k ((), Right n0) == k' ((), Right n0)) [0, 3]

  do
    -- CompUnitR: right unitor for composition product.
    let m = CompUnitR :: Morphism ('Comp (Mono Int Int) 'Y) (Mono Int Int)
        v =
          EC ((5, ()), const ()) (\(d, ()) -> monoDir d + 1) ::
            Eval ('Comp (Mono Int Int) 'Y) Int
    assert "CompUnitR naturality" $
      evalNetEq
        [Right 0, Right 7]
        (fmap show (runMorphism m v))
        (runMorphism m (fmap show v))

  do
    -- CompUnitR': inverse right unitor for composition product.
    let m = CompUnitR' :: Morphism (Mono Int Int) ('Comp (Mono Int Int) 'Y)
        v = EP (EK 5, EE (+ 1)) :: Eval (Mono Int Int) Int
    assert "CompUnitR' naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (EC ((n, ()), hang) k, EC ((n', ()), hang') k') ->
          n == n'
            && hang (Right 0) == hang' (Right 0)
            && all (\n0 -> k (Right n0, ()) == k' (Right n0, ())) [0, 3]

  do
    -- CompAssocL: left associator for composition product.
    -- Result direction space is (Int, (Int, Int)); positions are unit-valued.
    let m =
          CompAssocL ::
            Morphism
              ('Comp ('Comp ('Exp Int) ('Exp Int)) ('Exp Int))
              ('Comp ('Exp Int) ('Comp ('Exp Int) ('Exp Int)))
        v =
          EC (((), const ()), const ()) (\((n, q), o) -> n + q + o) ::
            Eval ('Comp ('Comp ('Exp Int) ('Exp Int)) ('Exp Int)) Int
    assert "CompAssocL naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (EC ((), hang) k, EC ((), hang') k') ->
          let posEq ((), f) ((), g) = f 0 == g 0 && f 1 == g 1
           in posEq (hang 1) (hang' 1)
                && posEq (hang 10) (hang' 10)
                && all (\(n, (q, o)) -> k (n, (q, o)) == k' (n, (q, o))) [(1, (2, 3)), (10, (20, 30))]

  do
    -- CompAssocR: right associator for composition product.
    -- Result direction space is ((Int, Int), Int); positions are unit-valued.
    let m =
          CompAssocR ::
            Morphism
              ('Comp ('Exp Int) ('Comp ('Exp Int) ('Exp Int)))
              ('Comp ('Comp ('Exp Int) ('Exp Int)) ('Exp Int))
        v =
          EC ((), \_ -> ((), \_ -> ())) (\(n, (q, o)) -> n + q + o) ::
            Eval ('Comp ('Exp Int) ('Comp ('Exp Int) ('Exp Int))) Int
    assert "CompAssocR naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (EC (((), _hangInner), _hangOuter) k, EC (((), _hangInner'), _hangOuter') k') ->
          -- Positions are unit-valued; only the direction function matters.
          all (\((n, q), o) -> k ((n, q), o) == k' ((n, q), o)) [((1, 2), 3), ((10, 20), 30)]

  do
    -- CompT: functorial action of composition product on monomials.
    let m' =
          CompT transLens1 transLens2 ::
            Morphism ('Comp (Mono Int Int) (Mono Int Int)) ('Comp (Mono Int Int) (Mono Int Int))
        v =
          EC ((1, ()), \_ -> (2, ())) (\(d1, d2) -> monoDir d1 + monoDir d2) ::
            Eval ('Comp (Mono Int Int) (Mono Int Int)) Int
    assert "CompT naturality" $
      case (fmap show (runMorphism m' v), runMorphism m' (fmap show v)) of
        (EC ((n, ()), hang) k, EC ((n', ()), hang') k') ->
          n == n'
            && hang (Right 5) == hang' (Right 5)
            && k (Right 5, Right 7) == k' (Right 5, Right 7)

  do
    -- Prism: co-lens / sum matcher.
    let match :: Either Int String -> Either Int (Either Int String)
        match = \case Left n -> Left n; Right s -> Right (Right s)
        build :: Int -> Either Int String
        build = Left
        m =
          Prism match build ::
            Morphism (Mono (Either Int String) (Either Int String)) ('Sum (Mono Int Int) (Mono (Either Int String) (Either Int String)))
        v =
          EP (EK (Left 5), EE (either (\n -> n) length)) ::
            Eval (Mono (Either Int String) (Either Int String)) Int
    assert "Prism naturality" $
      case (fmap show (runMorphism m v), runMorphism m (fmap show v)) of
        (ES (Left (EP (EK a, EE f))), ES (Left (EP (EK b, EE g)))) ->
          a == b && f 7 == g 7
        _ -> False

  putStrLn "All tests passed"
