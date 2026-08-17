---
name: agent-sketch
description: agent as Moore coalgebra — the tape agent and its compressed-state pretense (journal/agent.md entry 001)
tags: [agent, system, process, sketch]
---

# agent-sketch ⟜ entry 001 in code

> an agent is the second pretending to be the first: it presents a
> compressed-state interface, but under the hood it's re-folding the tape.

Paste into `cabal repl` from the `circuits-diagrams` root.

```haskell
import Circuit.Poly
import Circuit.ChannelPoly
```

## the second ⟜ the tape agent

State is the raw history; every turn re-folds the whole tape to make the
output. Born with empty tape, grows by prepending percepts.

```haskell
tape :: ([i] -> o) -> System [i] (Mono o i)
tape f hist = EP (EK (f hist), EE (: hist))

-- turn count, sums: re-folded from scratch each turn
iterateSystem (tape length) [] [1,2,3 :: Int]
-- [1,2,3]

iterateSystem (tape sum) [] [1,2,3 :: Int]
-- [1,3,6]
```

## the first ⟜ compressed state

Same observable behaviour, one Int of state, no tape anywhere.

```haskell
sumAgent :: System Int (Mono Int Int)
sumAgent s = EP (EK s, EE (+ s))

iterateSystem sumAgent 0 [1,2,3]
-- [1,3,6]
```

## the pretense

`iterateSystem` cannot tell the two apart: `Mono o i` only ever exposes
output-off-state, and both agents expose the same outputs on the same
inputs. The carrier — tape or summary — is invisible at the interface.

Open ⟜ which birth does an agent get? `System` is born *with* a state
(`s0` from outside); `Process` is born *from* the first percept
(`systemAsProcess` bridges the two). Unsettled — see journal/agent.md.

## entry 002 ⟜ memory is demand

Laziness makes the tape a universal carrier: throw the whole `[i]` at any
agent and it pays only for what it looks at. An agent's memory *is* its
demand pattern on the tape.

```haskell
-- zero demand ⟜ state = (), percepts never forced
iterateSystem (tape (const ())) [] [undefined, undefined]
-- [(),()]

-- spine demand ⟜ counts percepts, never looks at one
iterateSystem (tape length) [] [undefined, undefined]
-- [1,2]

-- head demand ⟜ pure function of the current percept; later percepts unforced
take 1 (iterateSystem (tape head) [] [7, undefined, undefined])
-- [7]

-- total demand ⟜ the LLM case; re-folds everything, every turn
iterateSystem (tape sum) [] [1,2,3 :: Int]
-- [1,3,6]
```

note ⟜ laziness governs *forcing*, not *forgetting* — the consed tape is
retained by the state whether or not it is demanded. Forgetting is a
separate move: the agent must drop the tail itself.

## entry 003 ⟜ forgetting is done to you

The runner owns the tape and may rewrite it between turns — compaction is
`s -> s` applied from outside. This is why agents are `System`s (state
reachable) and not `Process`es (state existential).

```haskell
run1 :: System s (Mono o i) -> s -> i -> (o, s)
run1 sys s i = let s' = snd (runSystem sys s) i in (fst (runSystem sys s'), s')

a = tape sum :: System [Int] (Mono Int Int)
(o1,s1) = run1 a [] 1
(o2,s2) = run1 a s1 2          -- o2 = 3, tape [2,1]
(o3,s3) = run1 a [sum s2] 3    -- wholesale forget: tape := [3]
o3                             -- 6 — same as unforgotten; sum cannot tell

b = tape length :: System [Int] (Mono Int Int)
(p1,t1) = run1 b [] 1
(p2,t2) = run1 b t1 2
(p3,t3) = run1 b [sum t2] 3    -- same compaction
p3                             -- 2, not 3 — length can tell
```

Whether an agent notices wholesale forgetting is a property of its fold.

## entries 006–007 ⟜ the addressed tape, outputs fed back

The force puts the agent's `o` back on the tape (006), and entries are
addressed — writer and audience (007). `selfrec` records the agent's own
output on the tape; `view` is the per-agent session assembly.

```haskell
import Data.Maybe (mapMaybe)

data Entry = Say String String | Think String String deriving Show

view :: String -> [Entry] -> [String]
view who = mapMaybe $ \case
  Say w t -> Just (w ++ ": " ++ t)
  Think w t | w == who -> Just ("self: " ++ t)
  _ -> Nothing

-- like tape, but the agent's own output is consed back on
selfrec :: ([i] -> i) -> System [i] (Mono i i)
selfrec f hist = EP (EK (f hist), EE (\i -> let h' = i : hist in f h' : h'))

j = selfrec (\h -> Think "j" ("turn " ++ show (length h)))
  :: System [Entry] (Mono Entry Entry)

(o1,s1) = run1 j [] (Say "human" "hi")
(o2,s2) = run1 j s1 (Say "human" "you there?")

s2
-- [Think "j" "turn 3",Say "human" "you there?",Think "j" "turn 1",Say "human" "hi"]

view "human" s2
-- ["human: you there?","human: hi"]         — monologue invisible

view "j" s2
-- ["self: turn 3","human: you there?","self: turn 1","human: hi"]
```

## entry 009 ⟜ prim1, prim2, and a multi-conversation tape

The forces with types: prim1 plucks addressed entries, prim2 posts
outputs, `tick` runs one delivery round for one agent.

```haskell
data Entry = Entry { writer :: String, addr :: String, conv :: String, body :: String }
  deriving Show

prim1 :: String -> [Entry] -> [Entry]
prim1 who t = reverse (filter ((== who) . addr) t)   -- oldest first

prim2 :: Entry -> [Entry] -> [Entry]
prim2 = (:)                                          -- newest first

reply name hist =
  Entry name (writer (head hist)) (conv (head hist)) ("ack: " ++ body (head hist))

tick :: String -> System [Entry] (Mono Entry Entry) -> ([Entry], [Entry]) -> ([Entry], [Entry])
tick name sys (s, t) =
  foldl (\(st, tp) i -> let (o, st') = run1 sys st i in (st', prim2 o tp))
        (s, t)
        (drop (length s) (prim1 name t))

t0 = [Entry "human" "k" "beta" "hi k", Entry "human" "j" "alpha" "hi j"]
(sj1, t1) = tick "j" (tape (reply "j")) ([], t0)
(sk1, t2) = tick "k" (tape (reply "k")) ([], t1)

t3 = prim2 (Entry "human" "j" "alpha" "again") t2
(sj2, t4) = tick "j" (tape (reply "j")) (sj1, t3)
map body (reverse sj2)
-- ["hi j","again"]        — j sees only its addressed entries, no re-delivery

(sk2, t5) = tick "k" (tape (reply "k")) (sk1, t4)
length sk2
-- 1                       — k got nothing new from j's round
```

## entry 010 ⟜ toolcall without extra structure

A tool is another agent. A tool call is an addressed entry; the result is
an addressed entry back. No ToolCalls type, no schemas — addressing plus
scheduling.

```haskell
import Data.List (isPrefixOf)

-- j: forward "calc:..." bodies to the calc agent; final back to the
-- latest non-tool writer (threading is a fold-level discipline)
llmJ hist =
  if "calc:" `isPrefixOf` body (head hist)
    then Entry "j" "calc" (conv (head hist)) (drop 5 (body (head hist)))
    else Entry "j" (writer (head (dropWhile ((== "calc") . writer) hist)))
                   (conv (head hist))
                   ("final: " ++ body (head hist))

-- calc: a mechanical fold — sum the words
calc hist =
  Entry "calc" (writer (head hist)) (conv (head hist))
        (show (sum [read w :: Int | w <- words (body (head hist))]))

t0 = [Entry "human" "j" "alpha" "calc:1 2 3"]
(sj1, t1) = tick "j" (tape llmJ) ([], t0)     -- j posts 1 2 3 to calc
(sc1, t2) = tick "calc" (tape calc) ([], t1)  -- calc posts 6 to j
(sj2, t3) = tick "j" (tape llmJ) (sj1, t2)    -- j finals 6 to human

t3
-- [ j→human "final: 6", calc→j "6", j→calc "1 2 3", human→j "calc:1 2 3" ]
```
