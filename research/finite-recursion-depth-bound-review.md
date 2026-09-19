---
rg: 2
id: finite-recursion-depth-bound-review
kind: claim
title: Referee review of e6f7e2b3d7 — both directions of "WP decidable ⟺ depth computably bounded" are correct for functionally recursive groups, and Bartholdi–Mitrofanov Theorem A″ is quoted verbatim (v4, p. 2) with a faithful action on the regular tree A*; one overstatement: a uniform depth bound would only imply, not equal, the negation of the fp self-similar hard-WP target
distinct_from:
  finite-recursion-gives-no-computable-depth-bound: that is the lane node under review; this checks its criterion, its citation and its consequences.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof e6f7e2b3d7 by bh-gate1-abstract).**
Read at source: Bartholdi–Mitrofanov, *The word and order problems for self-similar and automata groups*,
arXiv:1710.10109v4 (27 Nov 2017), §1 (pp. 1–2).

## Verdicts

| item | verdict |
|---|---|
| 1. residually `W_(|A|)` | **PASS** |
| 2. "if": computable `F ≥ D` ⇒ `WP` decidable | **PASS** |
| 2. "only if": `WP` decidable ⇒ `D` computable | **PASS** |
| 3. Theorem A″ quotation, faithfulness | **PASS**, verbatim |
| 4. consequences (no computable bound; not finitely presented) | **PASS** |
| "a uniform bound is exactly the negation of the fp target" | **overstated**: one implication only |

## Checks

- **Faithfulness and the tree.** B–M §1 set up "a group `G` acting faithfully and 'self-similarly' on the set `A*`",
  through `(a_1 … a_n)^g = a′_1 (a_2 … a_n)^(g′)` and a lift `Φ: A × S → F_S × A`. They write `G = ⟨Φ⟩`, the group
  *presented* by `Φ`, as a quotient of `F_S`.
  - Such actions preserve length and prefixes, so `G` is a faithful group of automorphisms of the `|A|`-regular
    rooted tree `A*`.
  - Item 1 follows: the level quotients embed in iterated wreath products of `S_(|A|)` and separate points.
- **Theorem A″ (p. 2), verbatim.** "There is a functionally recursive group ⟨Φ⟩ with Φ: A × S → F_S × A such that
  {s ∈ F_S | s = 1 in ⟨Φ⟩} is not recursive." The abstract is also quoted correctly. This set
  is always co-r.e., since nontriviality is witnessed by a moved vertex, so A″ says it is not r.e.
- **"If".** The level-`k` action of a word is computable from `Φ`, since section words have length `≤ L^k |w|`.
  - A move at level `j ≤ F(|w|)` gives a move at level `F(|w|)`, because the descendants of `v` and of
    `v^w ≠ v` are disjoint.
  - So `w = 1` iff `w` fixes level `F(|w|)`, which is decidable.
- **"Only if".** For each `n` there are finitely many words. Decide triviality, then search levels for each
  nontrivial word. The search terminates by faithfulness, so `D` is computable.
- **Item 4.**
  - `D` is nondecreasing, so "not bounded by any computable `F`" means `D(n) > F(n)` for infinitely many `n`.
  - A finitely presented `⟨Φ⟩` would have triviality r.e. as well as co-r.e., hence decidable. So A″'s group is
    not finitely presented.

## The one overstatement

- **What the node says.** It calls a uniform recursive depth bound over finitely presented functionally recursive
  groups "exactly the negation of `fp-self-similar-groups-with-arbitrarily-hard-word-problem`".
- **Only one direction holds.** A uniform bound `D ≤ F` gives `WP ≤ 2^(O(F))` for all such groups, which negates the
  target. The converse fails: word problems can be uniformly easy by other algorithms while depth is large.
- **The fix.** State it as "a uniform bound would refute the target".
- **Minor.** The one-type chart recursion of the prefix-chart node is functionally recursive when a single chart
  system is used. With several systems, addresses are not unique, and the node should say "up to chart
  transitions".

## Lesson for general BH

- **What remains of the Farley–Hughes hardness channel.** Depth equals decidability, and finite recursion allows
  non-computable depth. So in Farley–Hughes engines, finite presentation of the structure group is the only
  remaining cap.
- **The precise open question.** Whether finite presentation is compatible with super-recursive (but computable)
  depth.
