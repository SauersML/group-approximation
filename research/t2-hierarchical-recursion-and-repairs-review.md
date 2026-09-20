---
rg: 2
id: t2-hierarchical-recursion-and-repairs-review
kind: claim
title: Referee review of bh-ra-t2's hierarchical-recursion node (17693583ad) and of the repair commits 801ff83f59 and 17693583ad — the hierarchical node PASSes with two small repairs (item 3's design must say what happens on degenerate skeleton configurations, and item 2 inherits the unreviewed status of the linear node's 4(a)); the repairs requested by 54a06008fb and b8aa255019 are applied correctly except two wording items; the fixed-price repair to 42f4cefeb6 (40b29f5f5c) is correct
distinct_from:
  hierarchical-recursion-relaxes-t2-to-one-sided-locality: that is the lane node under review; this checks it item by item.
  word-codings-of-t2-force-finite-presentation: that is a lane node already refereed at b8aa255019; this checks only that its requested repairs were applied.
  pointer-encodings-give-non-linear-two-sided-locality: that is a lane node already refereed at 54a06008fb; this checks only that its requested repairs were applied.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of lane work by bh-ra-t2 and one repair by
bh-ra-proof).** No priority claimed. Everything was read at source on origin/main; no code was run.

## 1. `hierarchical-recursion-relaxes-t2-to-one-sided-locality` (landed in 17693583ad): PASS with two repairs

**Item 1 (compatibility with the squeeze and the tower law): correct.**
- `∏ Q_k` is profinite and not Lie, so the commutator squeeze of `0b2ca45eb` never starts.
- `|Q_k| ≤ |B|^(ℓ_k)`, since `Q_k` acts regularly on a set of level-`k` loop labels, which is a subset of
  `B^(ℓ_k)`. With geometric `ℓ_k ≍ s_k`, this gives `log I_N ≲ s_N`, so `sys(N_N) ≲ s_N`.
- For linearly repetitive `Z^2` hierarchies, `ψ(R_S · s_N) ≍ s_N^(-2)`, while level-`(N+1)` seams have density
  `≍ 1/s_(N+1) ≍ 1/(λ s_N)`, which is `≫ s_N^(-2)`.
- This is a compatibility statement (the tower law's inequality has room), not a construction, and the node
  presents it that way.

**Item 2 (recursion alone collapses): correct, conditional as stated.**
- It is item 4(a) of `two-sided-locality-holds-for-matrix-linear-automata` applied verbatim. Level-bounded
  transports give finite-valued cocycles, continuous over the odometer, so each label layer is an equicontinuous
  factor on which the lifts act by translations of a compact abelian group, hence commute.
- **Repair (a).** That 4(a) is itself a lane proof, not reviewed. Item 2 is therefore conditional on it. The
  Status line says so, but the Statement should carry "(conditional on 4(a) of the linear node, unreviewed)" too,
  since item 2 is cited as a fact in the Lesson.

**Item 3 (transports need only be computable): the logic is right; the design needs one clause.**
- *The key step checks.* Right-multiplication lifts are bounded-radius, shift-commuting rules. If every
  simulation-checked relation `w_(L′) = h(w_L)` is left multiplication by a fixed group element, then
  `h ∘ φ_γ = φ_γ ∘ h` by associativity, so `φ_γ` maps configurations satisfying all relations to such
  configurations. Its inverse `φ_(γ^(-1))` does too. So `φ_γ ∈ Aut(Y)`.
- *Soficity.* `Y` is a factor of an SFT, hence sofic by definition. The Durand–Romashchenko–Shen fixed-point
  construction (J. Comput. System Sci. 78 (2012), "Fixed-point tile sets and their applications"; recalled by the
  lane, and the attribution is correct) supplies level-`k` zones that verify computable predicates within a budget
  polynomial in the zone size.
- **Repair (b).** The claim "that set is `Y`" is exact only on configurations whose skeleton has finite levels
  everywhere. Hierarchical skeletons always have degenerate configurations: infinite-level seams, and
  quarter-plane or half-plane supertiles with no top level. There the relations of unbounded level are never
  checked by any zone, so `Y` contains label configurations on degenerate skeletons that satisfy only the relations
  actually checked in that skeleton. The conclusion `φ_γ ∈ Aut(Y)` still holds. `Y` is exactly the set of label
  configurations satisfying every relation checked in their own skeleton, every checked relation commutes with
  `φ_γ`, and `φ_γ` does not change the skeleton. But minimality and
  rigidity of `Y`, which the node already lists as unchecked, must be checked on these degenerate configurations
  too. State this in item 3's list of costs.
- *Budget.* The relation `h` is left multiplication in the finite quotient `Q_k`, so its cost is the word problem
  of `Q_k` in its loop encoding. For Osajda-type quotients this must be shown to fit the polynomial budget; the
  node's "if `h` is computable in the zone's time and space budget" correctly makes it a hypothesis.

**Item 4 (combing survives): correct.**
- The combing lemma (item 1 of `word-codings-of-t2-force-finite-presentation`) uses only that right multiplication
  by a generator rewrites a bounded neighbourhood of the word's end. Its relators `u s u′^(-1)` involve no left
  rule. The residual-chain argument of its item 2(b) also uses only the lift side.
- So one-sided word codings with bounded end rewriting still force finite presentation, as claimed.

**Item 5 (the crux): well posed.**
- Faithfulness on `⋃_n X_n` with each `X_n` finite makes `Γ` residually finite, which matches item 4's
  requirement.
- The pointer and linear codings satisfy it with exact `Γ`, and word codings of infinitely presented `Γ` fail it,
  as the node says.
- It is correctly labelled open.

## 2. Repairs requested by 54a06008fb, as applied in 801ff83f59

- **Padding → common loop-length indexing: applied correctly.** Products now run on parallel tracks of the same
  level-`n` loops, and both known encodings are indexed by `ℓ_n` itself.
- **Caveat withdrawn: applied correctly.** It is replaced by a scope note saying the transitive case is undecided,
  with the `U_3(F_q)` example withdrawn and the reason given.
- **"Not of finite type": proved, and the proof is correct.** Take loop length `ℓ_n > 8w` and pointers at loop
  distance `> 4w`. A window of diameter `w` meets only loop cells within loop distance `2w`, since the loop is a
  square boundary of side `> 2w`. So every window of the two-pointer label agrees with a window of one of the two
  single-pointer labels, and a finite-type layer would admit the two-pointer label.
- **Not applied (wording).** Item 3 still speaks of "a non-exact subgroup of `Aut(B^Z)`" and cites Salo's
  universality theorem, which is one-dimensional, while the loops live in a two-dimensional skeleton. It should say
  `Aut(B^(Z^2))`, or `Aut(B^Z)` after coding the loops, as 54a06008fb asked. Harmless for the argument.
- **Item 6(b)** is inside item 6, which the Status labels heuristic. Acceptable.

## 3. Repairs requested by b8aa255019, as applied in 17693583ad

- **"Finitely presented non-exact group" → "finitely presented, residually finite, non-exact group": applied
  correctly,** in the title, item 2(b) and the Lesson, with the Higman-embedding remark and the KMS groups excluded
  as solvable (hence exact). It is appropriately not claimed open in print pending a literature check.
- **Linear convolution added as the fourth mechanism: applied correctly,** and item 4 of the pointer node is cited
  for its exclusion. The obstruction is renamed a "fifth, non-linear mechanism".
- **Not applied (wording).** b8aa255019 asked the node to say that the strict notion of a word coding is empty for
  infinite residually finite groups (its item 2(a) shows this), so that 2(b) is the operative notion. The body does
  not say so. Harmless.
- **Minor.** The node says Osajda's groups are infinitely presented "(recalled)". bh-ra-t2 reports reading this
  in arXiv:1703.03791 itself, so it can be cited there instead.

## 4. The fixed-price repair to 42f4cefeb6 (40b29f5f5c): correct

- `hyperbolic-lattice-rigid-measures-are-hyperplane-tight` now states the fixed-price-`> 1` corollary **for
  faithful Toeplitz shifts**, with the period chain of trivial intersection, which makes it a Farber chain so that
  Abért–Nikolov applies. It notes that a non-faithful chain concerns the quotient by the common core.
- The surface-group case via the Euler characteristic alone is stated. This matches ae9e8f9da8.

## Verdict

- `hierarchical-recursion-relaxes-t2-to-one-sided-locality`: **PASS with repairs** (a) and (b) above.
- 801ff83f59 and 17693583ad: the substantive repairs are applied correctly. Two wording items remain, the
  `Aut(B^(Z^2))` wording and the "strict notion is empty" sentence.
- 40b29f5f5c: correct.
