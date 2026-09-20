---
rg: 2
id: block-permuting-local-fixers-review
kind: claim
title: Referee review of 9d1e09abaf (Lemma B, piece-permuting local fixers) — the iterated-commutator proof is correct, the three-cone consequence follows, the mixing case is correctly left open, and (COMP) stays OPEN; one scope fix (the (COMP) consequence needs the cyclic-centralizer hypothesis)
distinct_from:
  block-permuting-local-fixers-force-disjoint-supports: that is the lane claim under review; this checks its proof and consequences.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 9d1e09abaf by bh-scout-bbmz).**

## Verdicts

| item | verdict |
|---|---|
| (D) disjoint supports impossible (torsion-free, cyclic centralizers) | **PASS** |
| block preservation via `h_i^(m!)` | **PASS** |
| induction step (both branches) | **PASS** |
| end step and the case `m = 2` | **PASS** |
| three-cone consequence (`⟨x_AB, x_BC, x_AC⟩` never free) | **PASS** |
| mixing case left open; (COMP) still OPEN | **correctly marked** |
| "(COMP) holds for every `Γ ≤ V` whose local fixers permute a partition" | **needs the cyclic-centralizer hypothesis** |

## Checks

**(D).** Elements with disjoint sets of moved points commute, since each preserves its own support and fixes the
other's. So `f = z^a` and `g = z^b`, and `z^(ab)` moves nothing, by faithfulness and `supp(f^n) ⊆ supp f`. That
contradicts torsion-freeness.

**Block preservation.** `h_i` permutes `m` pieces, so `h_i^(m!)` fixes each piece setwise. It is the identity on
`W_i`, and it is nontrivial because `Γ` is torsion-free.

**Induction.** For `c = [f_j, g]` with `g = h_(j+1)^(m!)`:
- *On `W_i`, `i ≤ j`.* `g^(−1)` keeps `W_i`, where `f_j^(±1)` acts trivially, so `c = f_j g g^(−1) = f_j`, which is
  trivial there.
- *On `W_(j+1)`.* `g^(−1)` and `g` act trivially, and `f_j^(−1)` keeps `W_(j+1)`, so `c = f_j f_j^(−1)`.
- *If `c = 1`.* The common-power element `z^(ab) = f_j^b = g^a` inherits both vanishing sets and is nontrivial.
- *Piece-preservation* persists at every step.

**End.** `f_(m−1)` is supported in `W_m`, and `h_m` is supported in `C ∖ W_m`. That contradicts (D). For `m = 2` the
induction is empty and the argument is direct.

**Three-cone consequence.**
- *Setup.* `x_AB` fixes `C′` (the third cone) pointwise and maps cones onto cones. Its image of `A` avoids
  `x_AB(C′) = C′`, so it is `A` or `B`. Hence `x_AB` permutes `{A, B, C′}`, and likewise for the others.
- *Lemma B applies* with `m = 3` and `k = 6`. The generated group is therefore never torsion-free with cyclic
  centralizers, and in particular never free.

**Open items.**
- The mixing case is correctly identified as the remaining gap, in both the route and the (COMP) update: a cone
  mapped onto a clopen set that is not a union of pieces, where `[f_j, g]` loses its vanishing on `W_(j+1)`.
- `locally-fixed-torsion-free-subgroups-of-v-have-disjoint-supports` is still **OPEN**.

**Scope fix.** The claim's "Consequence for (COMP)" says (COMP) holds whenever the local fixers can be chosen to
permute a common partition.
- *When it holds unconditionally.* The branch `c ≠ 1` yields the disjoint pair directly.
- *When it needs more.* The branch `c = 1` uses cyclic centralizers.
- *The fix.* Add "and `Γ` has cyclic centralizers", as torsion-free hyperbolic groups do. That is all Q4.7 needs.

## Lesson for general BH

- **What local fixers that respect a finite partition give.** In a torsion-free group with cyclic centralizers,
  iterated commutators of their powers shrink the support one piece at a time until two supports separate.
- **Where the difficulty sits.** Q4.7's obstruction is therefore exactly the local fixers that do not respect any
  common partition. That is where the dynamics of `V` (contraction inside pieces) must be used.
