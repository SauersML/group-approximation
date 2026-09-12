---
rg: 2
id: thompson-v-coset-stabilizers-contain-copies-of-v
kind: claim
title: The separating stabilizer families of Thompson's V all contain copies of V, so Cantor-set coset peeling is circular
invalidates: [thompson-v-surjunctive-via-coset-peeling]
distinct_from:
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that shows no permanence operation built from sofic groups reaches a finitely presented simple nonsofic group; this shows the coset-transplant method itself, applied through the Cantor action of V, only ever offers stabilizer groups containing V.
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that forbids encoding the full shift into coset shifts with infinite stabilizers; this concerns transplanting an automaton over V to coset spaces of V and the groups its coset-region step would need.
  thompson-v-cantor-orbits-have-no-folner-sets: that rules out almost-invariant finite point sets of the Cantor action; this identifies the stabilizer groups of that action with copies of V.
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
---

Let `V` act on `C = {0,1}^N` and let `V_U` be the rigid stabilizer of a clopen `U`.

1. `V_U` is isomorphic to `V` for every nonempty clopen `U`.
2. Pointwise stabilizers of finite point sets separate finite subsets of `V`,
   and each contains some `V_U`.
3. Rigid stabilizers `V_D` of clopens with nonempty complement separate finite
   subsets of `V`, and `V_(D_1) intersect V_(D_2) = V_(D_1 intersect D_2)`.
4. The transplant of an automaton to `V_D\V` commutes with a free action of
   `V_(C \ D)`, a copy of `V`. It is an injection of `(B^E)^(V_(C\D))` with a
   countably infinite `E`, and such equivariant injections need not be onto over
   any group.

So the coset-region step of the peeling proofs, applied through these families,
needs surjunctivity of a group containing `V`.

**ESTABLISHED** by `thompson-v-coset-stabilizers-contain-v-proof`.
