---
rg: 2
id: permutational-boone-higman-via-v-times-aperiodic-sft-full-groups
kind: route
title: The same two symbolic premises that give Boone--Higman through V times minimal free SFT full groups also give permutational Boone--Higman
target: permutational-boone-higman-conjecture
requires:
  - decidable-groups-embed-in-fp-groups-with-minimal-free-sft
  - v-times-minimal-free-sft-alternating-full-groups-are-fp
  - v-times-ample-full-groups-are-generated-by-transpositions
  - fp-v-times-minimal-action-full-groups-have-type-a-actions
---

**Route.** The implication is complete. It fires once the OPEN premises (P1)
`decidable-groups-embed-in-fp-groups-with-minimal-free-sft` and (P2)
`v-times-minimal-free-sft-alternating-full-groups-are-fp` are proved.

**How this differs.**
- `boone-higman-via-v-times-aperiodic-sft-full-groups` concludes only
  Boone--Higman from (P1) and (P2), via simplicity of `A(T)`. Its last remark
  left the type (A) corollary unclaimed, because the hypotheses of
  `fp-full-binary-cantor-groups-have-type-a-actions` were not checked on
  `C × X`.
- This route closes that gap with a criterion needing no binary model:
  `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, applied through
  `fp-v-times-minimal-action-full-groups-have-type-a-actions`.
- The conclusion is formally stronger than Boone--Higman. It is the root that
  `permutational-boone-higman-via-mif-envelopes` reaches only through BFFHZ
  Question 3.4.

## Proof that (P1) and (P2) give permutational Boone--Higman

Let `K` be finitely generated with solvable word problem.
1. By (P1) choose an infinite finitely presented `Λ >= K`, a finite alphabet `A`,
   and a nonempty subshift of finite type `X ⊆ A^Λ` on which `Λ` acts freely and
   minimally. `X` is compact, metrizable and totally disconnected.
2. Put `T = G_V × (Λ ⋉ X)`. By
   `v-times-ample-full-groups-are-generated-by-transpositions`, `F(T) = A(T)`.
   By (P2), `F(T)` is finitely presented.
3. `Λ` embeds in `F(T)` by `λ ↦ (c, x) ↦ (c, λx)`. Injectivity uses that `X` is
   nonempty and the action is free. This is step 5 of
   `boone-higman-via-v-times-aperiodic-sft-full-groups`, repeated here in full:
   the set `{(1_c, (λ, x))}` is a compact open bisection with source and range `Y`,
   and the assignment is a homomorphism.
4. By `fp-v-times-minimal-action-full-groups-have-type-a-actions`, `F(T)` admits an
   action of type (A) on the proper nonempty clopen subsets of `C × X`.

So `K <= Λ <= F(T)`, a group admitting an action of type (A). ∎

## Where it can fail

Exactly where the Boone--Higman route fails: at (P1) or at (P2). The added step 4
uses only minimality of `X`, not freeness or finite type. So a disproof of the
permutational conjecture that leaves Boone--Higman intact would have to break
(P1) or (P2). It could not come from the passage to type (A).
