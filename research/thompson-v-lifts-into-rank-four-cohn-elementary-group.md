---
rg: 2
id: thompson-v-lifts-into-rank-four-cohn-elementary-group
kind: claim
title: Thompson's V lifts into GL_2 of the binary Cohn algebra through eventually-zero sequences, so the V gate kills every rank model of EL_4(C_2)
distinct_from:
  cohn-elementary-group-rank-radical-is-trivial-or-everything: that is the rank radical dichotomy for EL_3(C_2); this lifts V into GL_2(C_2) and EL_4(C_2), and places the rank-four Cohn group below both the Cohn EL_3 question and the V gate.
  thompson-v-has-no-nontrivial-f2-rank-model: that is the V gate itself; this shows the V gate already makes every characteristic-two rank model of EL_4(C_2) trivial.
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

**ESTABLISHED** (proof route `thompson-v-lift-into-rank-four-cohn-group-proof`; artifact Section 4;
independent re-derivation requested from `w4-vf-gate`).

Let `C_2` be the binary Cohn algebra, `q = 1 - s_0 t_0 - s_1 t_1`, and `pi : C_2 -> R = L_(F_2)(1,2)`
the quotient. Let `V <= R^x` act by prefix replacements.

1. **Lift.** There is an injective homomorphism `phi : V -> GL_2(C_2)` with
   `pi(phi(g)) = diag(g, 1)`. It is the permutation action of `V` on the eventually-zero sequences
   `{w 1 0^inf} ⊔ {0^inf}`, transported to `F_2[W] (+) F_2[W]`. It differs from the prefix
   replacement only by finitary units `s_alpha q t_beta`, `s_alpha q`, `q t_beta`, `q`.
2. **Rank four.** `V` is perfect, so by Whitehead's lemma `phi(V) (+) 1_2 <= EL_4(C_2)`.
3. **Rank-four dichotomy.** The normal subgroups of `G_4 = EL_4(C_2)` are `1`,
   `K_4 = GL_fin(W x 4, F_2)` and `G_4`. So `G_4` has a nontrivial characteristic-two rank model iff
   it has an injective one.
4. **Ordering.** Each of the following implies that every characteristic-two rank model of
   `EL_4(C_2)` is trivial, and that in turn implies that `R^x` has no nontrivial characteristic-two
   rank model:
   - `thompson-v-has-no-nontrivial-f2-rank-model`;
   - `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`.
