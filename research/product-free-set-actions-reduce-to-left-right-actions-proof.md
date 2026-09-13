---
rg: 2
id: product-free-set-actions-reduce-to-left-right-actions-proof
kind: route
title: Local fibre product, Marshall Hall retraction, finite-index induction and local separation
target: product-free-set-actions-reduce-to-left-right-actions
requires:
  - sofic-actions-restrict-to-co-amenable-subgroups
  - separating-sofic-quotient-sets-make-an-action-sofic
  - gkp-sofic-action-toolkit
  - gkp-free-group-actions-are-sofic
  - gkp-amenable-group-actions-are-sofic
artifacts:
  - research/artifacts/pfg-positive-goursat-reduction-2026-09-13.md
---

Full proof: Sections 1--2 of the artifact.

**Class properties.**

- *Markings.* Lift markings through a free group; models compose.
- *Amenable groups.* GKP 2.17 and 2.15(1).
- *Subgroups.* Extend the markings of `P <= Q` by free factors, restrict to
  the original actors, and take the orbit of `1` (GKP 2.15(2),(3)).
- *Products.* (S2), pulled back along `(F_1*F_2)^2 -> (F_1xF_1) x (F_2xF_2)`.
- *Limits.* Kernel balls agree, so (LS) of
  [[sofic-actions-restrict-to-co-amenable-subgroups]] applies to the identity
  on words.

**Theorem.**

- *Step 0.* Increasing unions of finitely generated free factors, GKP
  2.15(4) and 2.16. The orbit stabilizers `G_k ∩ gLg^-1` have Goursat
  quotients that are subgroups of `Q_L`.
- *Step 1.* `L_R = < L ∩ B_(2r+2f) >`, `A_R = p_1(L_R)`, `B_R = p_2(L_R)`,
  `L^+ = L ∩ (A_R x B_R)`. Then `p_1(L^+) = A_R` and `p_2(L^+) = B_R`. So
  `(A_R x B_R)/L^+` is `LR(rho_1|, rho_2|)` over the finitely generated subgroup
  `P = rho_1(A_R)`, which is sofic by hypothesis.
- *Step 2.* Marshall Hall gives finite-index `F_1 = A_R * C` and
  `F'_1 = B_R * D`, with retractions `r`, `r'`. Put `K = (r x r')^-1(L^+)`, so
  `K ∩ (A_R x B_R) = L^+`. `G_1/K` is the pullback of Step 1 along
  `r x r'`, hence sofic. `G/K` is sofic by (FI).
- *Step 3.* `Y = G/K x G/(A_R x B_R)`. The second factor is sofic by GKP 2.19
  on each free factor and (S2). The diagonal action is sofic by (S2) and 2.15(3).
- *Step 4.* `iota(g_x L) = (g_x K, g_x(A_R x B_R))`. It is well defined and
  partially equivariant because short elements of `L` lie in
  `L_R <= K ∩ (A_R x B_R)`. It is injective because
  `K ∩ (A_R x B_R) = L^+ <= L`. (LS) finishes.

**Corollary.**

- (MLF1) is a set action of `F_m x F_m`.
- A finitely generated group is the marked limit of finitely presented groups.
- Locality gives all countable groups.
- GKP 2.16 plus the Theorem gives every set action. `∎`
