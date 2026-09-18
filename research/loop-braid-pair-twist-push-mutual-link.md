---
rg: 2
id: loop-braid-pair-twist-push-mutual-link
kind: claim
title: "Pair-twist push in the loop braid descending link: τ_br centralizes the triple-cable subgroup, so lk(u_0) ∩ lk(τ_br u_0) contains a forbidden-ring family member of free count N−3"
distinct_from:
  loop-braid-forbidden-ring-coning-statement: that is an open connectivity statement about the q in {0,3} subcomplex Y; this is a proved local fact about one vertex and its push (a pairwise mutual link), with no connectivity content
artifacts:
  - research/artifacts/zp-loop-braid-bfmwz-push-decomposition-2026-09-17.md
  - experiments/loop-braid-bfmwz-push-2026-09-17/mutual_link.py
  - experiments/loop-braid-bfmwz-push-2026-09-17/mutual_link_output.txt
---

Notation is from `zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md`.
- `P = PLB_n = PΣAut_n` acts on `X_n = L_n(LB_*)` with strict fundamental domain `Q ≅ OM(K_n)`.
- `X_n(F) = t^{-1}(OM(K_{[n]∖F}))`, with free count `N = n − |F|`.
- `A_ij : x_i ↦ x_j x_i x_j^{-1}`.
- For distinct rings c, d, the **pair twist** `τ_cd = A_dc ∘ A_cd` conjugates `x_c` and `x_d` by
  `x_c x_d`.
- For an ordered triple `(c_1, c_2, c_3)`, `T(c_1, c_2, c_3)` is the triple-cable subgroup: the
  image of the cabling subgroup `P'_e` under the cabling map of `u = (c_1, c_2)` or `(c_2, c_3)`.

**Claim.** Let `u_0 = [(a,b)] ∈ Q` with `a, b ∉ F`, and let `r ∉ {a, b}`. Let
`(T, g) = (T(a,b,r), τ_br)` or `(T(r,a,b), τ_ra)`, and let `Q_abr` be the subcomplex of Q of
simplices whose rings avoid `a, b, r` and F. Then:
1. g commutes with every element of T;
2. `g ∉ P_u`, so `g u_0 ≠ u_0`, and `g u_0` has type `(a,b)`;
3. `L := T · Q_abr ⊆ lk(u_0) ∩ lk(g u_0)`, and `L ≅ X_{n−2}(F'' ∪ {t})` (t the fused triple),
   a family member of free count `N − 3` if r is free and `N − 2` if `r ∈ F`;
4. every vertex of `lk(u_0) ∩ lk(g u_0)` has type avoiding `a, b, r`.

In contrast, the one-ring pushes `A_ra^{±1}, A_rb^{±1}` do not conjugate T into `P_u`
(computation, artifact §6). This answers the sub-question (★) of the w8 artifact §7 in modified
form.
