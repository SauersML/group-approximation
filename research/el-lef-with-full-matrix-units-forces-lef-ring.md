---
rg: 2
id: el-lef-with-full-matrix-units-forces-lef-ring
kind: claim
title: A ring containing full 2x2 matrix units is a LEF ring as soon as one elementary group of rank at least two over it is LEF
distinct_from:
  lef-elementary-groups-force-lef-rings: that needs one LEF EL_N with N at least four over an arbitrary ring and runs the finitely presented Steinberg cover; this accepts N = 2 or 3 for rings with full 2x2 matrix units, reaching rank 2N at least four inside EL_N through a matrix-unit corner.
---

**ESTABLISHED (unreviewed; route `el-lef-with-full-matrix-units-forces-lef-ring-proof`).**

Let `R` be a unital associative ring containing elements `ε_ij`, `i, j ∈ {1,2}`, with `ε_ij ε_kl = δ_jk ε_il`,
`ε_11 != 0` and `R ε_11 R = R`. If `EL_N(R)` is LEF for one `N >= 2`, then `R` is a LEF ring in the sense of
`lef-simple-rings-are-not-finitely-presented`. No simplicity, countability or finite generation is assumed.

**Mechanism.**
- With `e = ε_11 + ε_22` and `S = ε_11 R ε_11`, the corner is `eRe ≅ M_2(S)`.
- `g |-> (1-e)I_N + g` embeds `EL_N(eRe) = EL_N(M_2(S)) = EL_(2N)(S)` in `EL_N(R)`. Since `2N >= 4`,
  `lef-elementary-groups-force-lef-rings` makes `S` a LEF ring.
- Fullness makes `R` a unital corner `f M_m(S) f`. LEF passes to matrix rings and to unital corners, so `R`
  is LEF.

**Why ranks 2 and 3 needed a new idea.** The finitely presented cover used at rank at least four is not
available: `St_3(A)` of a free ring `A` is not finitely presented, since `A` maps onto `F_p[t]`
(Krstić–McCool Cor. 2, as quoted by Ershov–Jaikin-Zapirain; see the un-verify-measure review note on
`lef-elementary-groups-force-lef-rings`). The matrix units trade the missing presentation for rank.

**Model tests.**
- A domain has no nonzero 2x2 matrix units: `ε_12^2 = 0` forces `ε_12 = 0`, and then `ε_11 = ε_12 ε_21 = 0`.
  So division rings and simple domains are not covered, and their rank-three case stays open
  (`simple-ring-el3-lef-forces-lef-ring`).
- `M_2(F_2)` with `ε_ij = E_ij`: the hypothesis holds, `EL_N` is finite, and the ring is finite. Consistent.
- `L_k(1,2)` with `ε_12 = s_1 s_2^*`, `ε_21 = s_2 s_1^*`, `ε_11 = s_1 s_1^*`, `ε_22 = s_2 s_2^*`: the ring is
  simple, so the hypothesis holds. The ring is not directly finite, hence not LEF, and the claim predicts that
  no `EL_N(L_k(1,2))`, `N >= 2`, is LEF. That agrees with the full-complementary-idempotents theorem of
  `non_mf_groups_exist.tex` (`t = s_1^*`, `s = s_1`, `R(1-st)R = R`): every homomorphism from `EL_n(R)`,
  `n >= 2`, to an MF group is trivial.
- `LC(X,F_q) ⋊ Z` over an infinite minimal subshift, with a clopen `V != ∅`, `V ∩ TV = ∅`, and
  `ε_12 = u e_V`, `ε_21 = e_V u^{-1}`, `ε_11 = e_(TV)`, `ε_22 = e_V`: the ring is simple, so the hypothesis
  holds, and both sides hold (`minimal-subshift-algebra-is-simple-lef-ring`). Consistent.

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part3.md`):** PASS (§3). Re-derived: the corner isomorphism `eRe ≅ M_2(S)`; `EL_N(M_2(S)) = EL_(2N)(S)` inside `EL_N(R)` for `N ≥ 2`; LEF of matrix rings, through partial sums of products; the fullness isomorphism `R ≅ fM_m(S)f`; and LEF of unital corners.

**Review (sk-verify-12, 2026-09-13, `research/artifacts/sk-verify-12-2026-09-13.md`):** PASS, independent (§3). Re-derived: `Φ`, `Ψ` and `eRe ≅ M_2(S)`; rank doubling, with within-block transvections as commutators through another block; the LEF import for arbitrary unital rings; the partial-sum induction for `M_m(S)`; `vu = 1` and `R ≅ fM_m(S)f`; and LEF of the corner `Φ′(f)Q′Φ′(f)`. Checked the subshift matrix units `ue_V`, `e_Vu^{-1}`.
