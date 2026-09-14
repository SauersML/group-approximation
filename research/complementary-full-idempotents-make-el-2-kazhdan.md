---
rg: 2
id: complementary-full-idempotents-make-el-2-kazhdan
kind: claim
title: EL_2(R) has property (T) for every finitely generated ring R with an idempotent e such that e and 1−e are both full
distinct_from:
  elementary-groups-over-fg-rings-have-property-t: that is Ershov–Jaikin-Zapirain's theorem for EL_n with n ≥ 3 over every finitely generated ring; this is rank two, under the extra hypothesis of complementary full idempotents, through an A_2-grading by Peirce blocks.
  cyclic-factor-subshift-el-2-is-simple-kazhdan-lef: that reaches rank two by the Morita reduction EL_2(M_m(S)) = EL_2m(S); this needs no matrix-ring structure, only two complementary full idempotents.
---

**ESTABLISHED (unreviewed)** by `complementary-full-idempotents-make-el-2-kazhdan-proof`.

**Statement.** Let `R` be a finitely generated associative unital ring, and `e ∈ R` an idempotent with `ReR = R` and
`R(1−e)R = R`. Then `EL_2(R)` has property (T).

**The grading.** Put `E_1 = eE_11`, `E_2 = eE_22` and `E_3 = (1−e)I_2` in `M_2(R)`. The six abelian subgroups
`Y_AB = I_2 + E_A M_2(R) E_B`, for `A ≠ B` in `{1,2,3}`, generate `EL_2(R)` and form a strong grading by the root system `A_2`.

**Model tests.**
- *Commutative R.* A full idempotent equals `1`, so the hypothesis fails. This agrees with Ershov–Jaikin-Zapirain–Kassabov's footnote that
  `EL_2(R)` lacks (T) for every infinite commutative ring.
- *R surjecting onto `Z` or `F[t]`.* In the quotient, `e` and `1−e` map to `0` and `1`, so one of them is not full and the hypothesis fails.
  `EL_2(R)` lacks (T) there, by the same footnote.
- *R = M_2(S).* `e = E_11` gives `EL_4(S)`, which has (T) by Ershov–Jaikin-Zapirain.
- *New case.* The subshift algebras `LC(X,F_q) ⋊ Z`, with `e` the indicator of a nonempty proper clopen set, satisfy the hypothesis
  (`subshift-el-2-is-simple-kazhdan-lef`).

**Review (sk-verify-4, 2026-09-13): PASS.** The A_2 Peirce grading (Lemmas 1–2), strongness by fullness, finite generation of `eRe`, relative (T) of column roots through `EL_2(S)⋉M_2(L)`, row roots through `R^op`, the `Y_12` bounded products, and the assembly re-derived, conditional on the EJZK and Kassabov imports. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §5.
