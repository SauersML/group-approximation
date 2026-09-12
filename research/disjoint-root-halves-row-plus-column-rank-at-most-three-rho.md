---
rg: 2
id: disjoint-root-halves-row-plus-column-rank-at-most-three-rho
kind: claim
title: Two disjoint transvection halves in a Leavitt rank model have row rank plus column rank at most three times the displacement, so independent halves displace zero or one half
distinct_from:
  near-minimal-defect-ranges-are-rank-faithful-for-the-commutant: that bounds ranks of products of a defect with commuting elements; this bounds sums and intersections of the ranges and kernels of two commuting transvection halves, which products do not see.
  unitriangular-data-cannot-assemble-corner-leavitt-families: that realizes the free profile, displacement one half, in regular models of locally finite groups; this shows displacement one half is forced for any model whose disjoint halves are independent as left and right ideals.
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

**ESTABLISHED** (route `disjoint-root-halves-row-column-rank-proof`; artifact Section 4; independent
re-derivation requested from `w4-vf-gate`).

**Setting.** `sigma` is a characteristic-two rank model of `R^x = L_(F_2)(1,2)^x`. For disjoint cylinders
`C, C'` put `tau(C <- C') = 1 + S[C]T[C']`. All nilpotents `sigma(tau(C <- C')) - 1` with `C ∪ C'` proper have
one rank `rho`.

**Statement.**
1. **Subproducts** (Lemma 4.1). Take pairs with `2k` pairwise disjoint cylinders and proper union. Every
   nonempty subproduct of their transvections is conjugate by a prefix replacement to one transvection, so
   it has displacement `rho`.
2. **Row plus column** (Theorem 4.3). For commuting square-zero `a, b` with `rk(a) = rk(b) = rk(a+b) = rho`,
   in particular the nilpotents of two disjoint pairs,

   ```text
   rk(aM + bM) + rk(Ma + Mb)  <=  3 rho .
   ```

3. **Independent halves** (Corollary 4.4). If both ranks are at least `2rho - rho^2 - eta`, then
   `rho(1 - 2rho) <= 2 eta`.
4. **Near-minimal displacement** (Proposition 4.5). If `sigma` is fixed-point-free with
   `rho <= (1+eps) rho_*`, where `rho_*` is the infimum over nontrivial fixed-point-free models:
   * transvection nilpotents are rank-faithful for the commutants of clopen cylinder groups up to
     `eps rho/(1+eps)`;
   * for disjoint halves, `rk(aM ∩ bM) >= rho - rho^2 - eps rho` while `rk(ab) <= rho^2 + eps rho`.

**Consequences.** Halving never lowers displacement: the halves `x_12(e_0)`, `x_12(e_1)` of `x_12(1)`
displace exactly as much as their product. With displacement strictly between `0` and `1/2`, a model
cannot keep its halves independent in both rows and columns. At near-minimal displacement the ranges of
disjoint halves must overlap far beyond their product range. No distortion of a defect-range rank
(`some-commutant-element-distorts-defect-range-rank`) follows yet.
