---
rg: 2
id: integral-jacobson-defect-has-no-normal-kazhdan-subgroup
kind: claim
title: Over the integral Toeplitz--Jacobson algebra no compression defect at any matrix size contains a nontrivial normal Kazhdan subgroup
distinct_from:
  finite-rank-kernel-forces-abelian-defect-subgroups: that is the general finite-rank kernel theorem over any field; this is its instance for the shift model of the integral Jacobson algebra, together with the explicit nontrivial defect elements that show the exclusion is sharp.
  finite-additive-order-one-sided-defects-are-mf-invisible: that produces a finite central Kazhdan witness in the defect when the complementary idempotent has finite additive order; this shows that over the integral ring, where the same witness is infinite cyclic, no normal Kazhdan witness exists in any defect at any rank.
  jacobson-unit-group-is-locally-finite-and-mf: that computes the rank-one unit group over the binary field and finds it MF; this is a characteristic-zero statement about compression defects at every rank and says nothing about MF.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that kills a root over the binary Jacobson algebra in rank five; this is the characteristic-zero obstruction showing no analogous normal Kazhdan witness exists over the integers.
  jacobson-shift-representation-is-faithful: that is the faithful monomial basis of the shift model, consumed here; this is a group-theoretic exclusion theorem built on it.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  Let `J_Z = Z<s,t | ts = 1>`, `e = 1 - st`,
`f_(ij) = s^i e t^j`.  For every `n >= 1`, every subgroup
`Delta <= GL_n(J_Z)`, every finitely generated `L <= Delta`, and every
finitely generated normal subgroup

```text
K <| Delta,      K <= D_Delta(L),                                    (IJ1)
```

the group `K` is free abelian of finite rank.  Consequently

```text
L Kazhdan,  K <| Delta Kazhdan,  K <= D_Delta(L)   ==>   K = 1,      (IJ2)
```

and the same conclusion holds for any finitely generated normal
`K <= D_Delta(L)` with finite abelianization.  The exclusion also covers
homomorphic encodings: if `P` carries Kazhdan subgroups `L_0, K_0` with
`K_0 <| P` and `K_0 <= D_P(L_0)`, then every homomorphism
`f : P -> GL_n(J_Z)` kills `K_0`, because `f(D_P(L_0)) <= D_(f(P))(f(L_0))`
and images preserve normality and property (T).

**What it excludes.**  The normal-Kazhdan criterion
`normal-kazhdan-defect-non-mf` has no nontrivial instance inside
`GL_n(J_Z)`, hence none inside `EL_n(J_Z)` or any intermediate subgroup,
at any matrix size.  Raising the rank or choosing a cleverer subgroup
cannot repair this method for the integral ring; a proof that
`EL_n(J_Z)` is not MF, if one exists, must extract its obstruction from
different information (`integral-jacobson-elementary-group-is-not-mf`).

**The defect is not trivial, so the exclusion is sharp.**  The
manuscript's four-coordinate configuration (`prop:torsion-defect-ring` of
`non_mf_groups_exist.tex`) is exact over `J_Z`: in `EL_4(J_Z)` with
`L = EL_3(J_Z)` on the first three coordinates,
`v = u D(w_14 w_25)`, `c = D(1 + f_02)`, `y = e_42(f_10)`,
`z = D(1 + f_12)`, `l = e_21(1)`, one has `v L v^-1 <= L`,
`c in C(L)`, `[y, [v c v^-1, l]] = z^-1`, and `z` central in
`B = <L, v, c, y>`.  Over `J_Z`, `z^m = D(1 + m f_12) != 1` for `m != 0`,
so `<z> = Z` is an infinite cyclic central subgroup of `B` inside
`D_B(L)`; over `J_(F_p)` the same `z` has order `p`.  Moreover, with
`G = EL_4(J_Z)`, the identities

```text
[z, e_41(f_20)] = e_41(f_10),      [e_24(t), e_41(f_10)] = e_21(e)     (IJ3)
```

and signed permutations put every `e_(ij)(e)`, `i != j`, into `D_G(L)`;
those with `i, j <= 3` generate a copy of `SL_3(Z)` acting on the three
`v_0`-coordinates.  So the integral defect contains infinite cyclic
central subgroups and non-normal Kazhdan subgroups, and `(IJ1)` says
exactly that none of its finitely generated normal subgroups is
nonabelian.

**Why characteristic matters.**  Over `J_(F_p)` the finite-rank kernel
theorem yields finite elementary abelian `p`-groups instead of free
abelian groups, which is why the order-`p` witness `z` can be normal,
central, and Kazhdan there, and why the torsion theorem
`finite-additive-order-one-sided-defects-are-mf-invisible` exists in
positive characteristic and has no integral analogue by this route.

Derivation: `integral-jacobson-defect-has-no-normal-kazhdan-subgroup-proof`.
