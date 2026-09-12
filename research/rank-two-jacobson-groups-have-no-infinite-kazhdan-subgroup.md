---
rg: 2
id: rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup
kind: claim
title: Rank-two general linear groups over the torsion-defect and finite-field Jacobson algebras have only finite Kazhdan subgroups, so every compression defect there is trivial
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the positive theorem from rank four; this explains why the same criterion cannot reach rank two over these rings, because the rank-two groups have no infinite Kazhdan subgroup at all, and it leaves rank three untouched.
  full-defect-ring-non-mf-at-rank-two: that reaches rank two when the defect is full, through the properly infinite structure of the ring rather than through a Kazhdan subgroup of the rank-two group; this shows that over the nonfull torsion-defect rings rank two carries no Kazhdan subgroup for the criterion to use.
  integral-jacobson-defect-has-no-normal-kazhdan-subgroup: that is characteristic zero at every rank, excluding normal Kazhdan subgroups of the defect while infinite Kazhdan subgroups exist; this is rank two over the torsion rings and finite fields, excluding infinite Kazhdan subgroups altogether.
  order-two-universal-ring-has-no-infinite-corner: that kills the properly infinite corner route to low rank over the order-two ring; this kills the Kazhdan-subgroup route at rank two over every torsion modulus and every finite field.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `A_m = Z<s,t | ts = 1, m(1 - st) = 0>` for
`m >= 2`, and let `J_k = k<s,t | ts = 1>` for a finite field `k`.  Every
subgroup with property (T) of

```text
GL_2(A_m)        or        GL_2(J_k)                                     (RT1)
```

is finite.  Consequently, for every subgroup `Delta` of either group and
every Kazhdan `L <= Delta`,

```text
D_Delta(L) = 1,                                                          (RT2)
```

and every homomorphism from any group `P` into either group kills
`D_P(L_0)` for every Kazhdan `L_0 <= P`.

**What it means for the torsion problem.**  The normal-Kazhdan
criterion, and every variant that needs an infinite Kazhdan subgroup in
the target, is inert at rank two over these rings; no placement of
witnesses inside `EL_2(A_m)` or `EL_2(J_k)` can work, and neither can a
homomorphic encoding.  It does not say the rank-two groups are MF, and
it says nothing about rank three, where `SL_3(Z) <= EL_3` is Kazhdan.
The rank-four theorem's threshold is therefore not an artifact of the
proof at rank two; whether rank three is reachable is open.

**Literature input.**  Guentner--Higson--Weinberger, *The Novikov
conjecture for linear groups*, Publ. Math. IHES 101 (2005), Section 5,
Theorem 4: every countable subgroup of `GL(2, K)`, `K` any field, has
the Haagerup property (statement checked in the published paper on
2026-09-09).  A countable group with both property (T) and the Haagerup
property is finite.

Derivation: `rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup-proof`.
