---
rg: 2
id: klingen-center-kills-isw-condition-one
kind: claim
title: No infinite cyclic subgroup, in particular the Klingen long-root center, can carry the non-coboundary condition of Theorem A
distinct_from:
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that bounds the Levi-invariant scalar classes of the FULL Klingen radical H_3(Z); this is the sharper elementary fact that its CENTER — and any subgroup isomorphic to Z — can never serve as the Ioana--Spaas--Wiersma subgroup Lambda at all, because H^2(Z,T) vanishes.
  isw-theorem-a-has-no-data-on-sp4-lattice: that kills Theorem A at Sp_4(Z) uniformly through the finiteness of realizable classes; this kills the specific center-relative variant for every ambient group, by a one-line vanishing on the Lambda side.
---

**CLAIM.**  Let `Gamma` be any countable group and `Lambda <= Gamma`
with `Lambda` infinite cyclic.  Then hypothesis (1) of
Ioana--Spaas--Wiersma Theorem A (arXiv:2006.01874, p. 2,
source-verified 2026-08-21) — that `c_n|_Lambda` is not a
2-coboundary — is unsatisfiable, because

```text
H^2(Z,T) = 0:                                                 (KC1)
```

every `T`-valued 2-cocycle on an infinite cyclic group is a
coboundary.

**Klingen consequence.**  In `Sp_4(Z)` the Klingen radical is the
integer Heisenberg group `H_3(Z)`, normalized by an `SL_2(Z)` Levi
fixing its center `Z(H_3(Z)) = Z`, a long-root subgroup.  The pair
`(Sp_4(Z), Z(H_3(Z)))` has relative property (T) — trivially, since
`Sp_4(Z)` has property (T) (ISW p. 4 records (T) for `Sp_{2n}(R)`,
`n >= 2`, citing BdHV Rmk 3.5.5; lattices inherit it, classically), so
EVERY sub-pair of `Sp_4(Z)` has relative (T) in the Kazhdan--Margulis
sense quoted by ISW (p. 2).  Relative (T) is therefore not the
obstruction: the center-relative run of Theorem A dies at `(KC1)`, one
step earlier, for every ambient group containing a distinguished `Z`.
A Klingen-pair run must instead take `Lambda = H_3(Z)` itself (or a
non-cyclic subgroup); those runs are closed by
`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`
(parabolic-internal, Levi-invariant supply finite) and by
`isw-theorem-a-has-no-data-on-sp4-lattice` (global, any `Lambda`).
The Klingen extension question of the lifting lane is thereby closed
on every route.
