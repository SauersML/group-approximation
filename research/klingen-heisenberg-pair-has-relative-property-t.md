---
rg: 2
id: klingen-heisenberg-pair-has-relative-property-t
kind: claim
title: The Klingen radical is relatively Kazhdan in every nonamenable Klingen subgroup
distinct_from:
  klingen-center-kills-isw-condition-one: that uses relative (T) of subpairs of the Kazhdan group Sp_4(Z), which is trivial; this is relative (T) inside the NON-Kazhdan group H x| Sigma, the ambient needed to run Ioana--Spaas--Wiersma inside a parabolic subgroup, where amenability of the radical matters.
  elementary-linear-semidir-pair-relative-t: that is the abelian pair (R^2 x| SL_2(R), R^2); this lifts relative (T) through a non-split central extension with infinite center, where the naive quotient argument fails (compare (Z,Z)).
---

**CLAIM.**  Let `H` be a central extension `1 -> Z -> H -> Z^2 -> 1`
with center generator `z` and `[H,H] = <z^m>` for some `m >= 1` (the
integer Heisenberg group `H_3(Z)`, or the Klingen radical `H_omega` of
`Sp_4(Z)` with law `N(v,c)N(w,d) = N(v+w, c+d+omega(v,w))`, `m = 2`).
Let `Sigma < SL_2(Z)` be nonamenable and let `Gamma = H x| Sigma`,
where `Sigma` fixes `z` and acts on `H/<z> = Z^2` in the standard way.
Then

```text
(Gamma, H) has the relative property (T).                     (KHT)
```

In particular this holds for the Klingen subgroup `H_omega x| SL_2(Z)`
of `Sp_4(Z)` and for every `H_omega x| F` with `F < SL_2(Z)` free of
finite index.

**Why it matters.**  The 2026-09-16 swarm note listed relative (T) of
`(E, H_omega)` as an unchecked sketch.  `(KHT)` is the rigidity input
for running Ioana--Spaas--Wiersma Theorem C inside the Klingen
parabolic instead of on all of `Sp_4(Z)`.  Inside the parabolic the
Connes-embeddability wall of `sp4-isw-theorem-c-embeddable-twist-data-exists`
is far weaker, because the radical is amenable and the Levi is virtually
free.  The price is on the cocycle side; see
`theorem-c-on-klingen-subgroups-needs-non-free-radical-action`.
