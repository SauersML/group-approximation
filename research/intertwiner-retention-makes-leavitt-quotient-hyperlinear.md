---
rg: 2
id: intertwiner-retention-makes-leavitt-quotient-hyperlinear
kind: claim
title: A positive-rank sector of the left-right intertwiner representations that is almost reducing, almost trivial on the kernel and retains one quotient element makes the simple Leavitt quotient hyperlinear
distinct_from:
  leavitt-presentation-double-positive-rank-retention: that is the open existence of such a sector for the Shulman-induced unstable pairs; this is the established implication from its existence to hyperlinearity.
  hyperlinear-near-representation-criterion: that is the Kahl--Schneider abstract criterion through amenable near representations; this is a concrete compression criterion on Hilbert--Schmidt spaces of exact free-group representations, tied to one quotient.
  abstract-unitary-embedding-upgrades-to-hyperlinear: that supplies the last step (an injective homomorphism into a tracial ultraproduct gives hyperlinearity); this is the construction of that homomorphism from a retained sector.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

Setting of `leavitt-presentation-double-forces-restriction-instability`:
`Q = F/K` the simple nonsofic Leavitt quotient, `u_n, v_n : F -> U(d_n)`
exact, `Pi_n(f)(T) = u_n(f) T v_n(f)^*` on `H_n = HS(C^(d_n))`.  For
subspaces `W_n <= H_n` with projections `P_n`, `r_n = dim W_n`, and the
normalized Hilbert--Schmidt norm `||.||_(2,r_n)` on operators of `W_n`,
consider:

```text
(IR1)  ||(1 - P_n) Pi_n(f) P_n||_(2,r_n) -> 0        for every f in F;
(IR2)  ||(Pi_n(k) - 1) P_n||_(2,r_n) -> 0            for every k in K;
(IR3)  liminf_n ||(Pi_n(f_0) - 1) P_n||_(2,r_n) > 0  for some f_0 in F - K.
```

**Theorem.**  If (IR1)--(IR3) hold then `Q` is hyperlinear; since `Q` is
nonsofic, it is then a hyperlinear nonsofic group.

**Exact sectors cannot work.**  An exactly `K`-trivial, exactly
`Pi_n(F)`-invariant `W_n` carries a finite-dimensional representation of
`Q`, trivial by `finitely-generated-map-groups-are-residually-finite` (2), so
(IR3) fails.  A successful sector is genuinely asymptotic: almost `K`-trivial,
almost reducing, of positive trace-visible rank, and not repairable to an
exact quotient representation at any finite stage.
