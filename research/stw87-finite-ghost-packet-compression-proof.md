---
rg: 2
id: stw87-finite-ghost-packet-compression-proof
kind: route
title: Compress compact ghosts into one finite matrix corner
target: stw87-property-a-ghost-packets-are-zero-dimensional
requires:
  - roe-willett-property-a-ghosts-are-compact
artifacts:
  - research/artifacts/stw87-property-a-ghost-packet-firewall-audit-2026-08-30.md
---

Put `H=ell^2(X)`.  By the Roe--Willett theorem, property A identifies the
ghost ideal of `A=C*_u(X)` with `K(H)`.  The net of diagonal finite-set
projections

```text
p_F=chi_F,        F subset X finite,
```

converges strongly to `1_H`.  If `k` is compact, then

```text
norm(k-p_F k p_F) -> 0.                            (1)
```

Indeed, strong convergence gives uniform convergence on the compact sets
`k` of the unit ball and `k^*` of the unit ball, so both
`norm((1-p_F)k)` and `norm(k(1-p_F))` tend to zero.  Because the packet `G`
is finite, one finite `F` makes the left side of `(1)` smaller than
`epsilon` simultaneously for all `g in G`.

Every rank-one matrix unit `e_(xy)`, for `x,y in F`, has finite propagation
and therefore lies in `A`.  Hence

```text
p_F A p_F = p_F B(H) p_F = M_F.
```

Define

```text
psi:A -> M_F,       psi(a)=p_F a p_F,
phi:M_F -> A,       phi(b)=b.
```

Compression is c.p.c. and inclusion of the corner is a star-homomorphism;
in particular `phi` is c.p.c. order zero.  Equation `(1)` now reads

```text
norm(phi psi(g)-g)<epsilon       (g in G),
```

which is a nuclear-dimension-zero approximation on the prescribed packet.
The construction imposes no diagonal-bimodularity or other restriction on
the admissible approximation maps.

Finally, the quotient map `A -> A/K(H)` kills every ghost because the ghost
ideal equals `K(H)`.  Thus neither a finite ghost packet in `A` nor the class
of such a packet in the uniform Roe corona can supply the missing lower
bound.  The conclusion is intentionally packet-local: it says nothing about
finite sets that also contain noncompact non-ghost operators, and it does not
turn a family of packetwise corners into one global finite-dimensional
approximation scheme for all of `A`.
