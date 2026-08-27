---
rg: 2
id: sl3-joint-hecke-multiplicity-has-a-majority-phase-sector
kind: claim
title: Canonical SL3 double microstates have an extensive common-phase joint Hecke-multiplicity sector
artifacts:
  - research/artifacts/sl3-joint-determinant-index-audit-2026-08-21.md
distinct_from:
  sl3-canonical-double-has-a-correctable-vertex: that asks to correct one whole ambient vertex to an exact representation; this asks only for a majority phase sector for one fold word and permits both vertices to remain global outliers.
  source-hecke-data-leave-projective-square-free: that proves scalar source Hecke data cannot select the mixed phase; this asks for matrix-coordinate multiplicity coherence of the joint extension.
  sl3-regular-arithmetic-double-fold-mark-collapse: that forces the fold trace modulus to one; this weaker terminal asks only for a fixed positive lower bound, already enough to contradict canonical character.
---

Put `D=A*_C A` for

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
w=i_0(h)i_1(h)^(-1),       h=diag(2,1,1/2).
```

There is `kappa>0` such that every canonical-character normalized-HS
microstate sequence `sigma_n` of `D` admits projections `p_n`, phases
`z_n`, and a decomposition of `p_n` into finite joint `C-C` Hecke-
multiplicity packets satisfying

```text
tr(p_n) >= 1/2+kappa,
||(sigma_n(w)-z_n I)p_n||_2 -> 0.                       (JHM1)
```

The packet decomposition is required to be simultaneous for the two vertex
assignments and compatible with the `h`-transport incidence maps; separate
Wedderburn multiplicities of the two `C` restrictions do not qualify.

## Attempts

Determinant and additive index cannot produce `(JHM1)`:
`sl3-hnn-fold-determinant-and-index-are-trace-blind` realizes trace-zero
determinant-one commutators in every dimension and makes all equal-rank
relative indices vanish.  Scalar source Hecke data are also insufficient by
`source-hecke-data-leave-projective-square-free`.  Exact finite-dimensional
joint extensions fold completely, but every remaining canonical enemy has
both ambient vertices uniformly far from exact representations.  The open
step is therefore an extensive matrix-coordinate matching theorem for the
joint Hecke multiplicities, not a congruence, determinant, or source-only
moment identity.

There is also an exact one-edge expander fence.
`sl3-one-parahoric-multiplicity-flow-has-a-tracezero-gauge` tensors any
joint parahoric packet with a spectator multiplicity space and inserts a
cyclic shift in one of the two transports.  It preserves all one-edge
transport equations and normalized multiplicity flow while making the
local fold trace exactly zero.  Thus the index-forty-two packet cannot reach
`(JHM1)` by a stronger coset spectral gap.  The narrowed positive terminal
is `sl3-joint-parahoric-loops-share-a-majority-carrier`: synchronize the six
directional packets on one majority carrier, where the already proved
rank-two parahoric triangle can kill the spectator gauge.
