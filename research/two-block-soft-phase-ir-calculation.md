---
rg: 2
id: two-block-soft-phase-ir-calculation
kind: route
title: Put a near square root of one on two growing multiplicity blocks
target: soft-cyclic-phases-can-support-all-ir-clauses
requires: []
---

The matrices in `(SCP3)` are exact representations of the infinite cyclic
free group.  Block swap gives the stated global conjugacy, and direct
multiplication verifies the standard unitary equivalence between the
left-right representation and `Ad(sigma_n)`.

For an upper-right block `T`,

```text
sigma_n(a) T sigma_n(a)^*=conjugate(z_n)T,             (TSP1)
```

which proves `(SCP5)`.  Consequently the projection onto `W_n` commutes
with the entire adjoint representation, proving `(IR1)` with zero error.
For `k=a^(2l)`, `(TSP1)` gives the scalar
`conjugate(z_n)^(2l)->1`, proving `(IR2)`.  The case `f_0=a` gives `(SCP6)`
and `(IR3)`.  Formula `(SCP4)` is the dimension count
`s_n^2/(2s_n)^2=1/4`.

The two eigenvalues of `sigma_n(a)` are `1,z_n`, and those of
`sigma_n(a^2)` are `1,z_n^2`.  Both pairs are distinct, so both commutants
are exactly the same two diagonal full matrix blocks, proving `(SCP7)`.
Finally `(SCP2)` gives `z_n^2=exp(4 pi i/N_n)->1` without ever equaling one,
which proves `(SCP8)` and the collapsing finite-label gap.
