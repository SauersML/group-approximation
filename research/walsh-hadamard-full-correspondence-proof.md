---
rg: 2
id: walsh-hadamard-full-correspondence-proof
kind: route
title: Use a mutually unbiased Walsh basis to fill every matrix unit
target: hadamard-edge-has-divergent-full-bi-dimension
requires: []
---

Index the standard basis by `V=(Z/2Z)^r`, so `d=|V|`, and let `D_d` be the
diagonal algebra.  Define the normalized Walsh matrix

```text
(H_d)_(s,t)=d^(-1/2)(-1)^(s dot t).                    (WHP1)
```

It is a real symmetric unitary and `H_d^2=1`.  Every entry is nonzero.  If
`e_s,e_t` are the minimal diagonal projections, then

```text
e_s H_d e_t=(H_d)_(s,t) E_(s,t).                       (WHP2)
```

Hence `D_d H_d D_d` linearly spans every matrix unit, proving `(HBD1)`.

As a right `D_d`-module, `M_d` is the direct sum of its `d` rows, each
isomorphic to the standard module `D_d`.  Thus its Murray--von Neumann right
dimension is `d`.  The column decomposition proves the identical left
dimension, giving `(HBD2)`.  Since the correspondence subspace equals
`M_d`, its ordinary Hilbert-space rank divided by `dim_C(M_d)` is one.

The trace-preserving expectation onto `D_d` keeps only the diagonal.  Every
diagonal entry of `H_d` has modulus `d^(-1/2)`, so with normalized trace

```text
||E_(D_d)(H_d)||_2^2
 =d^(-1) sum_(t in V)|(H_d)_(t,t)|^2
 =1/d.                                                  (WHP3)
```

For nonzero `u in V`, let

```text
a_d=diag(((-1)^(u dot t))_(t in V)).                   (WHP4)
```

This is a trace-zero diagonal involution.  Fourier conjugacy gives

```text
H_d a_d H_d=P_u,                                       (WHP5)
```

where `P_u` is translation by `u`.  Since `u!=0`, `P_u` has zero diagonal,
and `(HBD4)` follows.

Finally put `y_d=H_d-E_(D_d)(H_d)` and choose a closest unitary polar
extension `v_d`.  Since `H_d` is itself an admissible unitary,

```text
||v_d-y_d||_2<=||H_d-y_d||_2=d^(-1/2),
||v_d-H_d||_2<=2d^(-1/2).                              (WHP6)
```

All statements are exact except this explicit vanishing correction.  No
large computation or asymptotic representation theorem is involved.
