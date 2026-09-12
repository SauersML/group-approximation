---
rg: 2
id: finite-bounded-spectral-probes-proof
kind: route
title: Block Parseval criterion for a finite family of diagonal transport probes
target: finite-bounded-spectral-probe-obstruction
requires: []
---

Write

```text
w_(psi,chi)=||Q_psi C P_chi||_2^2.                     (1)
```

The two PVMs resolve the identity, so these nonnegative block weights have
the prescribed marginals

```text
sum_psi w_(psi,chi)=tr(P_chi),
sum_chi w_(psi,chi)=tr(Q_psi).                          (2)
```

On the `(psi,chi)` block, `C A_j C^*` acts by `f_j(chi)`
and `B_j` acts by `f_j(sigma^(-1)psi)`.  Orthogonality of all blocks gives

```text
d_j^2=sum_(psi,chi)
 |f_j(chi)-f_j(sigma^(-1)psi)|^2 w_(psi,chi).          (3)
```

Similarly, expansion of the squared difference of two projections gives

```text
E_sigma
 =2 sum_(psi!=sigma chi) w_(psi,chi).                  (4)
```

If `(BSP5)` holds, every wrong block in `(4)` has coefficient at most `K`
times its total coefficient in the sum of `(3)` over `j`.  Correct blocks
have zero coefficient in both expressions.  Summing proves `(BSP4)`.

Conversely choose distinct `chi_0,chi_1`.  On `C^2`, let the source atoms
`P_(chi_0),P_(chi_1)` be the two coordinate lines, take the target atoms
`Q_(sigma chi_i)=P_(chi_i)`, and let `C` swap the two lines.  Then `(4)`
gives

```text
E_sigma=2,                                              (5)
```

while `(3)` gives exactly

```text
sum_j d_j^2=||F(chi_0)-F(chi_1)||_2^2.                 (6)
```

Thus `(BSP4)` implies `(BSP5)`, and `(5)--(6)` prove the quantitative
two-atom assertion whenever two feature vectors are sufficiently close.

Finally, boundedness puts `F(Omega)` in a bounded subset of the
finite-dimensional space `C^q`, which is totally bounded.  An infinite
subset cannot have positive minimum pairwise distance: for every
`epsilon>0` it contains distinct points at squared distance below
`epsilon`.  Equations `(5)--(6)` then prove `(BSP6)` and rule out every
finite coercivity constant.

For the matrix-valued extension, use

```text
H=(C^k) direct_sum (C^k),
P_0=Q_(sigma chi_0)=projection onto the first block,
P_1=Q_(sigma chi_1)=projection onto the second block,
```

and let `C` exchange the two blocks by the identity map on `C^k`.  Formula
`(5)` is unchanged.  Direct block calculation gives `(BSP8)` with normalized
matrix Hilbert--Schmidt norms.  A uniformly operator-norm-bounded subset of
`M_k(C)^q` is bounded, hence totally bounded, for the finite-dimensional
Hilbert--Schmidt metric.  Close distinct feature tuples therefore give the
same full-energy/arbitrarily-small-defect countermodels.
