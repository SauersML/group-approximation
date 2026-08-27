---
rg: 2
id: canonical-marked-corner-kazhdan-density-vanishes-proof
kind: route
title: Combine the central-sign trace calculation with the Kazhdan spectral budget
target: canonical-marked-corner-kazhdan-density-vanishes
requires:
  - central-involution-corner-exactification
  - property-t-hs-adjoint-low-spectrum-budget
---

Apply `central-involution-corner-exactification` to the fixed generators and
SOS multiplication window, and denote the corrected tuple by `psi_n`.
Write `d_n^- = rank(e_n)`.  Canonical trace gives

```text
d_n^-/d_n -> 1/2.
```

For every nonidentity `lambda in Lambda`, both `lambda` and `J lambda` are
nonidentity in `G`, and therefore

```text
tr_(d_n^-)(e_n psi_n(lambda) e_n)
 = (tr_(d_n)(psi_n(lambda))-tr_(d_n)(Z_n psi_n(lambda)))
   /(2 d_n^-/d_n)
 -> 0.                                                    (1)
```

Both numerator terms differ by `o(1)` from the original fixed word traces
of `lambda` and `J lambda`.  Thus the compressed `Lambda` character is
canonical.

Fix `eta` with `0<eta<b`.  The property-`(T)` SOS spectral budget gives

```text
tr_ad(1_[eta,b](A_n)) -> 0.                              (2)
```

It remains to control `P_n=1_[0,eta](A_n)`.  Choose distinct
`g_1,...,g_L in Lambda`.  On `P_n`, the average squared displacement by
each fixed `g_i^-1 g_j` is `O_(g_1,...,g_L)(eta)+o(1)`, by telescoping the
generator Dirichlet form and the microstate defects.  Put
`V_i=Ad(psi_n(g_i))` on the marked corner and
`T=L^-1 sum_i V_i`.  The exact identity

```text
(1/L^2) sum_(i,j)||(V_i-V_j)P_n||_2^2
 =2 tr_ad(P_n)-2||T P_n||_2^2
```

and `||TP_n||_2<=||T||_2` therefore give the sharper estimate

```text
tr_ad(P_n)
 <= (1/L^2) sum_(i,j)
      |tr_(d_n^-)(e_n psi_n(g_i^-1 g_j)e_n)|^2
    +O_(g_1,...,g_L)(eta)+o(1).                         (3)
```

By `(1)`, the first term tends to `1/L`.  First let `eta` tend to zero,
then let `L` tend to infinity.  Equations `(2)--(3)` prove `(CMK1)`.

The use of a fixed positive cutoff is the point of the argument:
`commutant-density-trace-blind` alone records only an iterated averaging
limit, while the SOS budget removes the intermediate spectrum uniformly in
the matrix dimension.

Finally let `R_n` be as in `(CMK2)` and fix any `0<b<kappa`.  With
`P_n=1_[0,b](A_n)`, functional calculus gives

```text
tr_ad(R_n A_n)
 >= b tr_ad(R_n(1-P_n))
 >= b(tr_ad(R_n)-tr_ad(P_n)).                           (4)
```

By `(CMK1)`, the last term is `b rho+o(1)`, contradicting the vanishing
average energy in `(CMK2)`.  This proves the energetic form without assuming
that `R_n` is contained in a spectral subspace.
