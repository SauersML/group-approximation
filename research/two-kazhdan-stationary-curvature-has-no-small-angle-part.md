---
rg: 2
id: two-kazhdan-stationary-curvature-has-no-small-angle-part
kind: claim
title: Almost-stationary relator energy has only hard-angle curvature
artifacts:
  - research/artifacts/stationary-curvature-and-operator-flat-gradient-basin-2026-09-05.md
distinct_from:
  two-kazhdan-correction-has-quadratic-rank-curvature: that changes arbitrary tuples before concentrating their curvature; this uses almost-stationarity to prove the original tuples already have that normal form and establishes a gradient-dominance basin.
  kazhdan-approximate-coefficients-have-curved-hodge-control: that evolves a supplied rectangular coefficient map against an exact target; this evolves the generator tuple's relator energy and requires full H2 vanishing.
---

Let G=<S|R> be finitely presented with ordinary H2(G,H_pi)=0 for
every unitary Hilbert representation. Use a fixed generator menu of
distinct nonidentity group elements admitting literal one-letter sections, as with
the twenty elementary generators of SL5; inverse letters are evaluated
as adjoints. Define

```text
E_r(U)=U(r)-I,     delta(U)=max_r||E_r(U)||_2,
F(U)=sum_r||E_r(U)||_2^2.
```

The gradient uses the product normalized-HS Riemannian metric on the
generator unitaries. If delta_j>0 tends to zero and
`||grad F(U_j)||_2=o(delta_j)`, then the unchanged tuples satisfy

```text
lim_(t down to 0) limsup_j max_r
 ||(E_r(U_j)/delta_j)1_(|E_r(U_j)|<=t)||_2=0.          (STG1)
```

For every fixed epsilon>0 this yields complementary HS error at most
epsilon delta_j outside supports of rank at most C_epsilon d_j delta_j^2.
Those supports are not asserted invariant.

There are dimension-independent t0,c0>0 such that

```text
max_r||E_r(U)||op<t0
       implies ||grad F(U)||_2>=c0 delta(U).          (STG2)
```

Hence every critical tuple in that operator-relator neighborhood is
exact. Put M=|R|, c_PL=c0/sqrt(M), and
`C_R=2ell max_s n_s`, where ell is the longest relator length and
n_s counts all occurrences of s or its inverse in the relator list.
Assume the list contains a nonempty word, so C_R>0.
For negative gradient flow starting with operator defect alpha_0<t0,
energy decays at least as exp(-c_PL^2 t) until its first exit; total
HS path length before exit is at most `2sqrt(F(U_0))/c_PL`.
At a finite exit its energy is at most
`F(U_0)(alpha_0/t0)^theta`, where theta=c_PL^2/C_R.

In particular the strict condition

```text
d F(U_0)(alpha_0/t0)^theta < t0^2                   (STG3)
```

precludes exit and gives exact same-dimensional correction at HS
distance O(delta(U_0)). The case alpha_0=0 is already exact.
Without the hybrid condition, hard-angle exit can occur on small
subspaces; neither global stability nor invariant-support repair is
asserted.

DERIVATION
cohomological-descent-tests-stationary-relator-energy
