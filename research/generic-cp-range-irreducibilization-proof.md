---
rg: 2
id: generic-cp-range-irreducibilization-proof
kind: route
title: Perturb a faithful scalar matrix state by two irreducible self-adjoint coordinates
target: generic-cp-noise-maximizes-range-block-degree
requires: []
---

Choose a faithful state `f` on `S`.  The map

```text
Omega_0(x)=f(x) I_d
```

is an interior point of the finite-dimensional cone `CP(S,M_d)`: under the
standard identification `CP(S,M_d)=M_d(S^*)_+`, the element `f tensor I_d`
pairs strictly positively with every nonzero element of `M_d(S)_+`.
Strict positivity is uniform on a compact base of that cone, so every
sufficiently small self-adjoint linear perturbation which vanishes at `1`
remains completely positive and unital.

Choose independent `x,y in S_sa` modulo `R1`, and real linear functionals
`ell_x,ell_y` on `S_sa`, vanishing at `1`, which are dual on their span.
Let

```text
H=diag(1,2,...,d),
K=sum_(i=1)^(d-1)(E_(i,i+1)+E_(i+1,i)).
```

The commutant of `H` consists of diagonal matrices, and commuting also with
`K` forces all diagonal entries equal.  Hence `C^*(H,K)=M_d`.  Extend

```text
T(a)=ell_x(a)H+ell_y(a)K
```

complex linearly.  For sufficiently small `epsilon>0`,
`Psi=Omega_0+epsilon T` is ucp.  Its values at `x,y`, modulo scalars, contain
`epsilon H,epsilon K`, so `C^*(Psi(S))=M_d`.  This proves part 1.

For part 2, fix a self-adjoint basis `s_1,...,s_q` of `S`.  On the traceless
matrices consider

```text
L_t(X)=([X,phi_t(s_1)],...,[X,phi_t(s_q)]).
```

The entries of `L_t` are affine polynomials in `t`.  Because `Psi(S)` has
scalar commutant, `L_1` is injective.  Some `(d^2-1)`-square minor is
therefore a nonzero polynomial in `t`; it has only finitely many zeros.
For arbitrarily small positive `t` outside this finite set, `L_t` is
injective.  Thus `phi_t(S)` has scalar commutant, and the finite-dimensional
bicommutant theorem gives `C^*(phi_t(S))=M_d`.

Convexity preserves unital `k`-positivity.  Since unital positive maps are
contractive on self-adjoint elements and have norm one, the triangle
inequality gives `(GCP1)` (the displayed constant two also covers arbitrary
complex `x`).  Choosing such `t_n->_omega 0` proves the sequential statement.

