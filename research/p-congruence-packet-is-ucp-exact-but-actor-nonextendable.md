---
rg: 2
id: p-congruence-packet-is-ucp-exact-but-actor-nonextendable
kind: claim
title: A mod-p lattice packet is exactly UCP-captured while remaining a uniform same-dimensional arithmetic outlier
distinct_from:
  one-britton-moment-forces-uniform-actor-noncorrectability: that proves every canonical one-Britton packet is uniformly far from a same-dimensional exact arithmetic actor; this shows that the same distance condition, even together with exact lattice centrality and the exact trace-zero commutator moment, is compatible with distance zero from the lattice UCP matrix range.
  sl3-large-prime-hnn-matrix-range-capture: that concerns packets satisfying all approximate relations and canonical moments of the arithmetic HNN group; this finite packet deliberately violates the denominator-transport relation and proves that this full actor covariance, rather than the quantified outlier modulus alone, must construct the UCP point.
  finite-lamp-frame-is-matrix-range-neutral: that proves Morita neutrality after adjoining a fixed lamp frame to an arbitrary pre-existing tuple; this gives an arithmetic packet whose lattice coordinates are exactly in the matrix range but cannot be extended across the inverted-prime root transport.
---

Fix a prime `p`, put

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),   s=e_12(1),
```

and choose a finite symmetric generating set `S` of `Lambda` containing
`s`.  Let `lambda_p` be the left regular representation of
`SL_3(F_p)`, pulled back to `Lambda`, and put `r=|SL_3(F_p)|`.  There are
matrices in dimension `d=2r`,

```text
X_g=I_2 tensor lambda_p(g)       (g in Lambda),
T=T_0 tensor I_r,                H=H_0 tensor I_r,              (PCE1)
```

such that

```text
T_0=diag(1,-1),
H_0=2^(-1/2) [[1,-1],[1,1]].                                  (PCE2)
```

They have all four properties

```text
dist_(2,S)(X,MR_d(Lambda,S))=0,                                (PCE3)
max_(g in S)||[T,X_g]-I||_2=0,                                 (PCE4)
tr_d([T,H])=0,                                                 (PCE5)
inf_(rho:Gamma->U(d))
 max(||H-rho(h)||_2,max_(g in S)||X_g-rho(g)||_2)
 >=max(sqrt(2)/(p+3),c_*),                                     (PCE6)
```

where `c_*=sqrt(2)/(2+4sqrt(|S|)/kappa)` is the one-Britton
noncorrectability constant for a Kazhdan constant `kappa` of `(Lambda,S)`.

Thus the quantified same-dimensional actor-outlier stratum meets the UCP
matrix range **exactly**.  In particular no inequality of the form

```text
dist_(2,S)(X,MR_d) >=
 F(actor distance, lattice-centrality defect, |tr([T,H])|)     (PCE7)
```

can have `F(zeta,0,0)>0` merely because `zeta>0`.  The one-Britton scalar
data do not carry a complete-positivity obstruction.  Any proof of
`sl3-large-prime-hnn-matrix-range-capture` must use the approximate
`Gamma` relations which transport the root `e_12(1)` through `h` (or
equivalent mixed actor covariance); the outlier modulus by itself neither
selects nor obstructs a UCP lift.

## Scope

This is not a counterexample to HMR1.  Indeed `(PCE1)` intentionally cannot
be completed to even an approximate representation of `Gamma` with small
denominator-transport defect: in `Gamma`,

```text
h s h^(-1)=s^p,
```

whereas `X_s^p=I` and `H` commutes with `X_s`.  The theorem is a sharp
firewall against using only the already established one-Britton
noncorrectability modulus in the primal UCP construction.
