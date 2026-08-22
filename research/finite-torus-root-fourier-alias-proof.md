---
rg: 2
id: finite-torus-root-fourier-alias-proof
kind: route
title: Fourier-expand the finite Frobenius root packet and telescope the p-cycle
target: finite-torus-root-fourier-has-stationary-aliases
requires: []
---

The covariance `t_lambda u_a t_lambda^(-1)=u_(lambda a)` makes `(TFC1)`
the ordinary spectral projection for conjugation by `Lambda`.  Inserting
`sum_chi q_chi=1` on the two sides of `u_a` proves `(TFC2)`: a block
`q_alpha u_a q_beta` has conjugation character `alpha beta^(-1)`.

For nonzero `a`, scalar multiplication by distinct elements of `Lambda` is
free.  The group basis is orthonormal for the canonical trace, proving the
first formula in `(TFC3)`.  The blocks in `(TFC2)` have orthogonal source and
range character corners.  A direct two-Fourier-sum trace calculation (whose
identity term requires both torus variables to be `1`) gives squared norm
`1/m^2` for each block and hence `(TFC3')`.  Character orthogonality proves
`F_rho(0)=0` when `rho` is nontrivial.

Put `Delta(a,b)=F_rho(a+b)-F_rho(a)-F_rho(b)`.  Induction gives

```text
F_rho(n a)-n F_rho(a)=sum_(j=1)^(n-1) Delta(j a,a).
```

At `n=p`, the left side is `-pF_rho(a)`, because `pa=0`.  The triangle
inequality and `(TFC3)` give `(TFC4)`.  The same telescoping argument proves
the general estimate `(TFC5)`.

Finally the maps `E_rho` are the mutually orthogonal spectral projections
for a finite abelian action.  Expanding `z=sum_sigma E_sigma(z)` and
`w=sum_tau E_tau(w)` and collecting conjugation weights proves `(TFC6)`.
The algebra `C[(k,+)]` is a finite-dimensional commutative semisimple
algebra, so the nonzero element `F_rho(a)` has nonzero powers; their weights
are the corresponding powers of `rho`.
All formulas already hold in the finite group algebra and therefore in its
left regular representation and every amplification.  This supplies the
claimed zero-defect stationary counterpacket.
