---
rg: 2
id: finite-torus-root-fourier-has-stationary-aliases
kind: claim
title: Finite torus Fourier compression grades a root group but cannot linearize its coefficients
distinct_from:
  char-p-weyl-blocks-local-commutator-decoder: that uses a characteristic-p Weyl pair to refute a complex additive-commutator decoder; this computes every torus-character component of one additive root group and gives a quantitative additivity floor before any commutator is formed.
  finitely-generated-rational-dilations-preserve-char-p-weyl-cells: that extends the Weyl countercell by rational dilation covariance; this treats finite scalar tori and the proposed character-corner extraction itself.
  steinberg-root-shear-plancherel-covariance: that positively identifies equal Plancherel blocks and shear permutations on a fixed root window; this shows why selecting a purported linear Fourier weight from those blocks has a zero-defect stationary escape.
---

Let `k` be a finite field of characteristic `p`, let `Lambda<=k^x` have
order `m>1`, and put

```text
G=(k,+) rtimes Lambda.
```

Write `u_a` for `(a,1)`, `t_lambda` for `(0,lambda)`, and use the canonical
trace on `C[G]`.  For `rho in dual(Lambda)` define the conjugation-weight
compression

```text
F_rho(a)=m^(-1) sum_(lambda in Lambda)
                    conjugate(rho(lambda)) u_(lambda a).       (TFC1)
```

Equivalently, if

```text
q_chi=m^(-1) sum_lambda conjugate(chi(lambda)) t_lambda,
```

then

```text
F_rho(a)=sum_(chi in dual(Lambda)) q_(rho chi) u_a q_chi.       (TFC2)
```

Thus `(TFC1)` includes both finite torus-character corners
`q_alpha u_a q_beta` and the full ``odd'' or nontrivial Fourier component
obtained by summing the blocks of one conjugation weight.

For `a!=0`, the `m` group words `u_(lambda a)` are distinct.  Hence every
weight has exactly the same canonical normalized-HS mass:

```text
||F_rho(a)||_2^2=1/m.                                          (TFC3)
||q_(rho chi) u_a q_chi||_2^2=1/m^2.                           (TFC3')
```

For nontrivial `rho`, character orthogonality gives `F_rho(0)=0`.  If

```text
epsilon=max_(a,b in k)
 ||F_rho(a+b)-F_rho(a)-F_rho(b)||_2,
```

then repeated addition on the prime-field line through any nonzero `a`
gives

```text
p ||F_rho(a)||_2 <= (p-1) epsilon,

epsilon >= p/((p-1)sqrt(m)).                                  (TFC4)
```

In particular, a nontrivial torus Fourier component has a dimension-free
additivity defect in an **exact finite group representation**.  The same
bound survives arbitrary amplification.  More generally, every map from an
elementary `p`-group to a complex normed vector space which is
`epsilon`-additive and sends zero to zero satisfies

```text
||A(a)|| <= (p-1)epsilon/p.                                   (TFC5)
```

Therefore an exact additive coefficient decoder cannot send a
characteristic-`p` coefficient unit to a nonzero complex projection.

The failure is not repaired by regarding the Fourier weight as a bounded
degree.  Let

```text
E_rho(z)=m^(-1) sum_lambda conjugate(rho(lambda))
                         t_lambda z t_lambda^(-1).
```

These are the spectral projections for the conjugation action, and exact
multiplication is the full character convolution

```text
E_rho(z w)=sum_(sigma tau=rho) E_sigma(z) E_tau(w).             (TFC6)
```

Thus the character labels form a grading, not polynomial degrees.  A
nonzero weight component in `C[(k,+)]` has nonzero powers because this
complex group algebra is semisimple and has no nonzero nilpotents.  Repeated
multiplication therefore reaches every weight in the subgroup it generates;
when the weight is a generator it reaches all `m` weights.
In the finite regular packet none of those aliases is an asymptotically
small tail: `(TFC3)` assigns every component the same mass `1/m`.

Consequently finite torus-character compression, a single off-diagonal
corner, or an odd Fourier component does not provide the coefficient map
missing from `affine-leavitt-steinberg-hs-coefficient-decoder`.  A successful
decoder may still use the **complete** Fourier block system and the paired
Steinberg triangles nonlinearly to recover only the three products in
`(ALD1)`; it must include a coercive relation which excludes the stationary
finite Frobenius packet above.  No additive or bounded-weight extraction can
be that relation by itself.
