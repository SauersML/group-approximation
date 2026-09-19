---
rg: 2
id: profinite-free-compressor-coefficient-proof
kind: route
title: Implement every compressor by a permutation of one common finite regular quotient
target: profinite-free-compressors-retain-coefficient-residual
requires:
  - kt-two-compressor-irrep-flow-has-profinite-stationary-points
  - opposite-transvections-are-free-but-finite-lamp-windows-close
  - one-bounded-type-coefficient-separates-unbounded-exits
---

Write

```text
b=sum_(g in F)c_g g.
```

Apply `(PFC1)` to a finite set containing `F` and all pair differences
`g^(-1)h`, `g!=h` in `F`.  Put `q=q_T`, `Q=Q_T`, and represent the base on
`ell^2(Q)` by

```text
pi(g)=lambda_Q(q(g)).                                   (PFP1)
```

For an automorphism `theta of Q`, let `C_theta` be the permutation unitary

```text
C_theta delta_x=delta_(theta(x)).                       (PFP2)
```

Then direct evaluation on the standard basis gives

```text
C_theta lambda_Q(y) C_theta^(-1)=lambda_Q(theta(y)).    (PFP3)
```

Assign `rho(t_i)=C_(bar(alpha_i))`.  Equations `(PFC1)` and `(PFP3)` show
that every covariance relation in `(PFC2)` holds exactly, so this defines an
exact finite-dimensional representation of `H`.

The support-separation requirement on `q` makes the elements `q(g)`,
`g in F`, pairwise distinct.  Orthogonality of the corresponding regular
matrices gives

```text
||rho(b)||_2^2=sum_(g in F)|c_g|^2
              =||lambda_Lambda(b)||_2^2,                (PFP4)
```

which is `(PFC3)`.

If `sigma:F_r->U(m)` is any finite-dimensional representation, replace

```text
pi(g) by pi(g) tensor 1,
C_(bar(alpha_i)) by C_(bar(alpha_i)) tensor sigma(t_i). (PFP5)
```

The second tensor factor commutes with the base, so `(PFP3)` and every
covariance row remain exact, while normalized tensor-product trace preserves
`(PFP4)`.  Residual finiteness of `F_r` supplies a finite regular `sigma`
which is canonical on any prescribed finite pure stable-letter window.

For the Kun--Thom specialization, take a finite quotient of the ambient
residually finite actor `G`.  The inclusions
`q(A)Qq(A)^(-1)<=Q` and `q(B)Qq(B)^(-1)<=Q` are equalities because `Q` is
finite, proving `(PFC1)`.  Finally apply the regular coefficient estimate
for `b=z(1-a)` from
`one-bounded-type-coefficient-separates-unbounded-exits` to `(PFP4)`, which
gives `(PFC5)`.
