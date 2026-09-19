---
rg: 2
id: bernoulli-factor-decoder-schreier-gap-proof
kind: route
title: Turn a Bernoulli site decoder into a PVM and identify transport with factor error
target: finite-bernoulli-site-decoder-has-schreier-error-floor
requires:
  - infinite-schreier-pvm-transport-kills-finite-mark
  - global-schreier-pvm-is-stronger-than-action-soficity
---

For `x in X`, put

```text
E_x=1_{f^{-1}(x)} in L^infinity(Omega).                 (BFP1)
```

Because `f` has finite image, `(E_x)` is a finite-support orthogonal PVM and
`sum_x tau(E_x)=1`. Let `u_s` implement the Bernoulli shift. For two labels
`a,b in X`, the elementary one-hot identity is

```text
sum_x |1_{a=x}-1_{b=x}|^2=2 1_{a!=b}.                  (BFP2)
```

Apply `(BFP2)` pointwise to the two partitions
`(u_sE_xu_s^*)_x` and `(E_(sx))_x`. Invariance of product measure gives

```text
sum_x ||u_sE_xu_s^*-E_(sx)||_2^2
 =2 Pr[f(s omega)!=s f(omega)].                        (BFP3)
```

The proof of the PVM transport inequality `(ISP3)` uses only tracial
Cauchy--Schwarz and the scalar Schreier gap, so it applies verbatim in a
finite tracial von Neumann algebra. (For a finite cylinder decoder one may
instead use the regular matrix representation of its finite Boolean atom
algebra.) Applied to `(BFP1)`, it gives

```text
2 (1/|S|)sum_s Pr[f(s omega)!=s f(omega)] >= 2 gamma,
```

which is `(BSD1)`.

Finally, a polynomial in finitely many commuting coordinate projections is
constant on their finite Boolean atoms. Every spectral projection or finite
Borel function of finitely many such polynomials is constant on the same
atoms. A complete orthogonal family labelled by finitely many sites
therefore has the form `(BFP1)`. If its equivariance energy were controlled
by raw Bernoulli relator energy, evaluation in the exact Bernoulli crossed
product would make the proposed upper bound zero, contradicting `(BFP3)`
and `(BSD1)`.
