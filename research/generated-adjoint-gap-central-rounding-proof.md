---
rg: 2
id: generated-adjoint-gap-central-rounding-proof
kind: route
title: Project every generator to the generated commutant and decode its central character
target: uniform-generated-adjoint-gap-rounds-to-central-code
requires: []
---

Let `E_(A')` be the trace-preserving conditional expectation onto the
commutant inside the finite-dimensional ambient algebra and
put

```text
 z_i=E_(A')(Q_i).
```

The finite-dimensional Wedderburn decomposition is

```text
 A=direct_sum_alpha(M_(n_alpha) tensor I_(m_alpha)),
 A'=direct_sum_alpha(I_(n_alpha) tensor M_(m_alpha)).   (GAC1)
```

Consequently `E_(A')` maps `A` onto `Z(A)`: on block `alpha` it takes the
normalized matrix trace in `M_(n_alpha)`.  Thus every `z_i` is a central
selfadjoint contraction.  Applying `(UGA3)` to `T=Q_i` gives

```text
 ||Q_i-z_i||_2^2
 <=lambda^(-1)(1/L)sum_j||[Q_i,Q_j]||_2^2.             (GAC2)
```

Let `S_i=sgn(z_i)`, choosing either sign on the zero spectral projection.
Since conditional expectation is the orthogonal `L_2` projection and
`Q_i^2=I`, on every scalar spectral value `t in [-1,1]` one has

```text
 (1-|t|)^2<=1-t^2.
```

Pythagoras therefore yields

```text
 ||Q_i-S_i||_2^2
  =||Q_i-z_i||_2^2+||z_i-S_i||_2^2
 <=2||Q_i-z_i||_2^2.                                  (GAC3)
```

The `S_i` are central reflections and hence commute.  Averaging `(GAC2)`--
`(GAC3)` gives, with

```text
 a=(1/L)sum_i||Q_i-S_i||_2^2,
```

the bound

```text
 a<=2E_com/lambda.                                     (GAC4)
```

For a check row `h`, telescope its ordered `Q`-product against the
commuting `S`-product.  Since `|h|<=q`, Cauchy--Schwarz gives

```text
 ||prod_(i in h)S_i-I||_2^2
 <=2||prod_(i in h)Q_i-I||_2^2
   +2q sum_(i in h)||Q_i-S_i||_2^2.                    (GAC5)
```

Every column occurs at most `D` times and `M>=cL`, so the parity energy of
`S` is at most

```text
 E_par(S)<=2E_par+(2qD/c)a
          <=2E_par+4qD E_com/(c lambda).               (GAC6)
```

Resolve the finite-dimensional center into its atoms.  On each atom the
tuple `S` is a scalar string `x in F_2^L`, and a violated check contributes
exactly `4` to `(GAC6)`.  Choose a nearest codeword `d(x) in C` on each
atom and let `S'_i` be its coordinate signs.  The classical soundness
`(UGA1)` gives

```text
 (1/L)sum_i||S_i-S'_i||_2^2<=E_par(S)/kappa.            (GAC7)
```

Finally use `||Q_i-S'_i||_2^2<=2||Q_i-S_i||_2^2+
2||S_i-S'_i||_2^2`, average, and substitute `(GAC4)` and `(GAC6)`.  This is
exactly `(UGA4)`.  The last assertion follows by contraposition.
