---
rg: 2
id: commutant-density-bounded-type-proof
kind: route
title: Expand the commutant dimension over irreducible multiplicities
target: commutant-density-forces-bounded-type-mass
requires:
  - property-t-laplacian-sos-certificate
  - kazhdan-bounded-unitary-types-are-finite
---

Schur's lemma applied to `(BTM1)` gives

```text
End_Gamma(H)=directSum_i M_(m_i)(C).
```

Its dimension is `sum_i m_i^2`.  Since `a_i=n_i m_i/d`, division by `d^2`
gives `(BTM2)`.

Split the sum in `(BTM2)` at degree `K`.  On the low-degree part,
`n_i>=1` and the elementary inequality `sum x_i^2<=(sum x_i)^2` give

```text
sum_(n_i<=K) (a_i/n_i)^2 <= sum_(n_i<=K) a_i^2 <= mu_K^2.  (1)
```

On the complementary part `n_i>=K+1`, so

```text
sum_(n_i>K) (a_i/n_i)^2
 <=(K+1)^(-2) sum_(n_i>K) a_i^2
 <=(K+1)^(-2)(1-mu_K)^2.                                  (2)
```

Equations `(1)` and `(2)` prove `(BTM3)`.  If `c>=eta`, its weaker second
bound implies `mu_K^2>=eta-(K+1)^(-2)`, proving `(BTM4)`.

For the converse, there are at most `r_K` low-degree summands in `(BTM1)`.
Since `n_i<=K` on them,

```text
sum_(n_i<=K)(a_i/n_i)^2
 >=K^(-2)sum_(n_i<=K)a_i^2
 >=K^(-2)mu_K^2/r_K,
```

where the last step is Cauchy--Schwarz.  This proves `(BTM4b)`.

For `(BTM5)`, `dim End_Gamma(H)>=dim(W)` gives `eta=c_0q^2`.  Choose `K`
so `(K+1)^(-2)<=c_0q^2/2`; `(BTM4)` gives the stated mass and degree
bounds.  Finally, below a Kazhdan gap the exact adjoint Laplacian has no
nonzero spectrum: its spectral range is its invariant space, namely the
commutant.  This proves the property-`(T)` interpretation.
