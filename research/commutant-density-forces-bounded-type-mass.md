---
rg: 2
id: commutant-density-forces-bounded-type-mass
kind: claim
title: Positive normalized adjoint commutant density is positive bounded-degree representation mass
distinct_from:
  commutant-density-trace-blind: that expresses commutant density through character moments and proves its canonical vanishing; this gives a finite-dimensional isotypic inequality identifying exactly what positive density would force.
  canonical-marked-corner-kazhdan-density-vanishes: that excludes low-spectrum density in canonical marked microstates by an SOS argument; this shows that any proposed construction of such density is quantitatively a bounded-representation-type compiler.
  finite-normalizer-covariance-density-no-go: that supplies semidirect regular countermodels to finite covariance; this gives the representation-theoretic meaning of the missing conclusion independently of a particular cell.
---

Let `rho:Gamma->U(H)` be any finite-dimensional unitary representation,
`d=dim(H)`, and decompose it into inequivalent irreducibles as

```text
H=directSum_i (V_i tensor C^(m_i)),       n_i=dim(V_i).       (BTM1)
```

Put

```text
a_i=n_i m_i/d,
c=dim End_Gamma(H)/d^2.
```

Then

```text
c=sum_i (a_i/n_i)^2.                                      (BTM2)
```

For an integer `K>=1`, let `mu_K=sum_(n_i<=K) a_i` be the Hilbert-space
mass carried by irreducibles of degree at most `K`.  One has the sharp
dimension-free estimate

```text
c <= mu_K^2 +(1-mu_K)^2/(K+1)^2
  <= mu_K^2 +1/(K+1)^2.                                  (BTM3)
```

In particular, if `c>=eta` and `(K+1)^(-2)<=eta/2`, then

```text
mu_K>=sqrt(eta/2).                                        (BTM4)
```

If `Gamma` has property `(T)`, let

```text
r_K=|Irr_<=K(Gamma)|<infinity
```

by `kazhdan-bounded-unitary-types-are-finite`.  The converse inequality is

```text
c >= mu_K^2/(K^2 r_K).                                    (BTM4b)
```

Thus, for a fixed Kazhdan group, positive normalized commutant density is
equivalent (with constants depending on the chosen degree cutoff) to
positive Hilbert mass in a bounded finite menu of irreducible types.

If `Gamma` has property `(T)`, choose an adjoint Laplacian cutoff below its
Kazhdan gap.  In every exact representation its low-spectral space is
exactly `End_Gamma(H)`, so the same conclusion applies to any exact version
of `(PCD1)`.  More concretely, a Schur placement giving

```text
dim(W)/d^2 >= c_0 q^2,       W<=End_Gamma(H)              (BTM5)
```

necessarily puts at least `q sqrt(c_0/2)` of the whole Hilbert space in
`Gamma`-irreducibles of degree at most
`ceil(sqrt(2/c_0)/q)`.  Thus the desired old-commutant placement is not a
formal consequence of local Reynolds density: quantitatively, it must
compile forbidden carrier mass into bounded-degree old-`Gamma` type mass.

For canonical microstates of an infinite property-`(T)` subgroup this is
precisely the forbidden phenomenon detected by
`canonical-marked-corner-kazhdan-density-vanishes`.  Therefore `(PCD1)` is
already the substantive trace-promotion gate; describing its input as
coefficient covariance does not weaken what must be proved.  Finite
normalizer covariance cannot perform this compilation by
`finite-normalizer-covariance-density-no-go`.  A live Toeplitz construction
must show explicitly how non-surjectivity forces the bounded-degree mass (or
prove the low-spectrum estimate directly with equivalent strength).
