---
rg: 2
id: kazhdan-type-resolution-proof
kind: route
title: Apply the Kazhdan gap to the conjugation representation and sum off-isotypic blocks
target: kazhdan-generators-resolve-all-fd-types
requires: []
---

Let `M_d` carry normalized Hilbert--Schmidt inner product and let `Gamma`
act by conjugation through `pi`.  Its fixed space is exactly the commutant

```text
F=pi(Gamma)'.                                             (1)
```

Let

```text
B=direct_sum_theta P_theta M_d P_theta                  (2)
```

be the algebra of operators preserving every central isotypic summand.
Since every operator commuting with `pi(Gamma)` preserves those summands,
`F subset B`.  Orthogonal projection onto `B` is

```text
E_B(X)=sum_theta P_theta X P_theta.                      (3)
```

Applying `(KTR1)` to the Hilbert--Schmidt vector `C` gives

```text
dist_2(C,F)^2
 <= kappa^(-2) sum_(s in S)
      ||pi(s)Cpi(s)^*-C||_2^2
 =  kappa^(-2) sum_(s in S)||[C,pi(s)]||_2^2.           (4)
```

Because `F subset B`, equations `(3)--(4)` imply

```text
sum_(sigma!=theta)||P_sigma C P_theta||_2^2
 = ||C-E_B(C)||_2^2
 <= kappa^(-2) sum_(s in S)||[C,pi(s)]||_2^2.           (5)
```

For a unitary `C`, direct expansion and cyclicity of normalized trace give

```text
sum_theta ||C P_theta C^*-P_theta||_2^2
 = 2-2 sum_theta||P_theta C P_theta||_2^2
 = 2 sum_(sigma!=theta)||P_sigma C P_theta||_2^2.       (6)
```

Combining `(5)` and `(6)` proves `(KTR2)`.

For the two-representation statement, let `Gamma` act unitarily on the
Hilbert--Schmidt space `Hom(H_0,H_1)` by

```text
g.X=pi_1(g)Xpi_0(g)^*.                                   (7)
```

Its fixed space `F_01` is the intertwiner space.  By Schur's lemma every
intertwiner preserves irreducible type, so

```text
F_01 subset B_01
 := direct_sum_theta P_theta^1 Hom(H_0,H_1)P_theta^0.    (8)
```

The squared distance from `X` to `B_01` is exactly the left side of
`(KTR3)`.  It is at most the squared distance to `F_01`; applying `(KTR1)`
to `(7)` gives the right side of `(KTR3)`.  Rescaling the Hilbert--Schmidt
inner product by any positive scalar changes both sides equally.
