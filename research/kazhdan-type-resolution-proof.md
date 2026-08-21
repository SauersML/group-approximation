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
