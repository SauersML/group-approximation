---
rg: 2
id: generator-column-global-pauli-exactification-proof
kind: route
title: Compose sampled Weyl expansion with central-extension exactification
target: generator-column-pauli-test-globalizes-but-does-not-pin-sites
requires: []
---

De la Salle assumes that the two independent column measures obey

```text
hat(mu)(chi)<=1-1/c,       hat(nu)(a)<=1-1/c'
```

off the trivial character.  Proposition 3.8 first charges the commutation
and magic-square checks, obtaining sampled Weyl energy at most
`1320 epsilon`.  Applying the two Poincare inequalities for `mu` and `nu`
gives `(GCP1)`.

Corollary 1.8 in the same source applies average Gowers--Hatami to the finite
Weyl--Heisenberg central extension.  For full-average Weyl defect `delta`,
it gives average squared error less than `30000 delta` on each of the two
abelian subgroups and amplification trace at most `1+16 delta`.  Substituting
`delta=1320 c c' epsilon` gives exactly `(GCP2)` and `(GCP3)`.  For an
abelian representation `U(g)=sum_chi chi(g)p_chi`, Fourier orthogonality
gives

```text
E_g ||U(g)-U'(g)||_2^2=sum_chi ||p_chi-p'_chi||_2^2,
```

with the normalized convention.  Finally the unique irreducible
central-sign representation of the finite Weyl--Heisenberg group is the
`2^n`-dimensional Pauli representation, proving `(GCP4)`.

For the escape, `Q` anticommutes with each `X_i` and commutes with every
`Z_i`.  Expanding `exp(i theta Q)` proves `(GCP6)`.  Simultaneous conjugacy
preserves all PVM products and acceptance probabilities, so the corrected
generator-column test has exactly zero loss.  At `theta=pi/8` both
coefficients in `(GCP6)` are nonzero, hence the fine observable at every
named site differs from the original site Pauli.  This proves the dense
fixed-frame escape without contradicting `(GCP2)`: the latter simply chooses
the globally conjugated Pauli factor.

De la Salle's Example 3.10 constructs each support from the coordinate
functionals, equivalently the columns of a generator matrix of a
`[K,n,d]` code.  For `K,d=Theta(n)`, the spectral constants and all analytic
losses above are uniform, while selecting a column needs `log K=O(log n)`
bits.  The theorem contains no group words or filling-area estimate, proving
the final compiler distinction.

