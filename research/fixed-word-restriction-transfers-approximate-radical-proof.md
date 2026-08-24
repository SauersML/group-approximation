---
rg: 2
id: fixed-word-restriction-transfers-approximate-radical-proof
kind: route
title: Restrict every output microstate through the finitely many embedding words
target: marked-approximate-radical-survives-solution-group-embedding
requires:
  - slofstra-solution-group-embedding-preserves-marked-involutions
---

Choose finite presentations for `G` and `Gamma`.  For every generator `s` of
`G`, fix a word `W_s` in the generators of `Gamma` representing `phi(s)`.
Given any normalized-HS asymptotic representation `rho_n` of `Gamma`, define

```text
sigma_n(s)=rho_n(W_s).
```

Every defining relator of `G` becomes, after substitution, a fixed word that
is trivial in `Gamma`.  A fixed van Kampen derivation in the finite
presentation of `Gamma`, together with the unitary invariance and triangle
inequality of normalized Hilbert--Schmidt norm, shows its defect under
`rho_n` tends to zero.  Thus `sigma_n` is an asymptotic representation of
`G`.

By hypothesis, `||sigma_n(J')-I||_2->0`.  The equality `phi(J')=J` is another
fixed equality in `Gamma`, so the same word-defect estimate gives

```text
||rho_n(J)-sigma_n(J')||_2->0.
```

Therefore `||rho_n(J)-I||_2->0` for every asymptotic representation of
`Gamma`.  Injectivity of `phi` and `J'!=1` give `J!=1`.  A hyperlinear
approximation would have to separate this nontrivial element, a contradiction.
