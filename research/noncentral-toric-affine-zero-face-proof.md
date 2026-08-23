---
rg: 2
id: noncentral-toric-affine-zero-face-proof
kind: route
title: Pass a noncentral orbit to the normal toric quotient and test its regular trace
target: noncentral-toric-orbits-have-affine-full-support-zero-face
requires:
  - centralized-clause-zero-face-is-exact-affine-bcs-quotient
  - toric-gap-is-a-relative-fd-central-word-face
---

Pull the canonical regular trace of `barGamma=Gamma/N` back to `Gamma`.
Every clause is the identity, so its `D` expectation is zero; the state is
tracial on the decoded subgroup. Equation `(NTO2)` therefore gives

```text
0=tau_barGamma(H_B)
 =sum_(R in R_B)||R(bar z)||_(2,L(barGamma))^2.
```

Faithfulness of the regular trace proves `(NTO3)`. Notice that no centrality
of the individual clauses was used.

The involution and within-context commutator residuals make the subgroup in
`(NTO4)` elementary abelian. Its group algebra is the direct sum over all of
its characters. A forbidden assignment projection vanishes exactly when
that assignment does not descend to a character of the subgroup. This proves
`(NTO4)` as in the centralized quotient calculation.

The normal toric quotient theorem gives `(NTO5)`: setting
`beta_i a_i b_i=1` makes `a_i b_i` central, and commutation of the two player
factors separately forces `a_i` and `b_i` to become central in their player
quotients. Hence the conjugation orbit has no residual noncentral action in
the normal quotient.

Any exact perfect target representation fixing every clause kills `N` and
factors through `barGamma`. Its context spectral assignments are therefore
characters of the subgroup in `(NTO4)`. If all allowed assignments occur,
they lie in `Sigma_c`; `(NTO4)` supplies the reverse inclusion and proves
`(NTO6)`. Finally `N intersect B={1}` only embeds `B` in `barGamma` and does
not alter its regular trace, completing the phase-safe statement.
