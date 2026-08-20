---
rg: 2
id: subtree-trace-independence-certificate
kind: claim
title: Fixed adjoint-mixing relations certify approximate trace independence of sibling sign copies
distinct_from:
  relative-t-heisenberg-adjoint-quantum-expansion: that gives a uniform commutant gap in finite Heisenberg quotients; this asks for the scalar covariance estimate between the two designated subtree copies in one approximate group model.
  countable-tracial-amalgam-extension: reduced freeness gives exact independence in the completeness model; this requires a quantitative finite-dimensional certificate forced by finitely many relators.
---

For the sibling sign observables `x` and `y` in
`nekrashevych-clifford-sign-tape`, exhibit a fixed finite family of adjoint
mixing words and constants `C,epsilon_0>0` such that every matrix tuple of
relator energy `E<=epsilon_0` satisfies

```text
|tr(xy)-tr(x)tr(y)| <= C sqrt(E).                         (STI1)
```

The proof must be uniform in tree depth and matrix rank.  It may use a reduced
free-amalgam conditional expectation or a fixed Jacobi/quantum-expander
averaging identity, but it may not assume probabilistic independence merely
because the two supports are disjoint: commuting subalgebras can be perfectly
correlated in a tracial state.

The decisive check is finite: write the adjoint averaging operator on the
fixed local packet and verify a spectral gap on the mean-zero covariance
sector, then telescope the approximate relators at cost `O(sqrt(E))`.

The analytic part of that check is now closed by
`expander-separated-factors-have-independent-traces`: once one sibling lies
in the old spin factor and the other approximately commutes with its fixed
Jacobi expander, conditional expectation gives `(STI1)` directly.  The sole
remaining content is the group-word placement
`subtree-expander-relative-factor-placement`; disjoint support by itself does
not imply that placement.

## Attempts

- Reduced amalgamation makes centered sibling words orthogonal in the intended
  completeness trace, but freeness is not a group relation and gives no
  soundness estimate for arbitrary matrix tuples.
- Average covariance over fixed Jacobi conjugations and compute the singular
  value on the sibling mean-zero bimodule. Disjoint-support commutation alone
  is insufficient because it permits perfectly correlated copies.
