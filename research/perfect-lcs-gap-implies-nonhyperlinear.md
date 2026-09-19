---
rg: 2
id: perfect-lcs-gap-implies-nonhyperlinear
kind: claim
title: A perfect commuting LCS game with quantum value below one has a nonhyperlinear solution group
distinct_from:
  phase-safe-toric-gap-implies-nonhyperlinear: that handles general torically determined games and needs a separate normal-phase-survival hypothesis; for LCS games the standard solution-group criterion and hyperlinear-profile correspondence give the implication directly.
  phase-safe-toric-gap-game-exists: that asks for a concrete toric witness; this is only the established conditional compiler once a perfect LCS gap is available.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Let `G(A,b)` be a finite binary linear-constraint-system game and
`Gamma(A,b)` its solution group with distinguished central involution `J`.
If

```text
omega^co(G(A,b))=1,
omega^q(G(A,b))<1,
```

then `Gamma(A,b)` is not hyperlinear.

Perfect commuting play implies `J` is nontrivial in the solution group by the
Cleve--Liu--Slofstra solution-group criterion.  If `Gamma(A,b)` were
hyperlinear, every nontrivial element, in particular `J`, would be nontrivial
in approximate representations.  Slofstra--Vidick Proposition 4.3 / Corollary
5.3 then gives `omega^q(G(A,b))=1`, contradiction.

This is the exact `epsilon=0` implication highlighted in the abstract of
Taller--Vidick, arXiv:2507.22444.
