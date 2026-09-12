---
rg: 2
id: zpc-robust-compiler-nonhyperlinear-route
kind: route
title: A quantitatively sound explicit ZPC-to-LCS compiler yields a nonhyperlinear group
target: non-hyperlinear-group
requires:
  - perfect-zpc-irs-quantum-gap-game
  - explicit-zpc-irs-gap-game-witness
  - controlled-linear-predication-normal-form
  - zpc-selector-robust-lcs-compiler
  - perfect-lcs-gap-implies-nonhyperlinear
artifacts:
  - research/artifacts/zpc-perfect-decoding-gap-audit-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

Use the concrete source game supplied by `explicit-zpc-irs-gap-game-witness`.
The robust compiler gives a finite binary LCS `L(G)` with a perfect commuting
strategy and a constant `eta>0` such that an output strategy of value
`>=1-eta` would decode to a source strategy of value `>1/2`.  Since the source
quantum value is `<1/2`,

```text
omega^q(L(G)) <= 1-eta < 1,
```

while perfect ZPC-IRS completeness gives `omega^co(L(G))=1`.
`perfect-lcs-gap-implies-nonhyperlinear` therefore makes the explicitly listed
solution group of `L(G)` nonhyperlinear.

This route is the quantitative repair of the invalidated
`zpc-compiler-nonhyperlinear-route`: it blocks both failure modes exposed by
the audit, nonclosed finite-dimensional quantum strategies and a merely
existential unnamed source game.
