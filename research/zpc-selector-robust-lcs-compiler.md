---
rg: 2
id: zpc-selector-robust-lcs-compiler
kind: claim
title: Tailored ZPC control compiles to an LCS with quantitative near-perfect sound decoding
distinct_from:
  zpc-selector-sound-lcs-compiler: that controls only attained perfect finite-dimensional strategies; Slofstra nonclosure shows that this is insufficient for a hyperlinearity obstruction.
artifacts:
  - research/artifacts/zpc-perfect-decoding-gap-audit-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

There is an effective transformation, at least for the fixed finite game `G`
from `perfect-zpc-irs-quantum-gap-game`, to a finite binary LCS `L(G)` with:

1. every perfect ZPC-IRS strategy for `G` inducing a perfect
   commuting-operator strategy for `L(G)`; and
2. a constant `eta>0` such that every finite-dimensional strategy for `L(G)`
   with value at least `1-eta` decodes to a finite-dimensional strategy for
   `G` with value strictly greater than `1/2`.

Clause 2 is deliberately quantitative.  Since the source game has
`omega*(G)<1/2`, it implies

```text
omega^q(L(G)) <= 1-eta < 1,
```

not merely nonattainment of a perfect strategy.

## Attempts

- Upgrade the existing controlled predication and selector compiler in the
  weighted-algebra formalism of Mastel--Slofstra.  Their weighted homomorphisms
  were designed to transfer **near-perfect** BCS strategies with polynomial
  soundness loss, which is exactly the missing strength here.
- A noncommutative selector gadget must come with a stability modulus: an
  `epsilon`-representation of the selector relations must be close enough, in
  aggregate weighted loss, to a valid branch-sector decomposition to recover a
  source strategy above `1/2`.
- Pure affine selector auxiliaries remain ruled out by
  `affine-auxiliary-control-flow-barrier`; the quantitative target does not
  reopen that dead space.
- For a source-specific finite game, a compactness-plus-certificate proof may
  be sufficient: once a concrete selector gadget is fixed, prove directly that
  the compact finite-dimensional strategy moment set at output value tending to
  one has no limit point outside valid branch decompositions.
