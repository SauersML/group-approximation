---
rg: 2
id: zpc-selector-robust-lcs-compiler
kind: claim
title: Tailored ZPC control compiles to an LCS with quantitative near-perfect sound decoding
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

- The raw selector signs do **not** have to become one-hot.  The established
  `odd-selector-priority-decoding` partitions every odd joint spectral atom by
  its first active branch and loses only even-parity mass.  Together with
  `onehot-predicated-direct-sum-decoder`, this removes pairwise selector
  overlap from the soundness target.  The remaining local theorem is now
  `zpc-context-mismatch-transducer`.
- Upgrade the existing controlled predication and selector compiler in the
  weighted-algebra formalism of Mastel--Slofstra.  Their weighted homomorphisms
  were designed to transfer **near-perfect** BCS strategies with polynomial
  soundness loss, which is exactly the missing strength here.
- The required stability modulus now concerns cross-context consistency, not
  overlap suppression: equality/covariance checks must make the independently
  priority-decoded copies of each source observable agree in aggregate.
- Pure affine selector auxiliaries remain ruled out by
  `affine-auxiliary-control-flow-barrier`; the quantitative target does not
  reopen that dead space.
- For a source-specific finite game, a compactness-plus-certificate proof may
  be sufficient: once a concrete selector gadget is fixed, prove directly that
  the compact finite-dimensional strategy moment set at output value tending to
  one has no limit point outside valid branch decompositions.
