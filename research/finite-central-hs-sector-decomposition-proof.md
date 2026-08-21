---
rg: 2
id: finite-central-hs-sector-decomposition-proof
kind: route
title: Spectral cutting of an almost-central finite-order unitary
target: finite-central-hs-sector-decomposition
requires: []
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Write `Z_n` for the image of the central generator.  The relator `z^m=1`
gives `||Z_n^m-1||_2->0`.  Functional calculus rounds `Z_n`, at `o(1)`
normalized-HS cost, to an exact `m`-torsion unitary

```text
Z'_n=sum_(j=0)^(m-1) omega^j P_(j,n),  omega=e^(2 pi i/m). (FCS2)
```

The centrality relators give `||[Z'_n,U_(s,n)]||_2->0` for every fixed
presentation generator `s`.  Since distinct `m`th roots of unity have a fixed
spectral separation, expanding the commutator in the blocks of `(FCS2)` gives

```text
sum_(i!=j) ||P_i U_s P_j||_(2,n)^2 -> 0.                 (FCS3)
```

Thus every generator is `o(1)` from its block diagonal compression.  On each
block the compression is almost unitary; polar decomposition replaces it by a
unitary with the same dimension-weighted `o(1)` cost.  Apply this
simultaneously to the finite generating set.

Choose a section `sigma:Q->E`.  Its multiplication law has the form

```text
sigma(g)sigma(h)=z^(c(g,h)) sigma(gh).                    (FCS4)
```

After the block cut, `(FCS4)` on `P_j` is exactly the projective relation with
multiplier `omega^(j c(g,h))`.  Every presentation relator is a fixed word, so
word telescoping transfers the original `o(1)` defects plus the block/polar
errors to the projective relators.  Squared normalized HS norm is additive
with dimension weights across orthogonal blocks, proving item 3 and the final
positive-density consequence.
