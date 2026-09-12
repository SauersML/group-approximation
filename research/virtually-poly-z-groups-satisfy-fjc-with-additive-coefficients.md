---
rg: 2
id: virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients
kind: claim
title: Virtually poly-Z groups satisfy the K-theoretic Farrell–Jones conjecture with additive categories as coefficients, in every degree
distinct_from:
  e1-ring-spectrum-fj-for-geometric-and-linear-classes: that imports the ring-spectrum form for untwisted group rings R[G]; this is the form with coefficients in an arbitrary additive G-category, which is what covers crossed product rings with a twisting cocycle.
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `G` be a virtually poly-`Z` group, for
example `Z^n`. For every additive `G`-category `A` and every `n ∈ Z`, the
assembly map

```text
asmb_n : H_n^G(E_VCyc G; K_A) -> H_n^G(pt; K_A) = K_n(∫_G A)
```

is bijective. Here `K_A` is the non-connective `K`-theory spectrum over the
orbit category, and `E_VCyc G` is the classifying space for the family of
virtually cyclic subgroups.

**Source.** A. Bartels, F. T. Farrell and W. Lück, *The Farrell–Jones
Conjecture for cocompact lattices in virtually connected Lie groups*,
arXiv:1101.0469. Read from the arXiv e-print TeX source on MSI, 2026-09-12.
- Theorem "Virtually poly-Z-groups" (`the:FJC_virtually_poly_Z-groups`): "Let
  G be a virtually poly-Z-group ... Then both the K-theoretic and the
  L-theoretic Farrell-Jones Conjecture with additive categories as coefficients
  with respect to the family VCyc ... hold for G."
- Definition `def:K-theoretic_Farrell-Jones_Conjecture`: "for any additive
  G-category A the assembly map asmb_n^{G,A} : H_n^G(E_F G; K_A) → H_n^G(pt; K_A)
  = K_n(∫_G A) induced by the projection E_F G → pt is bijective for all n ∈ Z."

The journal reference was not checked. The proof (controlled topology) was not
re-derived.

**Use.** `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` applies the
case `G = Z^(d−1)`, with the coefficient category of a crossed product ring
(`crossed-product-rings-inherit-fjc-with-additive-coefficients`).
