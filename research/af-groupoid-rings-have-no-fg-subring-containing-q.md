---
rg: 2
id: af-groupoid-rings-have-no-fg-subring-containing-q
kind: claim
title: For an AF groupoid, no finitely generated ring of compactly supported functions under convolution contains Q, whatever the coefficient functions
distinct_from:
  integral-form-algebras-have-no-fg-subring-containing-q: that covers Steinberg algebras, whose coefficients are locally constant; this covers arbitrary compactly supported coefficient functions (continuous harmonic ones included) on AF groupoids.
  tracial-harmonic-ring-keeps-rational-scalars: that obtains Q in a finitely generated ring from a harmonic function on the transformation groupoid of a Z-action; this shows the same device cannot work on an AF groupoid such as the tail equivalence relation of a Bratteli diagram.
  fg-q-rings-have-no-matrix-representations: that is the representation lemma used here; this applies it to groupoid rings.
artifacts:
  - research/artifacts/gq-deep-adelic-1-uhf-class-verdict.md
---

**ESTABLISHED** by `af-groupoid-rings-have-no-fg-subring-containing-q-proof` (lane proof, not
independently reviewed; elementary).

## Setting

Let `G` be a Hausdorff étale groupoid with compact unit space `G^(0)`. Let `F_c(G, Q)` be the set of
functions `G -> Q` that vanish outside some compact set, with pointwise addition and convolution

    (f * g)(γ) = Σ_(αβ = γ) f(α) g(β).

The sum is finite: if `f` vanishes off a compact `K`, only `α ∈ K ∩ G^(r(γ))` contribute, and this is
a closed discrete subset of `K`. `F_c(G, Q)` is a unital ring with unit `χ_(G^(0))`. It contains every
Steinberg algebra `A_Q(G)`, every ring of compactly supported `Q`-valued continuous functions for the real
topology on `Q`, and every harmonic-type coefficient function.

Call `G` **AF** if every compact subset of `G` lies in a compact open subgroupoid `H ⊇ G^(0)`. Examples:
- the tail equivalence groupoid of a Bratteli diagram, which gives every UHF- or AF-type groupoid model,
  e.g. `K_0 ≅ Z[1/n! : n]`;
- `Γ ⋉ X` for a locally finite group `Γ`;
- every increasing union of compact open subgroupoids.

## Statement

If `G` is AF, then no finitely generated unital subring of `F_c(G, Q)` contains `Q`.

## Consequence

A finitely generated ring containing `Q` cannot be modelled on the AF groupoid of a UHF algebra, with any
choice of coefficient functions. Norm-convergent series in the C*-algebra, which are not compactly
supported functions, are not covered. The groupoid-model reading of the UHF K-budget target is therefore
empty; see `research/artifacts/gq-deep-adelic-1-uhf-class-verdict.md` for the full class verdict.
