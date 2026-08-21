---
rg: 2
id: rectangular-escape
kind: claim
title: Equivariant whole maps admit rectangular escape
invalidates: [rectangular-whole-map-extraction]
artifacts:
  - research/artifacts/affine-leavitt-normalized-hs-decoder-audit-2026-08-21.md
---

For every finite perfect pairing `b : V × W → F₂`, the direct-sum pairing on
`V′ = V⊕V`, `W′ = W⊕W` with the four coordinate embeddings satisfies
`b′(Rᵢv, Lⱼw) = δᵢⱼ b(v,w)` exactly, deterministically, and fully
translation-equivariantly — evading the `1/36` theorem purely because the
codomains are larger. Unitary covariance and trace balance do not close the
escape. The live theorem this forces is same-orbit closure (same-orbit-closure).

The escape persists at equal **ambient matrix dimension**.  If the source
perfect pairing has Weyl dimension `N`, place it in `M_N` with multiplicity
`N`; the direct-sum target pairing has Weyl dimension `N^2` and can be placed
irreducibly on the same `N^2`-dimensional Hilbert space.  Thus

```text
label_dimension * multiplicity = ambient_dimension
```

is preserved while label dimension doubles and multiplicity contracts.  The
construction iterates, so finite-depth functoriality, deterministic
equivariance, canonical Fourier marginals, and equality of total matrix size
still do not imply a common reservoir.  A valid decoder must charge this
label/multiplicity conversion or close a cycle back onto the identical
multiplicity carrier.
