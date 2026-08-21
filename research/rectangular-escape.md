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

## Candidate charging mechanisms

- **Fixed-degree PI fingerprint (2026-08-21).**  The standard polynomial
  `s_(2N)` vanishes identically on `M_N tensor I_m` for every
  multiplicity `m` (Amitsur--Levitzki), yet has definite nonzero
  normalized-HS evaluations on tuples generating `M_(N^2)`.  On this
  recorded escape the gap is already present: the source Weyl words sit
  in `M_N tensor I_N`, so any fixed source tuple has
  `s_(2N)`-evaluation exactly `0`, while the escaped target pairing
  acts irreducibly on the `N^2`-dimensional space, where generic word
  tuples give `||s_(2N)(...)||_2 >= kappa_N > 0`.  Unlike the
  self-indexing dimension oracle
  (`two-generator-amitsur-levitzki-dimension-oracle`, which reads the
  AMBIENT dimension) or the isotypic multiplicity reading of
  `multiplicity-pi-turing-tape-proof`, the fixed degree `2N` is chosen
  from the SOURCE label factor once and for all, and external
  multiplicity cannot spoof it: `X -> X tensor I_m` preserves every
  evaluation.  The open design task is the transport: a compressor
  cycle whose relations force the signed-sum evaluation
  `s_(2N)`(transported words) to be carried to the target side up to
  `o(1)`.  The polynomial is used by the PROOF, not as a relator — each
  monomial is a word matrix, and the analyst forms the signed sum
  externally, exactly as with character projectors and Reynolds
  averages.  Any relation set achieving that transport contradicts this
  escape and charges the label/multiplicity conversion, which is what a
  valid decoder must do.
