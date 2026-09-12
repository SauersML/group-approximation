---
rg: 2
id: leavitt-tensor-hosts-acyclic-steinberg-and-fp
kind: claim
title: Khanh's acyclicity, Steinberg comparison and finite presentation hold over B ⊗ L for simple B once low K-theory vanishes
distinct_from:
  leavitt-steinberg-map-iso-from-rank-three: that is the Steinberg comparison over L itself, imported from Khanh; this transfers it, together with acyclicity and finite presentation, to every B ⊗ L with B simple and K_1, K_2 of B ⊗ L zero.
  leavitt-unit-group-finitely-presented: that is finite presentability of L^x; this is finite presentability of (B ⊗ L)^x for every finitely presented simple coefficient algebra B satisfying the K-theory hypothesis.
  projective-elementary-fp-kernel-criterion: that criterion asks for finite normal generation of an unstable Steinberg kernel over an arbitrary ring host; here that kernel is proved trivial whenever the host is a simple algebra tensored with L and K_1, K_2 vanish.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
  - research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**ESTABLISHED (conditional on the imported criteria of Khanh
arXiv:2609.08428v1).** Let `B` be a simple unital `F_2`-algebra, let
`L = L_(F_2)(1,2)`, and put `R = B ⊗ L`.

1. If `K_i(R) = 0` for `1 <= i <= N`, then `H_n(GL_r(R); Z) = 0` for
   `1 <= n <= N` and every `r >= 1`. If every `K_i(R)`, `i >= 1`, vanishes,
   then every `GL_r(R)` is integrally acyclic.
2. If `K_1(R) = K_2(R) = 0`, then `GL_m(R) = E_m(R)` for `m >= 2`, and
   `St_r(R) -> GL_r(R)` is an isomorphism for `r >= 3`.
3. If in addition `B` is a finitely presented ring, then `R^x` is finitely
   presented.

For `B = F_2` this is Khanh's theorem. The artifact (Sections 1--4) checks
which of his steps are specific to `L`. Two are.

- **Stable input.** He took `H_n(GL_∞(L)) = 0` from Ara--Brustenga--Cortiñas.
  Here it is the hypothesis on `K_*(R)`.
- **Leavitt word reduction.** Over `F_2`, a nonzero leading coefficient is `1`.
  Over `B ⊗ L` it is some nonzero `c` in `B`. Simplicity of `B` gives
  `Σ y_k c z_k = 1`, and distinct Leavitt words of one length put this finite
  sum into one product. This yields a common right multiplier `X` and left
  inverses `u_i` with `u_i a_i X = 1` and `ker u_i ≅ R`. That is all
  Proposition 4.2 of the source needs.

The remaining steps are ring-general as stated in the source:
- Theorem 2.2 for `F_2`-algebras with `A^2 ≅ A`;
- Theorem 5.1 and Lemma 5.2;
- Menal--Moncasi GE for simple rings with strong division;
- Voronetsky's refinement;
- Krstić--McCool.

## Consumers

- `central-simple-leavitt-tensor-unit-groups-are-simple`
- `leavitt-square-unit-group-is-fp-simple-and-acyclic`
- the reduction route `boone-higman-via-central-simple-leavitt-tensor-host`

DERIVATION
leavitt-tensor-hosts-khanh-transfer-proof
