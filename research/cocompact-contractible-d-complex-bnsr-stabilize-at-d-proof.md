---
rg: 2
id: cocompact-contractible-d-complex-bnsr-stabilize-at-d-proof
kind: route
title: "The Sigma^m-criterion with a d-dimensional model pushes heights in every degree at once"
target: cocompact-contractible-d-complex-bnsr-stabilize-at-d
requires: []
---

Sources, read 2026-09-13 from the PDF of M. C. B. Zaremsky, "Separation in the
BNSR-invariants of the pure braid groups", arXiv:1507.08597v1, pages 3–4.

- **§1, page 3:** "if G acts freely (or just properly) and cocompactly on an
  (n − 1)-connected CW-complex, then G is of type F_n."
- **Definition 1.1:** "Let G act properly cocompactly on an (n−1)-connected
  CW-complex Y (so G is of type F_n). Let χ: G → R be a character of G …
  There exists a continuous map h_χ: Y → R such that h_χ(g.y) = χ(g) + h_χ(y)
  … For m ≤ n, the mth BNSR-invariant Σ^m(G) is defined to be
  Σ^m(G) := {[χ] | (Y_{χ≥t})_{t∈R} is essentially (m − 1)-connected}."
- **Citation 1.5** (the Σ^m-criterion of [MMV01]; homological version
  [BR88, Theorem 4.1]): "With the notation from Definition 1.1, [χ] ∈ Σ^m(G)
  if and only if there exists a continuous, cellular G-equivariant map
  φ: Y^{(m)} → Y^{(m)} satisfying h_χ(φ(y)) > h_χ(y) for all y ∈ Y^{(m)}."

**Proof.**
1. `X` is contractible, so it is `(m − 1)`-connected for every `m`. By the
   §1 remark `G` is of type `F_m` for every `m`, i.e. of type `F_∞`.
   Definition 1.1 applies with `Y = X` and any `n`.
2. Fix `m ≥ d`. Always `Σ^m(G) ⊆ Σ^d(G)`.
3. Let `[χ] ∈ Σ^d(G)`. By Citation 1.5 (with `Y = X`, `n = m`, at degree `d`)
   there is a continuous cellular `G`-equivariant `φ: X^{(d)} → X^{(d)}` with
   `h_χ(φ(y)) > h_χ(y)` for all `y`.
4. Since `dim X = d`, `X^{(d)} = X = X^{(m)}`. So `φ` is a continuous cellular
   `G`-equivariant self-map of `X^{(m)}` raising `h_χ` everywhere.
5. By Citation 1.5 at degree `m`, `[χ] ∈ Σ^m(G)`. Hence `Σ^m(G) = Σ^d(G)`. ∎

This is the argument behind the sentence imported in
`type-f-bnsr-invariants-stabilize-at-dimension-citation`: Ershov–Zaremsky
point to "[Zar17, Citation 1.5]" for it.
