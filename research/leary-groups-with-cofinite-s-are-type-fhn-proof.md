---
rg: 2
id: leary-groups-with-cofinite-s-are-type-fhn-proof
kind: route
title: "Apply isolated-vertex replacement to an (n-1)-acyclic slab of Leary's branched cube complex"
target: leary-groups-with-cofinite-s-are-type-fhn
requires:
  - isolated-type-fn-vertex-stabilizers-give-type-fhn
  - leary-gls-cocompact-slabs-with-isolated-stabilizers
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part3.md
---

Theorem L of `research/artifacts/zp-fpn-fhn-2026-09-13-part3.md`, §10.

1. By `leary-gls-cocompact-slabs-with-isolated-stabilizers`, `G_L(S)` acts on
   the contractible `X_L^{(S)}` with an invariant height function. Slabs
   `X(m)` are cocompact. Stabilizers are trivial except `π_1(L)` at vertices
   of height not in `S`, with cone neighbourhoods over `𝕊(L̃)`. Unbranched
   vertices have ascending and descending links `L`.
2. Take `m ≥ max |ℤ − S|`. The Morse lemma gives
   `H_i(X(m'), X(m)) = ⊕ H̃_{i−1}(L) = 0` for `i ≤ n` and all `m' > m`. With
   contractibility of the union, `X(m)` is `(n−1)`-acyclic.
3. `π_1(L)` is finitely presented because `L` is finite, and of type `FP_n`
   by hypothesis. Apply `isolated-type-fn-vertex-stabilizers-give-type-fhn`.

Unreviewed.
