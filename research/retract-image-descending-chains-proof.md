---
rg: 2
id: retract-image-descending-chains-proof
kind: route
title: Morphological openings by doubling finite sets give strictly nested retract images
target: retract-images-of-full-shifts-have-infinite-descending-chains
requires: []
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Lemma 1.1, Theorem 1.2 and Corollary 1.3 of the artifact.

- **Openings are idempotent automata:** `h in gamma_F(S)` iff `h f^-1 F <= S` for some `f in F`,
  which reads the configuration on `h F^-1 F` and commutes with left translation. The image is the set
  of supports that are unions of translates `gF`, and `gamma_F` fixes each of them.
- **On `A^G`:** compose with a sitewise retraction `A -> {0,1}`.
- **Nesting:** `g F_(n+1) = g F_n ∪ (g c_n) F_n`, so `X_(F_(n+1)) <= X_(F_n)`.
- **Strictness:** `c_n notin F_n F_n^-1` gives `|F_n| = 2^n`. The indicator of `F_n` lies in
  `X_(F_n)`, but no translate of `F_(n+1)` fits in `F_n`, so it is not in `X_(F_(n+1))`.
- **Corollary:** a strictly monotone map into a well-ordered set would send the chain to an infinite
  strictly descending sequence of ordinals.
