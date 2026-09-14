---
rg: 2
id: generic-limit-of-subshift-sl-models-is-simple-kazhdan-proof
kind: route
title: Relations of bounded length see only bounded windows; admissible subshifts are the closure of the infinite transitive ones; Pavlov–Schmieding genericity and a Baire argument
target: generic-limit-of-subshift-sl-models-is-simple-kazhdan
requires: [subshift-algebra-groups-embed-in-marked-groups, subshift-elementary-group-simple-iff-infinite-minimal, simple-kazhdan-lef-group-from-minimal-subshift, generic-transitive-subshift-is-regular-toeplitz, subshift-elementary-group-word-problem-degree, subshift-crossed-product-k0-is-coinvariant-group]
artifacts:
  - research/artifacts/sk-free-2-generic-limits-2026-09-13.md
---

Full argument: the artifact.

**1. Closure of the models.**
- Relations of length `≤ λ` of the model `y` (period `N > 2λ`, so no aliasing) and of `G_Y` depend only on the `(2λ+1)`-languages of `O_y` and `Y`.
- So the infinite limits are exactly `G_Y` for infinite chain-transitive `Y`: Euler walks on word graphs give the approximants, and limits of orbits of unbounded period are infinite and chain transitive. Models of bounded period are isolated.
- `Y ↦ G_Y` is a homeomorphism onto its image (`subshift-algebra-groups-embed-in-marked-groups`). Adding `e_ij(1)`, a fixed word in the other generators, does not change this.

**2. Admissible = `T̄′[A]`.**
- (⊆) The edge shift of `G_{M−1}(Y)` is irreducible and not a cycle, so it is infinite transitive with the same `M`-language.
- (⊇) Strong connectivity of word graphs passes to limits, and a finite limit would force periodic approximants.

**3. Genericity.**
- Minimality is `G_δ`: `∀m ∃M` every `M`-word contains every `m`-word, a clopen condition for each `(m,M)`.
- It is dense by `generic-transitive-subshift-is-regular-toeplitz` (Theorem 1.3), restricted to the clopen `S[A]`.
- The edge-shift approximants are non-minimal and dense. By Baire, the minimal set is not `F_σ`.
- `Adm_A` is a Cantor set: closed in the zero-dimensional compact `S[A]`, and perfect because `T′` is perfect (Pavlov–Schmieding p. 2).

**4. Transport.**
- Simple ⟺ infinite minimal (`subshift-elementary-group-simple-iff-infinite-minimal`), and then simple Kazhdan LEF (`simple-kazhdan-lef-group-from-minimal-subshift`).
- Regular Toeplitz, uniquely ergodic, zero entropy and strongly orbit equivalent to the universal odometer (Theorem 1.3(1),(3)), with rank-one `K_0(R_X)` by `subshift-crossed-product-k0-is-coinvariant-group`.
- Word problem ≡_T `L(X)` (`subshift-elementary-group-word-problem-degree`). Recursive languages are countable, hence meager in a perfect space. ∎
