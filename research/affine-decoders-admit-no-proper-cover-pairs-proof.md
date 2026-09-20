---
rg: 2
id: affine-decoders-admit-no-proper-cover-pairs-proof
kind: route
title: Lifts of the free generators assemble into a finite-memory right inverse, and direct finiteness makes it onto
target: affine-decoders-admit-no-proper-cover-pairs
requires: []
artifacts:
  - research/artifacts/affine-cover-pairs-direct-finiteness-2026-09-19.md
---

Full proof: the artifact, which covers Lemma 0, Theorem A, Corollaries A1, A2 and K, and the converse.

1. **Translate.** For finitely supported `u`, `F(p+u) = F(p) + L(u)`. So each finitely supported `δ` equals
   `L(u)` for some finitely supported `u` with `p + u ∈ X`.
2. **Assemble a right inverse.** Choose `u_i` with `L(u_i) = e_i δ_e`. Then `T(x) = Σ_{g,i} x_i(g) g.u_i` is an
   R-linear automaton, and `LT = id`. This uses that `V[G]` is free on the `e_i δ_e`.
3. **Make it onto.** Direct finiteness of `M_k(R[G])` gives `TL = id`, because the ring of R-linear automata is
   `M_k(R[G])^op`.
   - Alternatively, surjunctivity of `G` makes the injective automaton `T` onto.
4. **Conclude.** Lifts are unique, so `p + V[G] ⊆ X`. This set is dense and `X` is closed, so `X = V^G`.

**Converse.** If `ST = id ≠ TS`, then `(T(V^G), S)` is a proper linear constant-point SFT cover pair, with
lift `x + T(z − Sx)`.

**Stable finiteness to direct finiteness.** `F_p[G]` stably finite gives `M_k(F_q[G])` directly finite, by
restriction of scalars. Then `M_k(R[G])` is directly finite, by the local-factor decomposition and nilpotent
lifting (`ba` is an invertible idempotent).
