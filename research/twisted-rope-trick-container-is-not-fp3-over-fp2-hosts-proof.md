---
rg: 2
id: twisted-rope-trick-container-is-not-fp3-over-fp2-hosts-proof
kind: route
title: "Mayer--Vietoris and Kuenneth: the twisted edge map has infinite kernel on H_2 over a host with finite H_2"
target: twisted-rope-trick-container-is-not-fp3-over-fp2-hosts
requires: []
---

All homology has rational coefficients. Let `A = P × G` and `K = Hig_{ι,ι'}(G)`.

**Mayer–Vietoris.** For the HNN extension `K` of `A` along `L` (Bieri,
*Homological dimension of discrete groups*, Theorem 2.12) there is an exact
segment

    H_3(K) → H_2(L) --α--> H_2(A),   α = H_2(ι × 1) − H_2(ι' × π).

**Künneth.** Over `Q`, `H_2(P × G) = H_2(P) ⊕ (H_1(P) ⊗ H_1(G)) ⊕ H_2(G)`. Let
`κ = (H_2(pr_P), H_2(pr_G)): H_2(A) → H_2(P) ⊕ H_2(G)`.

- `κ` kills the mixed term: a cross product `a × b` of degree-one classes is
  sent by `pr_P` to `a × ε_*(b) = 0`, and similarly by `pr_G`.
- So `ker κ` is the mixed term, finite-dimensional because `P` and `G` are
  finitely generated.
- For any homomorphism `(f, g): L → P × G`,
  `κ ∘ H_2((f, g)) = (H_2(f), H_2(g))`. The trivial homomorphism induces `0`.
- Therefore `κ ∘ α = (H_2(ι) − H_2(ι'), −H_2(π))`, and `ker(κ ∘ α) = V`.

**Counting dimensions.**
- `α` maps `V` into the finite-dimensional `ker κ`. So `ker α ∩ V` has finite
  codimension in `V` and is infinite-dimensional when `V` is.
- By exactness `H_3(K)` maps onto `ker α`, so `H_3(K)` is
  infinite-dimensional.
- A group of type `FP_3(Q)` has finite-dimensional `H_3(-; Q)`: compute with a
  projective resolution finitely generated through degree 3.

**Case 1.** If `H_2(ι) = H_2(ι')`, then `V = ker H_2(π)`. That space is
infinite-dimensional by Lemma 3.4 of Fournier-Facio–Zaremsky arXiv:2607.21727v1
(verbatim: "The induced map H_2(π): H_2(L; Q) → H_2(G; Q) has
infinite-dimensional kernel"). Its proof identifies the integral kernel with
`[F, R]/[R, R]` and uses only that `G` is infinite and `R ≠ 1`. Inner
automorphisms act trivially on homology, so conjugating `ι` by an element of
`P` does not change `H_2(ι)`.

**Case 2.** If `dim H_2(P) < ∞`, then `ker(H_2(ι) − H_2(ι'))` has finite
codimension in `H_2(L)`. Intersected with the infinite-dimensional
`ker H_2(π)` (Lemma 3.4), it is still infinite-dimensional. So `V` is
infinite-dimensional.
