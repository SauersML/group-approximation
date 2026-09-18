---
rg: 2
id: rational-leavitt-path-k1-k2-scalar-dichotomy-proof
kind: route
title: Read the unit map off the Ara--Brustenga--Cortiñas sequence and compute K_n(Q) tensor [1]
target: rational-leavitt-path-k1-k2-scalar-dichotomy
requires:
  - abc-leavitt-path-k-theory-exact-sequence
---

Lane proof, not independently reviewed.

1. **The unit map.** `E^0` is finite and `E` has no sinks, so `1_L = Σ_v v`. The unital
   map `Q -> L` factors as `Q -> Q^(E^0) -> L`: first the diagonal `1 -> (1,...,1)`, then
   the inclusion of the vertex subalgebra. On `K_n` the first map is `x -> (x,...,x)`.
   In Theorem 7.6 of Ara--Brustenga--Cortiñas (`abc-leavitt-path-k-theory-exact-sequence`),
   the map `K_n(Q)^(E^0) -> K_n(L)` is the one induced by the vertex inclusion. This comes
   from their comparison of `L` with the Cohn algebra, whose `K`-theory is that of
   `Q^(E^0)`. The identification was taken from the structure of the proof and not
   re-read at the source.
2. **The image.** Put `M = 1 - N_E^t`, an integer matrix, and `C = coker(M : Z^(E^0) -> Z^(E^0))`.
   Exactness of
   `K_n(Q)^(E^0) --M--> K_n(Q)^(E^0) -> K_n(L)`
   identifies the image of the middle group with `coker(M ⊗ K_n(Q)) = C ⊗ K_n(Q)`, by
   right exactness of `⊗`. For `n = 0` this gives `K_0(L) = C`, with `c = [1_L]` the class
   of `(1,...,1)`. So `x ∈ K_n(Q)` maps to `c ⊗ x ∈ C ⊗ K_n(Q) ⊆ K_n(L)`. This does not
   depend on the transpose convention: `c` is intrinsically `[1_L]`.
3. **Inputs about Q.** `K_1(Q) = Q^x ≅ {±1} × Z^(primes)`. By Tate,
   `K_2(Q) ≅ Z/2 ⊕ ⊕_(p odd) F_p^x`, with `F_p^x` cyclic of order `p - 1`. `C` is a
   finitely generated abelian group. A finitely generated torsion abelian group is
   finite.
4. **K_1, c of infinite order.** Choose `f : C -> Z` with `f(c) = k ≠ 0`. Then
   `f ⊗ id` sends `c ⊗ λ` to `λ^k ∈ Q^x`, which is `1` only for `λ = ±1`. So the kernel
   lies in `{±1}`.
5. **K_1, c of finite order m.** `c ⊗ μ^m = mc ⊗ μ = 0`, so `(Q^x)^m` lies in the kernel.
   This is not finitely generated, since it contains `p^m` for every prime `p`.
6. **K_2, c of infinite order.** With `f` as in step 4, `c ⊗ x -> kx` maps the image
   onto `kK_2(Q)`. `kF_p^x ≠ 0` whenever `(p - 1)` does not divide `k`, which holds for
   all `p > k + 1`. So `kK_2(Q)` is an infinite torsion group, hence not finitely
   generated. The image surjects onto it, so it is not finitely generated either.
7. **K_2, c of finite order, c ≠ 0.** Write `C ≅ Z^r ⊕ ⊕_i Z/d_i`. Then `c = (0; c_i)`
   with some `c_i ≢ 0 (mod d_i)`. Project to `Z/d_i`: `c ⊗ x -> c_i x` in
   `K_2(Q)/d_i K_2(Q)`. By Dirichlet, there are infinitely many primes `p ≡ 1 (mod d_i)`.
   For each, `F_p^x/d_i ≅ Z/d_i` and `c_i` times a generator is nonzero. These components
   are independent summands, so the image is infinite torsion and not finitely generated.
8. **c = 0.** The image of `K_2(Q)` is `0`, and the `K_1` kernel is all of `Q^x`.
9. **Example.** For the two-vertex graph in the claim, the monoid relations give
   `e_1 = 2e_1 + 2e_2` and `e_2 = e_1 + 3e_2`, both equivalent to `e_1 + 2e_2 = 0`. So
   `C = Z^2/Z(1,2)`, and `(1,1)` maps to the generator `1` under `(a,b) -> 2a - b`. The
   graph is strongly connected and each vertex carries a loop plus another arrow, so every
   cycle has an exit. By the Abrams--Aranda Pino criterion, `L_Q(E)` is purely infinite
   simple (standard; cited from memory).
