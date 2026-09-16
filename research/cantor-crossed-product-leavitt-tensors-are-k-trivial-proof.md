---
rg: 2
id: cantor-crossed-product-leavitt-tensors-are-k-trivial-proof
kind: route
title: B ⊗ L is the crossed product LC(X, L) ⋊ P, whose coefficient ring is a K-trivial flat union of regular coherent products of L
target: cantor-crossed-product-leavitt-tensors-are-k-trivial
requires:
  - fjc-crossed-products-of-k-trivial-regular-rings-vanish
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - coherent-flat-group-algebra-hosts-force-fp-infinity
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

Full proofs are in Sections 4 and 5 of the artifact. `LC(X, D)` is the ring of
locally constant `D`-valued functions. For compact `X` it is the directed union
`⋃_𝒫 D^𝒫` over finite clopen partitions `𝒫`, where `D^𝒫 ≅ ∏_(U∈𝒫) D`.

**Part 1.**
1. **Identification (artifact Lemma 4.1).** `LC(X, k) ⊗_k D -> LC(X, D)`,
   `f ⊗ d |-> f(−) d`, is an equivariant ring isomorphism. It is the directed
   union of the isomorphisms `k^𝒫 ⊗ D ≅ D^𝒫`.
2. **Crossed product.** `B ⊗ L = (LC(X, k) ⊗ L)_(α⊗id, 1)P`, so
   `B ⊗ L ≅ LC(X, L)_(α',1)P` with `α'_g(F) = F ∘ g^−1`. With `τ ≡ 1` this is a
   crossed product in the sense of Bartels–Reich.
3. **`K`-triviality of `R = LC(X, L)` (artifact Lemma 4.2).**
   - `K_n(L^𝒫) = ⊕_U K_n(L) = 0`, by Ara–Cortiñas Proposition 6.2
     (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
   - `K_n` commutes with directed colimits of rings, so `K_n(R) = 0` for all `n`.
4. **Regular coherence of `R[Z^m]` (artifact Lemma 4.3), on both sides.**
   - `L[t_1, ..., t_m]` is regular coherent by Ara–Cortiñas Lemma 6.1 (regular
     supercoherence of Leavitt path algebras). The anti-automorphism
     `x_i <-> y_i` transfers this between left and right modules.
   - `L[Z^m]` is its central localization at monomials. This is flat, and every
     finitely presented module is a base change, so it is regular coherent.
   - Finite products `L[Z^m]^𝒫` are regular coherent.
   - `R[Z^m] ≅ ⋃_𝒫 L[Z^m]^𝒫`. For `𝒬` refining `𝒫`, `D^𝒬 = ⊕_V D e_V` with
     `D e_V ≅ D^𝒫 e_(U(V))`, a finitely generated projective `D^𝒫`-module. So
     the union is flat over each `L[Z^m]^𝒫`.
   - A finitely presented module over the union is a base change from some
     `L[Z^m]^𝒫`, and flat base change carries a finite projective resolution to
     one over the union.
5. **Assembly.** `fjc-crossed-products-of-k-trivial-regular-rings-vanish` applies
   to `R_(α',1)P` and gives `K_n(B ⊗ L) = 0` for every `n`. ∎

**Part 2.** Let `S <= P` be finitely generated and not `FP_infinity` over `k`.
- `f ⊗ g |-> f g` is a bijection `LC(X, k) ⊗_k k[P] -> B` of right
  `k[P]`-modules, since `(f g)(1 h) = f gh`.
- Take a `k`-basis `{f_j}` of `LC(X, k)` containing `1`, and left coset
  representatives `c` of `S` in `P` containing `e`. Then `B` is a free right
  `k[S]`-module with basis `{f_j c}`, which contains `1`.
- So `k[S]` is a unital subalgebra, `B` is flat over it, and it is a direct
  summand of `B` as a right `k[S]`-module.
- If `B` were left coherent, `coherent-flat-group-algebra-hosts-force-fp-infinity`(1)
  would make `S` of type `FP_infinity` over `k`, a contradiction. ∎
