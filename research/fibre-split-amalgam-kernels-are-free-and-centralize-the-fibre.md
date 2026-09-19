---
rg: 2
id: fibre-split-amalgam-kernels-are-free-and-centralize-the-fibre
kind: claim
title: When two subgroups of an extension split over a common normal fibre, the kernel of their amalgam onto the join is free, centralizes the fibre, and is the graph of one map from the complement-amalgam kernel to the fibre
distinct_from:
  jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel: that states points 1-3 for the rank-three Jacobson halves (OPEN, awaiting verification); this proves them for any pair of fibre-split subgroups of any extension, adds freeness and the fibred-square identification, and applies to rank 2n in jacobson-symbol-half-amalgams-are-sofic-with-free-kernel.
  jacobson-el3-amalgam-kernel-is-residually-finite: that derives residual finiteness of the rank-three kernel from Baumslag's theorem on the ambient cone amalgam (OPEN); here the kernel is free outright, because it meets no conjugate of a vertex group, and no residual finiteness of the ambient amalgam is used.
  vertex-injective-quotients-give-hughes-free-division-rings: that uses the same Bass-Serre freeness for a vertex-injective quotient of an amalgam to build division rings; this applies it to the complement amalgam of a split extension and transports it to the kernel of the full amalgam, together with the fibre-centralizing and graph structure.
artifacts:
  - research/fibre-split-amalgam-kernels-proof.md
---

**ESTABLISHED** (route `fibre-split-amalgam-kernels-proof`; elementary, uses the normal form theorem for amalgams
and Serre's theorem that a group acting freely without inversions on a tree is free).

**Setting.** Let `E` be a group, `L ⊴ E`, `Λ = E/L` and `π : E -> Λ`. Let `A_0, B_0 <= E` with
`A_0 ∩ L = B_0 ∩ L = 1`. Put
```text
A = L A_0,   B = L B_0,   C_0 = A_0 ∩ B_0,   C = L C_0,
```
and assume
```text
(H)   π(A_0) ∩ π(B_0) = π(C_0).
```
Let `P = A *_C B` and `U = A_0 *_(C_0) B_0`, with canonical maps `Φ : P -> E` and `λ = π Φ : U -> Λ`. Put
`N = ker Φ`, `K = ker λ` and `ℓ = Φ|_K : K -> L`.

**Theorem.**
0. `A ∩ B = C`, `A_0 ∩ C = B_0 ∩ C = C_0`, and `A = L ⋊ A_0`, `B = L ⋊ B_0`, `C = L ⋊ C_0`.
1. **(Split.)** `L` is normal in `P`, the natural map `U -> P` is injective, and `P = L ⋊ U`. `U` acts on `L` through
   `Φ` followed by conjugation in `E`.
2. **(Graph.)** `N ∩ L = 1` and `[N, L] = 1`. The projection `p : P -> U` maps `N` isomorphically onto `K`, with
   inverse `k -> ℓ(k)^(-1) k`. So `N` is the graph of the homomorphism `ℓ : K -> L`.
3. **(Free.)** `K`, and hence `N`, is a free group. In particular `N` is residually finite, and every subgroup of `N`
   is residually finite and sofic.
4. **(Join.)** `Φ(U) = <A_0, B_0> =: E_0`, `N ∩ U = ker(Φ|_U) = ker ℓ`, and `ℓ(K) = E_0 ∩ L`. Now suppose
   `E_0 = E`. Then:
   * `ℓ` is onto, `E ≅ U / ker ℓ`, and `N / (N ∩ U) ≅ L`;
   * `N ∩ U` is normal in `P`, and `P / (N ∩ U) ≅ L ⋊ E ≅ E ×_Λ E = {(e, e') : π(e) = π(e')}`;
   * for every `r in N` with `ℓ(p(r)) != 1`, if `L` has no nontrivial proper `E`-invariant normal subgroup (for
     example `L` simple), then `N = (N ∩ U) · <<r>>_P`.
5. **(Sofic ambient.)** If `A` and `B` are sofic and `C` is amenable, then `P` is sofic
   (`elek-szabo-amalgams-over-amenable-subgroups-are-sofic`).

**Consequence (reduction).** Under 4 and 5, `E` embeds diagonally in `E ×_Λ E`, which is a subgroup of `E x E`.
So `E` is sofic if and only if `P / (N ∩ U)` is (closure under products and subgroups, `elek-szabo-sofic-permanence`).
The same argument gives the hyperlinear version once closure of hyperlinearity under finite products and subgroups is
imported; that import is not made here. Soficity of `E` is therefore exactly
the question whether the sofic group `P` stays sofic modulo the free normal subgroup `N ∩ U = ker ℓ`, which lies in
the complement `U` and centralizes `L`. No property of `N` as an abstract group, and no subgroup of it, can
obstruct soficity of `E`.
