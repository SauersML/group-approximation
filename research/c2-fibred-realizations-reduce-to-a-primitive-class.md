---
rg: 2
id: c2-fibred-realizations-reduce-to-a-primitive-class
kind: claim
title: For the admissible (C2) pair, passing the canonical-cycle test in any fibred K(G,1) (any marked graph, any fibration in the BNS cone) implies a basis-free condition on the pair (N, c_H). A passing complex needs a free factor system of F_4 carried by N whose H_1 contains c_H, and a marked rose passes if and only if c_H is the class of an F_4-primitive element of N. Finite-cover norms on H_1(L cap F_4) cannot give an Aut-invariant obstruction, because at index 9 the pushed class is primitive and its Z-twisted Fox vector is unimodular.
distinct_from:
  c2-rose-mapping-torus-has-no-one-lift-core: that excludes one rose and its Nielsen ball of radius 3, basis by basis. This replaces the basis by an intrinsic condition (P_free) on the pair, valid for every marked graph and every fibration at once, and shows the index-9 certificate cannot be made basis-free.
  two-cell-injective-maps-realize-relative-eg-pairs: that reduces RP(H,G) to 2-cell-injective maps into some K(G,1). This decides the fibred K(G,1)s of (C2) up to a free-factor problem in F_4.
---

**Reduction, ESTABLISHED** through `c2-fibred-realizations-reduce-to-a-primitive-class-proof`.
Unreviewed. Parts (R1)–(R4) are proved by hand. (R5) is exact finite computation, replayed by
`experiments/c2-primitive-class-2026-09-19/coker.py` and `twisted.py`. (R6) is a heuristic
search and proves nothing: it found no primitive representative.

## Setting

The pair is the one of `admissible-ab-nonzero-two-cell-base-exists` and
`c2-rose-mapping-torus-has-no-one-lift-core`:
- `G = ⟨x,y | w⟩ = F_4 ⋊_φ ⟨y⟩` and `H = N ⋊ ⟨y⟩` with `N = H ∩ F_4`;
- `c_H` is the generator of `H_1(N)^φ ≅ H_2(H) ≅ Z`, and its image in `H_1(F_4)` is the primitive
  vector `v = (−1,0,1,1)`.

A K(G,1) `X` *passes* when the generator of `Z_2(X_H)` has support that injects into the 2-cells of
`X`. This is the canonical-cycle test (T0) of the rose node. Every 2-cell-injective realization of
`RP(H,G)` in `X` needs `X` to pass.

## Statement

Say that `(N, c_H)` satisfies `(P_k)` when there are nontrivial finitely generated subgroups
`A_1, …, A_k ≤ N` and elements `g_1, …, g_k ∈ F_4` with both of these properties:
- the conjugates `g_i A_i g_i^{-1}` generate their free product, and that product is a free factor
  of `F_4`;
- `c_H` lies in the image of `⊕_i H_1(A_i) → H_1(N)`.

Write `(P_free)` for the statement that some `(P_k)` holds. Write `(P)` for this: some `q ∈ N` that is primitive in `F_4` has `[q] = c_H` in `H_1(N)`.

- **(R1) Every marked graph.** Let `f: Γ → Γ` be any topological representative of `φ` on any marked
  graph. If `M_f` passes, then `(P_k)` holds, where `k ≤ 4` is the number of components of the support
  of the canonical cycle.
- **(R2) `(P_1)` is `(P)`.**
- **(R3) Roses.** Some marked rose `R` for `φ` has a mapping torus `M_f` that passes, with connected
  support, if and only if `(P)` holds. Here `f: R → R` is the rose map of an automorphism representing
  `φ`.
- **(R4) Every fibration.** Let `χ: G → Z` be primitive, and suppose its kernel `F_χ` is free of
  finite rank. These are the fibrations in the BNS cone. Let `N_χ = H ∩ F_χ`.
  Then `χ(H) = Z`, and (R1)–(R3) hold verbatim for `(F_χ, N_χ, c_H^χ)`, with `c_H^χ` the generator of `H_1(N_χ)^{φ_χ}`.
- **(R5) No finite-cover norm at index 9.** Take the index-9 subgroup `L ⊇ H` of the rose node and
  `J = L ∩ F_4` (rank 28).
  - The image of `c_H` in `H_1(J)` is primitive.
  - `H_1(J)/im H_1(N) ≅ Z`.
  - The twisted Fox vector of `c_H` over `Z[t^{±1}]`, for the unique character of `J` that kills
    `N`, is constant and has an entry `1`, so it is unimodular.

  By Lemma B of the proof, these are exactly the conditions a primitive `q ∈ N` would impose inside
  `J`. So nothing at this level can exclude `(P)`. The least `ℓ^1`-norm of `c_H` over all bases of
  `J` is 1.
- **(R6) Search.** `c_H = 2[F_2] + 2[F_3] + [F_1]`, with `F_1 = SpSrs`, `F_2 = rP`, `F_3 = QsRq` in `N`.
  Among the tested products of `N`-conjugates of these five loops, and their hill-climbs in the coset
  `q_0[N,N]`, none is primitive.
  The least Whitehead-minimal cyclic length found is 11 (`RESULTS.md`).

## Consequence for the target

To exclude every fibred K(G,1) of (C2), it now suffices to prove `¬(P_k)` for `k = 1, …, 4` (and each `χ`). This
is one question about the subgroup `N` of `F_4`, with no choice of basis, graph or fibration. The
index-9 certificate of the rose node is basis-dependent and cannot be promoted, by (R5). The
remaining non-fibred K(G,1)s (slide complexes) are not touched here.

## Attempts

- w15-048 (2026-09-19): reduction (R1)–(R4) proved. The Aut-invariant index-9 norm is blocked, as
  shown in (R5). The search for `(P)` was negative, as recorded in (R6).
