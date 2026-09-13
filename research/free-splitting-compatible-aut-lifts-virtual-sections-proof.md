---
rg: 2
id: free-splitting-compatible-aut-lifts-virtual-sections-proof
kind: route
title: Ping-pong makes the images of the two factors adjacent, so the splitting tree is preserved and a fixed vertex of either type restricts to a section
target: free-splitting-compatible-aut-lifts-are-virtual-sections
requires: []
artifacts:
  - research/artifacts/bh-out-fn-into-aut-fm-2026-09-12.md
---

Complete proof: Sections 2--3 of the artifact.

1. **Adjacency.** Let `φ(A) = aAa^{-1}` and `φ(C) = cCc^{-1}`, and put `u = aA`,
   `v = cC`. Suppose `d(u,v) ≥ 3`, and let `w` be a `C`-vertex strictly inside
   `[u,v]`.
   - Nontrivial elements of `G_u` map the half-tree at `u` containing `v` into
     the half-tree at `v` containing `u`, minus the first. Nontrivial elements of
     `G_v` do the symmetric thing. This works because edge stabilizers are
     trivial.
   - So by ping-pong `⟨G_u, G_v⟩ ∩ G_w = 1`. But `⟨G_u, G_v⟩ = φ(G) = G` and
     `G_w ≠ 1`, a contradiction.
   - Hence `u` and `v` are adjacent. Let `e_φ` be the edge joining them, so that
     `φ(A) = e_φAe_φ^{-1}` and `φ(C) = e_φCe_φ^{-1}`.
2. **Tree action.** `gA ↦ φ(g)e_φA`, `gC ↦ φ(g)e_φC`, `g ↦ φ(g)e_φ`.
   - It is well defined and type-preserving.
   - `e_(φψ) = φ(e_ψ)e_φ`, by uniqueness of the joining edge, so `φ ↦ φ_T` is a
     homomorphism. This proves (a).
3. **Normalization.** Conjugating `ρ` by `ι_g` keeps the hypotheses, moves fixed
   vertices by `g^{-1}`, and leaves every induced class unchanged: with
   `b′ = g^{-1}ρ(γ)(g)b`, one gets `ι_(b′)^{-1}ρ′(γ)|_A = ι_b^{-1}ρ(γ)|_A`.
4. **Fixed `A`-vertex.** Normalize to `1A`. Then `e_γ ∈ A`, `ρ(γ)(A) = A`, and
   `λ = ρ|_A`.
5. **Fixed `C`-vertex.** Normalize to `1C`.
   - Then `e_γ ∈ C` is unique, `ρ(γ)(C) = C`, and `e_(γδ) = ρ(γ)(e_δ)e_γ` holds
     exactly in `C`.
   - Put `λ(γ) = ι_(e_γ)^{-1}ρ(γ)|_A`. Then
     `λ(γ)λ(δ) = ι_(ρ(γ)(e_δ)e_γ)^{-1}ρ(γδ)|_A = λ(γδ)`, and `[λ(γ)] = γ`.
6. **(c).** FA gives a fixed vertex for the action in (a).
7. **(d).** Define `γ·gA = ρ(γ)(g)a_γA`, with canonical coset `a_γA`. The relation
   `a_(γδ)A = ρ(γ)(a_δ)a_γA` makes it an action. On the pointwise stabilizer of a
   finite orbit, normalize to `A` and restrict.
