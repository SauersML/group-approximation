---
rg: 2
id: loop-retraction-forces-fp-eventual-section-groups-proof
kind: route
title: The section endomorphism at a commonly fixed letter carries every stage of the lift-ideal construction into a normal closure in the eventual section group
target: loop-retraction-forces-fp-eventual-section-groups
requires:
  - rover-nekrashevych-fp-iff-finite-lift-presentation
---

Notation of the claim.

## 0. The section endomorphism

Every `s in S` fixes `x`, so for a word `w = s_1 ··· s_n` the point `x` stays fixed along the word, and the
word-level section is `w|_x = s_1|_x ··· s_n|_x`. So `σ(w) = w|_x` is the endomorphism of `F` extending `σ` on
letters (inverses: `(s^{-1})|_x = (s|_x)^{-1}` because `s(x) = x`). Since `σ^p` is idempotent on the finite set
`S`, it is the identity on `S_∞ = σ^p(S)`, and `σ(S_∞) = σ^{p+1}(S) = σ^p(σ(S)) ⊆ S_∞`; so `σ` restricts to a
permutation `θ` of `S_∞`, of some order `q`, and `σ ∘ π = θ ∘ π` on `F`. `π = σ^p` is a surjective
homomorphism `F -> F_∞` that is the identity on `F_∞`.

`N` is section-closed (a word acting trivially has trivially acting sections), so `σ(N) ⊆ N`.

## 1. The lift ideal in stages

For a finite `R ⊆ N`, `M = ⟨⟨R⟩⟩_lift` is the union of the transfinite chain `M_0 = ⟨⟨R⟩⟩`,
`M_{α+1} = ⟨⟨M_α ∪ L(M_α)⟩⟩`, `M_λ = ∪_{α<λ} M_α`, where `L(M_α)` is the set of words with trivial root
permutation all of whose sections lie in `M_α`. (The chain is increasing and stabilizes; its limit is normal and
lift-closed, and each stage lies in every lift ideal containing `R`.)

Put `M' = ⟨⟨θ^j(π(R)) : 0 <= j < q⟩⟩_{F_∞}`. It is `θ`-invariant, and `M' ⊆ N ∩ F_∞`, because
`θ^j(π(r)) = σ^{p+j}(r) = r|_{x^{p+j}} in N`.

**Claim.** `π(M_α) ⊆ M'` for every `α`.
- `α = 0`: `π` is a surjective homomorphism, so `π(⟨⟨R⟩⟩_F) = ⟨⟨π(R)⟩⟩_{F_∞} ⊆ M'`.
- Successor: `π(M_{α+1})` is the normal closure in `F_∞` of `π(M_α) ∪ π(L(M_α))`. Let `w in L(M_α)`. Then
  `σ(w) = w|_x in M_α`, so by induction `π(σ(w)) in M'`. But `π ∘ σ = σ^{p+1} = σ ∘ π = θ ∘ π`, so
  `θ(π(w)) in M'` and `π(w) in θ^{-1}(M') = M'`.
- Limits: unions.

## 2. Conclusion

If `V_d(G)` is finitely presented, then by Theorem A (necessity) `N = ⟨⟨R⟩⟩_lift` for a finite `R`. For
`w in N ∩ F_∞`, `w = π(w) in π(N) ⊆ M'`. So `N ∩ F_∞ = M'`, a finitely generated normal subgroup of `F_∞`.
Since `N ∩ F_∞` is the relator kernel of `G_∞ = ⟨S_∞⟩`, `G_∞` is finitely presented. Finally
`{g|_{x^p} : g in G} = π(F)` modulo `N`, which is `G_∞`. ∎
