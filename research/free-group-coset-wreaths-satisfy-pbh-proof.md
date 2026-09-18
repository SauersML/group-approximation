---
rg: 2
id: free-group-coset-wreaths-satisfy-pbh-proof
kind: route
title: Pass to a finite-index normal subgroup N whose G/C-orbits have retract stabilizers, then use the retract case and finite-index closure; for free groups use Marshall Hall and Kurosh
target: free-group-coset-wreaths-satisfy-pbh
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Lane proof (bh-free-10, 2026-09-18), not reviewed.

**Criterion.** Let `N ⊴ G` have finite index, and let `r: N -> N ∩ C` be a retraction.
1. **Orbits.** As an `N`-set, `G/C` has finitely many orbits, at most `[G : N]`. The
   orbit of `gC` has stabilizer
   `N ∩ gCg^(-1) = g (g^(-1) N g ∩ C) g^(-1) = g (N ∩ C) g^(-1)`, because `N` is normal.
2. **Stabilizers are retracts.** Conjugation by `g` restricts to an automorphism `α_g`
   of `N`. So `α_g(N ∩ C)` is a retract of `N`, with retraction `α_g ∘ r ∘ α_g^(-1)`.
3. **Each orbit.** `N ∈ B_A`, being a subgroup of `G`. By case 3 of
   `pbh-coset-wreaths-iff-identity-edge-hnns`, each stabilizer satisfies condition (e)
   in `N`. By the equivalence, `Z/2 wr_(O) N ∈ B_A` for each `N`-orbit `O` of `G/C`.
4. **All orbits.** Over the finitely many orbits `O_1, ..., O_k`, the group
   `Z/2 wr_(G/C) N` embeds diagonally in `∏_i Z/2 wr_(O_i) N`, via
   `(f_1 ⋯ f_k, n) -> ((f_i, n))_i`. This product is in `B_A`
   (`boone-higman-type-a-class-closed-under-finite-extensions`).
5. **Back to `G`.** `Z/2 wr_(G/C) N` has index `[G : N]` in `Z/2 wr_(G/C) G`. So the
   latter is in `B_A`, by finite-index overgroup closure. That is condition (a) for
   `(G, C)`, and the equivalence gives (b)–(e). `∎`

**Free groups.** Let `F` be finitely generated free and `C <= F` finitely generated.
1. **Marshall Hall's theorem.** There is a finite-index subgroup `H <= F` in which `C`
   is a free factor: `H = C * D`.
2. **The normal core.** Let `N` be the normal core of `H` in `F`. It is normal and of
   finite index, and `N <= H`.
3. **Kurosh.** By the Kurosh subgroup theorem applied to `N <= C * D`, `N` is a free
   product of a free group, of the groups `N ∩ hCh^(-1)` over a set of representatives
   `h` of `N\H/C`, and of the groups `N ∩ kDk^(-1)` over representatives of `N\H/D`.
   Choose `h = 1` for the double coset `NC`. This is the Bass--Serre form: the vertex
   fixed by `C` represents its `N`-orbit, and its stabilizer in `N` is `N ∩ C`. So
   `N ∩ C` is a free factor of `N`, hence a retract of `N`: kill the other factors.
4. **Apply the criterion.** `F ∈ B_A`, since `F <= V`. `∎`
