---
rg: 2
id: thompson-f-subgroup-pair-certificates-collapse-proof
kind: route
title: "Assemble the obstruction: co-amenability of rigid stabilizers kills (S), the commensurated classification kills (C) and (G), and Theorem A′ identifies the survivors"
target: thompson-f-subgroup-pair-certificates-collapse
requires:
  - thompson-f-commensurated-subgroups-are-trivial-or-normal
  - thompson-f-rigid-stabilizer-schreier-graphs-are-amenable
---

1. *(S).* If `H ⊇ F[a,b]` for dyadic `a < b`, then `Sch(F/H)` is amenable by Theorem A of
   `thompson-f-rigid-stabilizer-schreier-graphs-are-amenable`, so no Ponzi scheme, paradoxical decomposition
   or spectral gap exists on `F/H`: each of these contradicts the existence of Følner sets. The equivalent
   forms of the hypothesis are Theorem A′ of the same claim.
2. *(C).* Let `φ : F → G` have dense image in a totally disconnected locally compact `G`. By the tdlc
   corollary of `thompson-f-commensurated-subgroups-are-trivial-or-normal`, either `G = φ(F)` is discrete
   with `ker φ = 1` (then `G = F` and a certificate for `G` is a certificate for `F` itself) or
   `ker φ ⊇ F′` (then `G` is abelian, hence amenable), or `G` is compact-by-abelian, which is amenable
   (compact groups and abelian groups are amenable, and amenability is closed under extensions of locally
   compact groups; standard). The Schlichting completion of a commensurated `H` is the special case where
   `G` is the closure of the image of `F` in `Sym(F/H)`, and the classification applies to `H` directly:
   `H = 1` or `H ⊇ F′`.
3. *(G).* By the locally finite graph corollary of the same claim, either all vertex stabilizers are
   trivial, or `F′` fixes every vertex, so the action factors through `F/F′ ≅ Z²`.
4. *Survivors.* A subgroup escapes step 1 exactly when it contains no `F[a,b]`, and Theorem A′ gives the two
   equivalent forms. `H = 1` is such a subgroup, and `Sch(F/1)` is the Cayley graph, so the surviving
   subclass contains the root and is not empty of content. ∎
