---
rg: 2
id: free-splitting-fa-lifts-choose-a-side
kind: claim
title: A section of Aut(F_n) to Out(F_n) over an FA factor-automorphism subgroup of a rank-one splitting is standard or fixes one big vertex
distinct_from:
  outer-covering-lifts-are-virtual-sections: that identifies covering-lift constructions with virtual sections; this constrains what any section looks like on the automorphisms of one factor of a rank-one free splitting.
  aut-out-free-abelianized-extension-splits-rationally: that shows rational cohomology gives no obstruction to virtual sections; this is the nonabelian side-choice step, the free-group analogue of the puncture lying on one side of a separating curve.
artifacts:
  - research/artifacts/bh-aut-out-virtual-section-2026-09-12.md
---

**ESTABLISHED.** Elementary Bass--Serre theory. No novelty is claimed.

**Setting.**
- Let `F_n = ⟨p⟩ ∗ B` with `rank B ≥ 2`, and let `T` be its Bass--Serre tree.
- Let `J_B ≤ Out(F_n)` be the injective image of `β ↦ [id_⟨p⟩ ∗ β]`, for
  `β ∈ Aut(B)`.
- Let `s: Γ → Aut(F_n)` be a section of `π` over `Γ ≤ Out(F_n)`, and put
  `Λ = Γ ∩ J_B`.
- Assume `Λ` has property FA and finite abelianization.

**Statement.** The group `π^{-1}(J_B)` acts on `T` without inversions, and
exactly one of the following holds.
- **(S)** For some `x ∈ F_n`, `s(λ) = ι_x (id ∗ β_λ) ι_x^{-1}` for all
  `λ ∈ Λ`. The fixed tree of `s(Λ)` is the star of the vertex `x⟨p⟩`.
- **(N)** The fixed tree of `s(Λ)` is a single vertex `xB`. After conjugating
  by `ι_x`, `s(λ) = ι_{y(λ)} (id ∗ β_λ)`, where `y: Λ → B` is a cocycle. Then:
  - `ρ(λ) = ι_{y(λ)} β_λ` is a homomorphism `Λ → Aut(B)` lifting
    `λ ↦ [β_λ] ∈ Out(B)`;
  - `s(λ)(p) = y(λ) p y(λ)^{-1}`.

**When the hypothesis holds.** `Aut(F_m)` has property (T) for `m ≥ 4`
(`aut-f4-has-property-t` for `m = 4`; the larger cases are recorded in the
aut-f4 status artifact). So for `n ≥ 5` the hypothesis holds for every
finite-index `Γ`.

**What is still missing.** Excluding virtual sections needs the side choices of
different splittings to be incompatible under `Γ`. That is not proved. In case
(N) the restriction of `ρ` to inner automorphisms raises the same question one
rank down.

The proof is `free-splitting-fa-lifts-choose-a-side-proof`.
