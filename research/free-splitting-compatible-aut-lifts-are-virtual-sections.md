---
rg: 2
id: free-splitting-compatible-aut-lifts-are-virtual-sections
kind: claim
title: A homomorphism from outer classes of F_n into Aut(F_n * C) preserving the splitting gives a section of Aut to Out whenever it fixes a vertex
distinct_from:
  outer-covering-lifts-are-virtual-sections: that identifies lifts to automorphisms of a finite-index subgroup of F_n with virtual sections; this treats homomorphisms into automorphisms of a larger free product F_n * C that preserve the splitting up to conjugacy, the natural shape of an embedding into Aut(F_m) with m > n.
  free-splitting-fa-lifts-choose-a-side: that constrains a given section of Aut(F_n) to Out(F_n) on one factor of a rank-one splitting of F_n itself; this starts from a homomorphism into Aut(F_n * C) and produces a section, with fixed vertices of both types giving one.
artifacts:
  - research/artifacts/bh-out-fn-into-aut-fm-2026-09-12.md
---

**ESTABLISHED.** Elementary Bass--Serre theory. No novelty is claimed.

**Setting.**
- `G = A ∗ C`, with `A` free of rank `n ≥ 2` and `C ≠ 1` any group.
- `T` is its Bass--Serre tree.
- `L ≤ Out(A)` is any subgroup.
- `ρ: L → Aut(G)` is a homomorphism. For each `γ`, `ρ(γ)` maps `A` and `C` to
  conjugates of themselves and induces `γ` on `A`: if `ρ(γ)(A) = bAb^{-1}`, then
  `[ι_b^{-1} ρ(γ)|_A] = γ` in `Out(A)`.

**Statement.**
- **(a)** `ρ(L)` acts on `T` by type-preserving automorphisms.
- **(b)** If `ρ(L)` fixes a vertex of `T`, there is a homomorphism `λ: L → Aut(A)`
  with `[λ(γ)] = γ`. So `Aut(F_n) → Out(F_n)` splits over `L`.
- **(c)** In particular it splits over `L` whenever `L` has property FA.
- **(d)** If only the conjugacy class of `A` is preserved, still inducing `γ`, then
  `L` acts on `G/A`, and any finite orbit gives a section over a finite-index
  subgroup of `L`.

`ρ` need not be injective.

**Consequence for Boone--Higman.** For `n ≥ 4`, finite-index subgroups of
`Out(F_n)` have (T), because `Aut(F_n)` does (`aut-f4-has-property-t` for `n = 4`,
and the results recorded in its status artifact for `n ≥ 5`), and so they have FA.
Any homomorphism from such a subgroup into `Aut(F_(n+k)) = Aut(A ∗ F_k)` of the
compatible shape is therefore a virtual section of `Aut(F_n) → Out(F_n)`. This
constrains `out-free-groups-virtually-embed-in-aut-free-groups`: embeddings into a
larger rank that respect such a splitting are no easier than the same-rank
question. An embedding bypassing it must preserve no such splitting. If it
preserves only the class `[A]`, it must act on `G/A` without finite orbits.

The derivation is `free-splitting-compatible-aut-lifts-virtual-sections-proof`.
