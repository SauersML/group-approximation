---
rg: 2
id: artin-ghost-ideals-reduce-to-four-lanner-trees
kind: claim
title: "Top-degree K(π,1): the Artin complex of every Artin group with infinite Coxeter group has zero top homology iff this holds for the four compact hyperbolic 4-simplex trees [5,3,3,3], [4,3,3,5], [5,3,3,5], [5,3,3^{1,1}]"
distinct_from:
  artin-ghost-ideal-localizes-to-standard-parabolics: that is the coset-slicing theorem for one group and one parabolic subgroup; this applies it with the classification of minimal non-spherical Coxeter groups and the known K(π,1) theorems to reduce a statement about all Artin groups to four groups.
  compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1: that is the full K(π,1) conjecture for the four trees (all homotopy groups of their Artin complexes); this is only the top homology group, but for every Artin group at once.
  deligne-connectivity-iff-artin-complex-connectivity: that transfers connectivity between Deligne and Artin complexes degree by degree; this reduces the top degree across diagrams, which has no analogue in lower degrees.
---

For an Artin group `A = A_Λ` on a finite set `S` let `G(A) = ⋂_{s ∈ S} ZA·(1 − s)`, the top
homology `H_{|S|−1}(Δ(A); Z)` of the Artin complex
(`artin-complex-top-homology-is-intersection-of-ideals`). Call `M ⊆ S` **minimal
non-spherical** if `W_M` is infinite and `W_T` is finite for every `T ⊊ M`.

**Theorem.**

1. Let `Λ` be a Coxeter diagram with `W_Λ` infinite. If some minimal non-spherical `M ⊆ S` is
   not one of the four diagrams `[5,3,3,3]`, `[4,3,3,5]`, `[5,3,3,5]`, `[5,3,3^{1,1}]`, then
   `G(A_Λ) = 0`.
2. Hence the following are equivalent:
   - (a) `H_{|S|−1}(Δ(A_Λ); Z) = 0` for every Coxeter diagram `Λ` with `W_Λ` infinite;
   - (b) the same holds for the four diagrams above, where `|S| = 5` and it is `H_4`.

So a ghost, meaning a nonzero finitely supported `x: A → Z` whose sums along all cosets
`g⟨s⟩` vanish, can exist in an Artin group with infinite Coxeter group only if every minimal
non-spherical subdiagram of its diagram is one of the four trees (for example `Λ` one of
them, or one of them joined by edges labelled 2 to a spherical diagram).

**Relation to the flagship.** Statement (a) is exactly what the K(π,1) conjecture
(`artin-group-k-pi-1-conjecture`) says about the top degree of the Artin complex (via
`deligne-connectivity-iff-artin-complex-connectivity`). It holds unconditionally in the
cases of item 1. What remains of it is `H_4` of the Artin complexes of four groups. For the
paths `[4,3,3,5]` and `[5,3,3,5]` it would follow from
`h4-deligne-complex-upward-flag-toward-5-edge` through the (unreviewed) route
`artin-complexes-4335-5335-contractible-via-haettel-criterion`.

Proof route: `artin-ghost-ideals-reduce-to-four-lanner-trees-proof`.

## Attempts

- **Why the argument stops at top degree** (sw-043, 2026-09-17). A top chain of `Δ(A)`
  restricts to each coset `gA_T` separately, because every codimension-one face of type `s`
  with `s ∈ T` lies over a single coset of `A_T`. A lower-degree cycle crosses cosets of
  every proper parabolic subgroup, so no such slicing exists. This is why the same method
  does not reduce the K(π,1) conjecture itself to minimal non-spherical diagrams.
- **Inside the four trees the slicing gives only a common-multiple condition.** For `Λ` one
  of the trees and `x ∈ G(A)`, item 1 of `artin-ghost-ideal-localizes-to-standard-parabolics`
  gives `x ∈ ⊕_r r·G(A_{S−u})` for each of the five spherical maximal parabolic subgroups
  `A_{S−u}`, and these ghost ideals are nonzero: they contain
  `x_T = Σ_{w ∈ W_T} (−1)^{ℓ(w)} σ(w)`, with `σ(w)` the positive lift. If each `G(A_T)` is the
  principal left ideal `ZA_T·x_T` (clear in rank one, not proved here in higher rank), a ghost is a nonzero common left multiple of the five elements `x_{S−u}` in `ZA`, a
  failure of a left Ore condition among them.
