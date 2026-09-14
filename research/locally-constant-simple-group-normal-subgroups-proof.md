---
rg: 2
id: locally-constant-simple-group-normal-subgroups-proof
kind: route
title: A commutator with a bump function puts every local copy of Q inside a normal subgroup
target: locally-constant-simple-group-normal-subgroups-are-open-sets
requires: []
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

Direct proof (artifact §2).

**Local copies.** Let `N` be normal and `f ∈ N`. Let `V ⊆ supp f` be clopen with `f ≡ x ≠ 1` on `V`.
- For `y ∈ Q`, let `g_y` equal `y` on `V` and `1` elsewhere. Then `[f, g_y] ∈ N` equals `[x,y]` on `V` and `1`
  elsewhere.
- The subgroup `⟨[x,Q]⟩` is normal in `Q` and nontrivial, because `Z(Q) = 1`, so it equals `Q`.
- So `N` contains every function that is constant on `V` and trivial elsewhere. Since `V` is compact and products of
  such functions over clopen pieces give all of `N_V`, `N_V ≤ N`.
- Covering `supp f` by such pieces gives `N_(supp f) ≤ N`.

**The open set.** Put `O = ⋃{V clopen : N_V ≤ N}`.
- Every `f ∈ N` has `supp f ⊆ O`.
- Every `f ∈ N_O` has compact clopen support covered by finitely many `V` with `N_V ≤ N`, and splits into a product
  of pieces supported on disjoint clopen refinements.
- So `N = N_O`. Uniqueness: `N_O ≤ N_(O')` iff `O ⊆ O'`, tested on functions supported in small clopen subsets of
  `O ∖ O'`.

**Points and topology.** Inclusion of normal subgroups is inclusion of open sets. So the maximal proper normal subgroups
correspond to the maximal proper open sets `Z∖{z}`. The basic hull–kernel set `{N_(Z∖{z}) : N_O ⊄ N_(Z∖{z})}` is
`{z : z ∈ O}`. An isomorphism preserves normality and inclusion, so it induces a homeomorphism of these spaces with
`α(N_O) = N_(h(O))`.
