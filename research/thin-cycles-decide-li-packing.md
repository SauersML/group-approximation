---
rg: 2
id: thin-cycles-decide-li-packing
kind: claim
title: Li's merge-packing condition fails exactly when some hitting set of types carries a thin growth cycle, so packing is decidable from finite type data; power Garside families inherit one-layer thin cycles through (2_Γ), so no power of the tree coding has packing
requires:
  - perron-weights-do-not-give-li-finiteness
distinct_from:
  perron-weights-do-not-give-li-finiteness: that proves one direction (a thin cycle kills packing) and the repair theorem; this proves the converse, making packing a finite decidable test, and shows changing the Garside family cannot remove thin cycles.
  raag-cube-codings-fail-li-multiplicity-at-every-power: that shows (t<d) fails at every power for RAAG cube codings; this shows the weaker, sufficient condition (Pack) also fails at every power, already for trees, through the same (2_Γ) generators.
---

**ESTABLISHED** through `thin-cycles-decide-li-packing-proof` (lane proof; X. Li,
arXiv:2110.04505v2, §§`s:GarsCat-TFG`, `s:Fn`, read at source; not independently reviewed;
no priority claimed).

## Statement

Work in Li's setting for `thm:Fn` with trivial units (`𝔠* = 𝔠⁰`) and a finite set
`𝔛(*)` of types. The notions (Pack), hitting set and thin growth cycle are those of
`perron-weights-do-not-give-li-finiteness` (items 3 and 4).

1. **Characterization.** (Pack) fails **if and only if** there are a set `R ⊆ 𝔛(*)` and
   a cycle of generators such that:
   - every generator in `Γ` has a codomain piece of type in `R` (a hitting set);
   - each generator on the cycle has exactly one `R`-type piece in its codomain, namely
     the next domain of the cycle;
   - at least one generator on the cycle has a further piece;
   - the cycle's types occur in `𝐗(*)`.
2. **Decidability.** Given the finite data (types, generators with codomain multisets,
   and the reachable types), (Pack) is decidable. One enumerates the subsets `R` and
   searches the `R`-thin generator graph for a cycle with a growth edge.
3. **Garside families cannot remove thin cycles.** Take the raw reduced-word coding of
   `F_k` (`k ≥ 2`, the pointed-cube category of the tree) and, for any `N ≥ 1`, the power
   Garside family of paths of length `≤ N`.
   - Li's (`2_Γ`) forces the one-step expansion `γ(∅, 𝔳𝔖)` into `Γ`. It arises from any
     `c` of length `≡ −1 (mod N)`, since then the fitting set `𝔰` is exactly the set of
     single edges.
   - So the thin cycle "expand `a` one step", with `R = {a, a^{-1}}`, persists: (Pack)
     fails at every power.
   - The same happens for the raw product-of-trees 2-graph (vertices `(ℓ,m)`, the last
     letters of `F_2 × F_2`).
     - There (`2_Γ`) forces the one-colour expansions `(ℓ,m) → (ℓ,m')`
       (`m' ≠ m^{-1}`), and likewise in colour 1.
     - `R = {(ℓ,m) : ℓ ∈ {a^{±1}} or m ∈ {c^{±1}}}` hits every generator.
     - "Expand `(b,c)` in colour 2" is a thin growth cycle, since its only `R`-child is
       `(b,c)`.

   That is why Li needs Matui's recoding in `cor:ProdGraphs`: the recoding changes the
   **category**, not the Garside family.

## Consequence for BBCMP Q1.15

For a cubulated group, Li's finiteness route needs a presentation `𝔠'` of the boundary
groupoid of `C_X` such that:
- the category `𝔠'` itself (not just its Garside family) has no hitting-set thin cycle;
- `𝔠'` keeps Li's lcm and (St) hypotheses.

The raw pointed-cube coding fails already for trees and for products of trees. For
products, factorwise graph recoding repairs it (Li `cor:ProdGraphs`, item 3 bis of
`virtually-torsion-free-cubulated-groups-satisfy-boone-higman`). For general `X`, no such
presentation is known, and item 2 makes any candidate a finite check.

## Lesson for general BH

Finite presentability of a coded full group comes down to one finite graph-theoretic
test on the coding: **no rare set of piece types that every move must touch and that one
move can regenerate thinly**. Garside-family changes (powers, normal-form coarsenings)
never pass this test when the underlying category fails it, because Li's (`2_Γ`) brings
back the one-layer moves. Only a new category does, as graph recodings do for SFTs.

So the design problem for higher-rank BH hosts is a **thin-cycle-free category
presenting the right groupoid**. That is a concrete, decidable target, and the next thing
to search for on non-product cube complexes.
