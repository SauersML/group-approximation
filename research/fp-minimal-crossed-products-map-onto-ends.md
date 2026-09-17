---
rg: 2
id: fp-minimal-crossed-products-map-onto-ends
kind: claim
title: A finitely presented crossed product of an infinite minimal subshift over a multi-ended group comes with an equivariant continuous surjection onto the space of ends, and ball patterns determine everything away from that end
distinct_from:
  fp-crossed-products-force-connected-differences: that is the coarse connectivity theorem over any group; this is its consequence for groups with more than one end, a dynamical factor map that the one-ended case cannot see.
  boundary-crossed-product-is-a-leavitt-path-algebra: that exhibits one finitely presented simple host over F_d whose space is the boundary; this proves that every minimal finitely presented host over a multi-ended group factors onto the end space.
  free-group-cantor-crossed-products-are-not-universal-hosts: that kills free acting groups by word-problem complexity of tree SFT languages; this is a structural constraint over every multi-ended group, with a linear pattern bound over free groups as a by-product.
---

**ESTABLISHED (unreviewed).** Let `P` be a finitely generated group with more than one end, `k` a
field, and `X ⊆ A^P` an infinite minimal subshift with `LC(X, k) ⋊ P` finitely presented. Let `r`
be an SFT radius of `X` (`fp-crossed-products-force-sft-over-any-group`). Let `D` be a constant from
part 1 of `fp-crossed-products-force-connected-differences`, so every difference set is
`2D`-connected. Call a pattern `p ∈ L_(B_R(c))(X)` *undetermined on* `C ⊆ P` if two points of
`X` extending `p` differ somewhere in `C`.

1. **One free direction.** Let `ρ >= 0`. Let `R` be at least `ρ + D + r + 1`, and large enough that
   `B_R(c)` contains every finite component of `P \ B_ρ(c)`. Then every `p ∈ L_(B_R(c))(X)` is
   undetermined on exactly one component of `P \ B_ρ(c)`, and that component is infinite. So `p`
   determines its extensions on all other components.
2. **The compass map.** These components are nested as `ρ -> ∞`, for any choice of centres. They define
   a map `ξ : X -> Ends(P)` that is continuous and `P`-equivariant.
3. **Surjectivity.** The image of `ξ` is a nonempty closed invariant subset of `Ends(P)`. When the
   action of `P` on `Ends(P)` is minimal, for example when `P` has infinitely many ends and
   Freudenthal–Hopf applies (recalled, not re-read), `ξ` is onto.
4. **Free groups: linear pattern counts.** For `P = F_d` with `d >= 2`,
   `|L_(B_N)(X)| <= |S_(N + 1)| · |L_(B_R)(X)|` for `R = D + r + 1`. So the pattern count is at most
   linear in `|B_N|`.
   - This is the rate of `∂F_d` itself.
   - It is far below the `exp(c|B_N|)` of positive-entropy shifts.

**Why it matters.** Torsion-free groups with more than one end are nontrivial free products or
`Z` (Stallings; recalled). So for `decidable-group-algebras-have-fp-cantor-crossed-hosts`, every host
over a multi-ended torsion-free `P = Q_1 * Q_2` is an extension of the end action. It is
deterministic toward all ends but one, and the undetermined end moves continuously with the point.

Over a free product with one-ended factors, a vertex end (a coset `gQ_i`) cannot be separated from
the balls it meets. So part 4 does not extend, and no complexity kill follows there. The remaining
freedom lives inside the one-ended sheets.

For two-ended `P` the hypotheses are never met: part 3 of
`fp-crossed-products-force-connected-differences` excludes infinite minimal hosts there. So the
content is for groups with infinitely many ends.

Route: `fp-minimal-crossed-products-map-onto-ends-proof`.
