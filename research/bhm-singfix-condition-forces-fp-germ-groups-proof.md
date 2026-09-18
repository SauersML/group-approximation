---
rg: 2
id: bhm-singfix-condition-forces-fp-germ-groups-proof
kind: route
title: The germ map on a one-point SingFix group is onto with kernel the simple neighbourhood-trivial subgroup of V
target: bhm-singfix-condition-forces-fp-germ-groups
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Notation as in the target. The three conditions defining a finite germ extension are
those of `germ-complex-and-bux-gonzalez-morse-inputs`, (FGE):
(1) every element has finitely many singular points; (2) `V` is exactly the set of
elements of `G` without singular points; (3) for `g ∈ G` and `q ∈ sing(g)` there is
`h ∈ G` with `sing(h) = {q}` agreeing with `g` near `q`.

**Step 1: a homomorphism.** Elements of `S_p` fix `p`, so `(gh)_p = (g)_p (h)_p` for
`g, h ∈ S_p`, and `g ↦ (g)_p` is a homomorphism `S_p -> (G)_p`.

**Step 2: onto.** Let `g ∈ Stab_G(p)`.
- If `p ∈ sing(g)`, condition (3) gives `h ∈ G` with `sing(h) = {p}` and `h = g` on a
  neighbourhood of `p`. Then `h(p) = g(p) = p`, so `h ∈ S_p` and `(h)_p = (g)_p`.
- If `p ∉ sing(g)`, then `g` agrees near `p` with some `v ∈ V`. So `v(p) = p`, and
  `sing(v) = ∅` gives `v ∈ S_p` with `(v)_p = (g)_p`.

**Step 3: the kernel.**
- Let `g ∈ S_p` with trivial germ at `p`, i.e. `g` is the identity near `p`. It agrees
  with `1 ∈ V` near `p`, so `p ∉ sing(g)`. With `sing(g) ⊆ {p}` this gives
  `sing(g) = ∅`, and condition (2) puts `g` in `V`. So `g ∈ K_p`.
- Conversely `K_p ⊆ V ⊆ G`, its elements have no singular points and fix `p`, so
  `K_p ⊆ S_p`, with trivial germs at `p`.

**Step 4: `K_p` is a nontrivial simple group.**
- For a nonempty proper clopen `U ⊆ C`, let `V[U]` be the elements of `V` supported in
  `U`. `U` is a disjoint union of `r >= 1` cones. Restriction to `U` identifies `V[U]`
  with the group of homeomorphisms of `U` that are locally prefix replacements: an
  element of that group, extended by the identity off `U`, is locally a prefix
  replacement everywhere, hence lies in `V` by compactness. So `V[U] ≅ V_{2,r}`, and
  `V_{2,r} ≅ V_{2,1} = V` is simple (Higman).
- Let `𝒲` be the set of proper clopen neighbourhoods of `p`. It is directed by reverse
  inclusion, since the intersection of two contains a cone around `p`.
- If `v ∈ K_p`, then `v` is the identity on some open neighbourhood of `p`, hence on a
  cone `W ∈ 𝒲` around `p`. Then `v(W) = W`, so `v` preserves `C − W` and lies in
  `V[C − W]`. Conversely every `V[C − W]`, `W ∈ 𝒲`, lies in `K_p`.
- So `K_p = ⋃_{W ∈ 𝒲} V[C − W]` is a directed union of simple groups, hence simple. It
  is nontrivial, because `V[C − W] ≠ 1`.

**Step 5: items 2 and 3.**
- `K_p` is normal in `S_p` as a kernel. For `1 ≠ k ∈ K_p`, the normal closure of `k` in
  `K_p` is `K_p` by simplicity. It is contained in the normal closure `⟨⟨k⟩⟩` of `k` in
  `S_p`, which is contained in `K_p`. So `⟨⟨k⟩⟩ = K_p`, and
  `(G)_p ≅ S_p / K_p = S_p / ⟨⟨k⟩⟩` by Steps 2 and 3.
- A quotient of a finitely generated group is finitely generated. Adding the one
  relator `k` to a finite presentation of `S_p` presents `S_p / ⟨⟨k⟩⟩`.

**Consequence for Theorem 2.1.** For `p ∈ sing(G)` and `n >= 1`, the pair
`({p},{p})` satisfies `|M'| = 1 <= n`, so hypothesis (2) of the theorem includes that
`S_p` has type `F_n`. Types `F_1` and `F_2` are finite generation and finite
presentation.
