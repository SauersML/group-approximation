---
rg: 2
id: countable-virtually-abelian-groups-embed-in-2v-proof
kind: route
title: Disjoint rectangles carry independent copies of 2V; fill them with Q and with the locally finite group sum of Q/Z
target: countable-virtually-abelian-groups-embed-in-2v
requires:
  - rationals-embed-in-brin-thompson-group-2v
  - brin-thompson-nv-embeds-in-mv
---

Notation as in `rationals-embed-in-brin-thompson-group-2v-proof`: `C = {0,1}^ω`,
and `2V` is the group of rectangle-to-rectangle prefix rearrangements of
`C × C`.

**Step 1: local copies.** Let `R = uC × u'C` be a rectangle and
`π_R(w, w') = (uw, u'w')`. For `f ∈ 2V` let `ι_R(f)` act as
`π_R f π_R^{-1}` on `R` and as the identity off `R`.
- If `f` is given by rectangles `u_i C × u'_i C → v_i C × v'_i C`, then
  `ι_R(f)` is given on `R` by `u u_i C × u' u'_i C → u v_i C × u' v'_i C`.
  Off `R` it is the identity on a finite rectangle partition of
  `(C × C) \ R = ((C \ uC) × C) ∪ (uC × (C \ u'C))`, since `C \ uC` is a finite
  union of cones. So `ι_R(f) ∈ 2V`.
- `ι_R` is an injective homomorphism onto the subgroup `2V_R` of elements
  supported in `R`.
- For pairwise disjoint rectangles `R_0, R_1, …`, elements of different `2V_(R_i)`
  have disjoint supports and commute. Every element of the group they generate
  is a finite product, and the supports separate the factors. So the group
  they generate is `⊕_i 2V_(R_i) ≅ ⊕_ω 2V`. Take `R_i = 1^i 0 C × C`.

**Step 2: the divisible hull.** Let `D = (⊕_ω Q) ⊕ (⊕_ω Q/Z)`.
- `Q <= 2V` by `rationals-embed-in-brin-thompson-group-2v`. Put one copy in each
  `2V_(R_i)`, `i >= 1`, through `ι_(R_i)`.
- `⊕_ω Q/Z` is countable and locally finite, so it embeds in `V`: Higman 1974,
  Theorem 6.6, as stated in survey arXiv:2306.16356v3, Theorem 4.3(3): "Any
  countable group ... that is an ascending union of finite groups". Then
  `V <= 2V` via `g -> g × id`, and put it in `2V_(R_0)`.
- So `D <= 2V`.
- Every countable abelian group embeds in `D`. It embeds in a countable
  divisible group, which is a direct sum of copies of `Q` and of quasicyclic
  groups `Z(p^∞) <= Q/Z`. See Fuchs, *Abelian Groups*, Theorems 4.1.4 and 4.3.1,
  as in the proof of survey Corollary 2.6.

**Step 3: finite extensions.** Let `G` be countable with an abelian subgroup of
finite index. Its normal core `A` is abelian, normal and of finite index, and
Krasner--Kaloujnine gives `G <= A wr F = A^F ⋊ F` with `F = G/A`.
- `H wr F <= 2V` whenever `H <= 2V` and `F` is finite. Choose a complete prefix
  code `{c_f : f ∈ F}` of size `|F|` in the first coordinate, and put
  `R_f = c_f C × C`. The group `F` acts on the rectangles by left
  multiplication. Realize this by `p_g ∈ V × id`, which maps `R_f` to `R_(gf)` by
  prefix replacement. Then `p_g ι_(R_f)(h) p_g^{-1} = ι_(R_(gf))(h)`, because
  `π_(R_(gf)) = p_g ∘ π_(R_f)` on `C × C`. So `⊕_f ι_(R_f)(H)` together with
  `{p_g}` is a copy of `H wr F`.
- `A` is countable abelian, so `A <= 2V` by Step 2. Taking `H = A` gives
  `G <= A wr F <= 2V`.

Finally, `2V <= nV` for `n >= 2` (`brin-thompson-nv-embeds-in-mv`). ∎
