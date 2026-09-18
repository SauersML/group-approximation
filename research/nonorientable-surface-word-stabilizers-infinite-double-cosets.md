---
rg: 2
id: nonorientable-surface-word-stabilizers-infinite-double-cosets
kind: claim
title: For every n at least three, the stabilizer in Out(F_n) of the one-cusp nonorientable surface word a_1^2...a_n^2 has infinitely many double cosets, and so does every surface peripheral-structure stabilizer
requires:
  - surface-word-stabilizers-have-infinitely-many-double-cosets
  - out-free-pair-finite-stabilizers-contain-fully-irreducibles
distinct_from:
  surface-word-stabilizers-have-infinitely-many-double-cosets: that treats the orientable one-cusp word in even rank n = 2g ≥ 4; this treats the nonorientable one-cusp word in every rank n ≥ 3, including odd rank, and adds the multi-boundary surfaces.
  out-free-pair-finite-stabilizers-contain-fully-irreducibles: that excludes stabilizers that virtually fix a proper free factor class; this uses it for surfaces with two or more boundary components, whose boundary classes are primitive.
---

**ESTABLISHED** (lane proof, same counting method as the orientable node; not
reviewed; no priority claimed).
- **Cited inputs, not read at source this session:**
  - Dehn–Nielsen–Baer for nonorientable punctured surfaces;
  - Mirzakhani, arXiv:1601.03342 (abstract only), used on the orientation double
    cover;
  - finiteness of the number of mapping-class orbits of closed curves with
    bounded self-intersection.

**Statement.**
1. **Nonorientable one-cusp surfaces.** Let `k = n ≥ 3`, let `N = N_{k,1}` be the
   once-punctured nonorientable surface of genus `k` with `π_1(N) = F(a_1,…,a_k)`,
   and let `w = a_1²a_2²⋯a_k²`. Then `H = Stab_{Out(F_n)}([w])` has infinitely
   many double cosets, and so does every `L` with `L ∩ H` of finite index in `L`.
2. **Every surface peripheral structure.** Let `Σ` be a compact surface with
   `π_1(Σ) ≅ F_n` (n ≥ 3), and let `P_Σ ≤ Out(F_n)` be the stabilizer of its
   finite set of boundary conjugacy classes. Then no subgroup virtually contained
   in `P_Σ` is a point stabilizer of an action with finitely many pair orbits and
   an infinite orbit. In particular none is a type (A) point stabilizer.

**Proof of 1.**
- **Exponential orbit growth.**
  - Construction: for `c` reduced in `F(a_2,…,a_k)` whose last letter is not
    `a_2⁻¹`, let `θ_c` send `a_1 ↦ a_1c` and fix every other generator.
  - The word: `θ_c(w) = a_1 c a_1 c a_2²⋯a_k²`. It is cyclically reduced: `c`
    has no `a_1^{±1}`, and the only possible cancellation, at `c·a_2`, is
    excluded by the choice of `c`. Its length is `2k + 2|c|`.
  - Injectivity: `a_1^{±1}` occurs exactly twice, both times positively. The two
    arcs between these occurrences are `c` and `c a_2²⋯a_k²`, so `c` is the
    shorter one, and `c ↦ [θ_c(w)]` is injective.
  - Count: `F(a_2,…,a_k)` has rank `r = k − 1 ≥ 2`. So there are at least
    `(2r−2)(2r−1)^{m−1} ≥ 2·3^{m−1}` classes of length `≤ 2k + 2m` in `O = G·[w]`.
- **Polynomial H-orbits.**
  - `H` consists of classes of homeomorphisms of `N` (Dehn–Nielsen–Baer). So
    each `H·u` lies in `Mod(N)·u`, all of whose curves have the same minimal
    self-intersection `K`.
  - Fix a hyperbolic metric on `N` and lift it to the orientation double cover
    `p: Ñ → N`. `Ñ` is orientable, of genus `k − 1`, with two punctures.
  - Lifts of a curve: for a closed geodesic `v`, `p⁻¹(v)` is one or two closed
    geodesics. The map `p` is a local homeomorphism, so the double points of
    `p⁻¹(v)` are exactly the `2K` preimages of the double points of `v`. So each
    component has self-intersection `≤ 2K` and length `≤ 2ℓ(v)`.
  - Count: choosing one component `ṽ` of `p⁻¹(v)` is injective in `v`, since
    `v = p(ṽ)`. The curves of self-intersection `≤ 2K` on `Ñ` fall into
    finitely many `Mod(Ñ)` types, and each type has `O(T^{6(k−1)−6+4})` members
    of length `≤ T` (Mirzakhani). With `ℓ ≤ K'‖·‖` as in the orientable node,
    `#{v ∈ H·u : ‖v‖ ≤ L}` is bounded by a polynomial in `L`.
- **Conclusion.** Finitely many `H`-orbits contradicts exponential growth of `O`.
  The statement for `L` follows exactly as in the orientable node.

**Proof of 2.**
- **One boundary component.** If orientable, then `n = 2g` and this is
  `surface-word-stabilizers-have-infinitely-many-double-cosets`. If
  nonorientable, it is item 1. In both cases `Stab([w])` has index at most 2 in
  `P_Σ`, since `P_Σ` may invert `[w]`.
- **Two or more boundary components.** Each boundary loop but one is a member of
  a free basis of `π_1(Σ)`. So the finite-index subgroup of `P_Σ` fixing each
  boundary class fixes the class of a rank-one proper free factor.
  `out-free-pair-finite-stabilizers-contain-fully-irreducibles` (item 2)
  excludes any subgroup that virtually does this.

**Scope.** This finishes the surface-type subgroups of `Out(F_n)`. It does not
touch non-geometric subgroups; see
`virtually-cyclic-out-free-subgroups-have-infinite-double-cosets` for the
virtually cyclic ones.
