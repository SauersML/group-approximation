---
rg: 2
id: regular-rank-two-isotropy-blocks-spatial-realization-in-g2n
kind: claim
title: An ample groupoid with a rank-two isotropy group all of whose nontrivial arrows have an isolated fixed point has no spatial realization in any Cuntz product groupoid G_2^n, because a rank-two lag group always contains a nonzero vector with a zero coordinate and such a lag fixes a coordinate slice
distinct_from:
  nv-point-germ-groups-embed-in-zn-by-slope: that shows point germ groups of nV embed in Z^n by slope and separates nV from actions with non-abelian point germs; this uses the finer fact that a slope vector with a zero coordinate fixes a whole coordinate slice, which separates G_2^n from groupoids whose point germs are abelian of rank two but regular, where the slope theorem says nothing.
  spatial-two-graph-realizations-in-g2n-leave-the-degree-plane: that pins letter-count cocycles by a Bernoulli measure argument and needs rho(M_1) > 1 and cocycle rigidity to conclude; this is a pointwise isotropy argument that uses no measure, no cocycle rigidity and no entropy hypothesis.
  robertson-steger-tile-groupoids-have-no-spatial-realization: that is the statement for the 2-graph groupoids of triangle presentations, whose isotropy can contain singular arrows with Cantor fixed sets; this is an abstract criterion whose hypothesis must be checked separately in each case.
---

**ESTABLISHED** through `regular-rank-two-isotropy-blocks-spatial-realization-proof`
(unreviewed, `requires: []`).

## Setting

- `G` is a Hausdorff étale groupoid whose unit space `X` is totally disconnected, with
  range and source maps `r, s`.
- For `x ∈ X`, the isotropy group is `G_x^x = {g : r(g) = s(g) = x}`.
- For an open bisection `S`, write `α_S : s(S) -> r(S)`, `s(g) -> r(g)`.
- For `g ∈ G_x^x`, the **fixed-point germ** of `g` is the germ at `x` of `Fix(α_S)`, for
  any open bisection `S ∋ g`. This does not depend on `S`: two such bisections contain
  the open bisection `S ∩ S' ∋ g`, so `α_S = α_{S'}` on the open neighbourhood
  `s(S ∩ S')` of `x`.
- `g` is **regular at `x`** when `x` is an isolated point of `Fix(α_S)`.
- `G_2^n` is the Cuntz product groupoid on `C^n`, with `C = {0,1}^N`. Its arrows are
  `(z, k, y)`, where for each `i` one can write `z_i = u_i t_i` and `y_i = v_i t_i` with
  `k_i = |u_i| - |v_i|`. The lag cocycle is `c(z,k,y) = k ∈ Z^n`, and the basic compact
  open bisections are
  `Z(u,v) = {(u t, |u|-|v|, v t)}` for multiwords `u = (u_1..u_n)`, `v = (v_1..v_n)`.
- A **spatial realization** is a continuous groupoid homomorphism `ι : G -> G_2^n` that
  restricts to a homeomorphism of `X` onto a compact open subset of `C^n`. Injectivity
  off the unit space is *not* assumed. This is the notion used in
  `spatial-two-graph-realizations-in-g2n-leave-the-degree-plane`.

## Statement

**Theorem.** Suppose some `x ∈ X` and some subgroup `A ≤ G_x^x` with `A ≅ Z²` are such
that every `a ∈ A \ {x}` is regular at `x`. Then for no `n ≥ 1` does `G` have a spatial
realization in `G_2^n`.

**Corollary (actions).** Let a group `Γ` act on a Cantor space `X`. Suppose `x ∈ X` and
`A ≤ Stab_Γ(x)` with `A ≅ Z²` are such that `x` is an isolated point of `Fix(a)` for
every `a ∈ A \ {1}`. Then there is no `n`, homomorphism `ρ : Γ -> nV`, and
`Γ`-equivariant homeomorphism `ι` of `X` onto a clopen, `ρ(Γ)`-invariant subset of
`C^n`. More generally, `Γ ⋉ X` has no spatial realization in any `G_2^n`.

**Lemma (the step where every candidate dies).** Let `p ∈ C^n`, let `(p, k, p)` be an
isotropy arrow of `G_2^n`, and suppose `k_j = 0` for some `j`. Then every open
bisection through `(p, k, p)` fixes, near `p`, the Cantor set
`{y : y_i = p_i for i ≠ j, y_j ∈ [v_j]}` for some prefix `v_j` of `p_j`. So `(p,k,p)`
is not regular at `p`.

## Worked applications

These are stated as implications. The existence inputs are cited in the proof route
and are not claimed as established here.

1. **Regular periodic flats of Ã2 lattices.** Let `K` be a nonarchimedean local field,
   `Γ ≤ PGL_3(K)`, and `Ω` the Cantor space of full flags in `K³`. Suppose `Γ` contains
   `A ≅ Z²` inside a `K`-split maximal torus such that no nontrivial element of `A`
   has a lift with a repeated eigenvalue. Then any `a ∈ A \ {1}` fixes exactly the six
   coordinate flags of the torus. So the coordinate flag `ω` satisfies the hypothesis,
   and `Γ ↷ Ω`, like `Γ ⋉ Ω`, has no spatial realization in any `G_2^n`.
2. **Division-algebra lattices.** If `Γ` is an arithmetic lattice of `SU(D, τ)`, with
   `D` a central division algebra of degree 3 over a CM field and `τ` of the second
   kind, then every nontrivial element has three distinct eigenvalues. When `Γ` also
   meets a `K`-split maximal torus in rank two, item 1 applies. That rank-two
   intersection comes from the S-unit theorem for tori.
3. **The condition is sharp in the right place.** In `G_2^n` itself the isotropy at a
   periodic point is `Z^n`, and the arrows with a zero lag coordinate have Cantor
   fixed sets. The product 2-graph groupoid `G_2^2` therefore fails the hypothesis, as
   it must.
