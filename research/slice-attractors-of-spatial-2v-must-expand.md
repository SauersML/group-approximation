---
rg: 2
id: slice-attractors-of-spatial-2v-must-expand
kind: claim
title: In a spatial copy of Brin's 2V inside CT_P(Z) (or any piecewise-affine host of Z-hat), the image of a slice contraction must expand some prime near its attractor; otherwise the other stack's V acts on the attractor by scalings between finitely many rational centres, with polynomial orbital growth, which is impossible
requires:
  - spatial-2v-in-affine-hosts-needs-unbounded-fibres
  - two-v-in-ct-p-z-needs-degree-rank-two-r
distinct_from:
  spatial-2v-in-affine-hosts-needs-unbounded-fibres: that kills contracting push families through a fixed-point budget; this kills non-expanding slice contractions through an orbital-growth count, and so constrains every element of the image, not only the pushes.
  two-v-in-ct-p-z-needs-degree-rank-two-r: that bounds the rank of the degrees; this bounds the growth of orbits inside a fibre set, which holds even with translations (the RCWA hosts).
---

**ESTABLISHED** for items 1–2 (lane proof, elementary; not independently reviewed; no priority
claimed). **OPEN:** does `2V` embed in `CT(Z)`? Only designs whose slice contractions *expand* a
prime near their attractors survive. Kourovka 17.58 stays OPEN.

## Setting

- `H` is a piecewise-affine host on a clopen `Z ⊆ Ẑ_P`: `CT_P(Z)`, or an RCWA host such as `B` or
  `G_(2,3)`. bh-invent-02 (a2f925b55) identifies `G_(2,3)` with `R_(3)`, the full group of the
  Zappa–Szép groupoid `Λ_{3} ⋈ Z`, which is of type `F_∞`.
- `ρ : 2V → H` is spatial, with `q = (q_1, q_2) : Z → C × C`.
- Let `h ∈ V` have an attracting fixed point `p`, with a cylinder `U ∋ p` such that `h(U) ⊆ U` and
  `∩ h^n U = {p}`.
- Put `T = ρ(h × id)` and `N = q^{-1}(U × C)`. Then `T(N) ⊆ N`, and the **slice attractor** is
  `K = ∩_n T^n(N) = q^{-1}({p} × C)`.
- `ρ(1 × V)` preserves `K`, commutes with `T`, and `q_2 : K → C` is a `V`-equivariant surjection.

## Statement

1. **Attractor reduction.** Every spatial `2V` gives such a pair `(T, K)`. `K` is uncountable, `T`
   is piecewise affine with `T(N) ⊆ N`, and `V` acts faithfully on `K` by restrictions of elements
   of `H` commuting with `T`.
2. **Non-expanding attractors are impossible.** Suppose every piece of `T` meeting `K` has a
   positive integer slope, and some prime `q_0 ∈ P'` divides every such slope. Then no spatial `2V`
   exists.
   - So in every spatial `2V`, each slice contraction has a piece near its attractor whose slope is
     not an integer, i.e. a piece expanding some prime.
   - By symmetry the same holds for `id × h`.

## Proof

**Item 1** is the setting. `K` is uncountable because `q(K) = {p} × C`.

**Item 2.**
- **Shrink `N`.** The sets `T^n N` decrease to `K`, so for large `n` the set `T^n N` lies in the
  union of the pieces meeting `K`. Replace `N` by it.
- **Boundedly many boxes.** Integer slopes send boxes to boxes and never decrease moduli. Once a box
  has modulus divisible by the least common multiple `M*` of the piece moduli, it lies in one piece
  and stays that way. So every `T^n N` is a union of at most `K′` boxes, with `K′` independent of
  `n`.
- **Finitely many centres.** Each of these boxes has `q_0`-diameter at most `q_0^{-n}`. So the
  `q_0`-coordinates of points of `K` take finitely many values `a_1, …, a_k`.
- **The centres are rational.** For `z ∈ K`, write `z = T^n z_n` with `z_n ∈ K`. Some value `a′`
  recurs along the `z_n`. `T^m` maps a point over `a′` to one over `a′` by an affine map `cy + d`
  with `|c|_{q_0} < 1`, so `a′ = d/(1−c) ∈ Q`. Every `a_i` is an affine image of such an `a′` with
  rational coefficients, hence rational.
- **V acts by scalings.** A piece of `ρ(1 × v)` sends a point of `K` over `a_i` to one over `a_j`.
  So `c a_i + d = a_j` in `Z_{q_0}`, and hence in `Q`. On that piece, in every coordinate,
  `y ↦ a_j + c (y − a_i)`.
- **Polynomial orbits in K.**
  - Choose `z ∈ K` with some coordinate `w = z_{q′} − a_i` irrational and `q_2(z) ∈ C_1`. This is
    possible because `q^{-1}({p} × C_1)` is uncountable.
  - Every point of the orbit is `ρ(g)z = a_j + c(z − a_i)`. This is determined by `(j, c)`, and
    determines it, because `(c − c′) w ∈ Q` forces `c = c′`.
  - The slopes `c` reachable within word length `R` have exponent vectors bounded by `CR`. So the
    orbit ball `B_z(R)` has at most `k (2CR+1)^{|P'|}` points.
- **Exponential orbits in C.** For `r = 0, 1` let `f_r ∈ V` send `1y ↦ 1ry`, and map `C_0` onto
  `C_0 ⊔ C_{1(1−r)}` (via `00x ↦ 0x`, `01x ↦ 1(1−r)x`). For `b ∈ C_1` the points `f_w(b)` with
  `|w| = R` are `2^R` distinct points at distance `O(R)`.
- **Contradiction.** `q_2` maps `ρ(f_w) z ↦ f_w(b)`, so it maps `B_z(O(R))` onto a set of size at
  least `2^R`. That contradicts the polynomial bound. `∎`

## What survives

A surviving design needs a slice contraction `T` whose pieces near `K` include non-integer slopes,
i.e. that expand some prime. Only then can the positions of `K` form a Cantor set in every
coordinate, and the `V`-germs along `K` be genuinely affine: `y ↦ cy + d` generating a
`Z[1/m] ⋊ Z^k`-type group of exponential growth.
- This matches the full-shift dynamics of Conway's map
  (`conway-amusical-permutation-is-the-full-three-shift`), where slopes `3/2` and `3/4` expand
  `Z_2` and contract `Z_3`. The combined obstructions now all point there.
- **Next test for a construction.** Find `T` built from `[[α]]`-pieces whose attractor carries a
  faithful `V`-action by affine germs.
- **The impossibility route (bh-kourovka).** Decidable torsion in `CT(Z)`, which would exclude `2V`
  outright.

**Lesson for general BH.**
- **Growth transfer.** A factor map that is equivariant along orbits carries orbital growth forward.
  So an embedded action of an exponentially growing group like `V`, on any invariant piece, needs
  germs generating exponential growth there.
- **Consequence for affine hosts.** In piecewise-affine hosts, non-expanding dynamics collapses
  invariant pieces onto finitely many rational centres, where all germs are commuting scalings with
  polynomial growth.
- **Where structure can live.** Rich subgroup structure in such hosts (a second stack, and plausibly
  intermediate growth) can only sit where some prime is expanded, i.e. in shift-like dynamics.
