---
rg: 2
id: regular-rank-two-isotropy-blocks-spatial-realization-proof
kind: route
title: Transport the regular Z^2 isotropy through the realization, read off an injective lag homomorphism into Z^n, pick a nonzero lag with a zero coordinate, and watch it fix a coordinate slice
target: regular-rank-two-isotropy-blocks-spatial-realization-in-g2n
requires: []
---

Notation is that of the target claim. Fix a spatial realization `ι : G -> G_2^n`, the
point `x`, and the group `A ≅ Z²` of the hypothesis. Put `p = ι(x)` and
`U* = ι(X)`, which is compact open in `C^n`.

## Step 0. Facts about `G_2^n`

**(F1)** An arrow `(z, k, y)` is determined by `z`, `k` and `y`, so `(p, 0, p)` is the
unit at `p`. The unit space is open, because `G_2^n` is étale.

**(F2)** The sets `Z(u,v)` are open bisections and form a base. So every arrow has a
neighbourhood basis of sets `Z(u,v)`.

**(F3)** On `Z(u,v)` the partial map is `α(v t) = u t`, defined on the brick `[v]`.
Coordinatewise it is `v_i t_i -> u_i t_i`.

## Step 1. The Lemma (zero lag coordinate means a slice of fixed points)

Let `(p, k, p) ∈ Z(u,v)` with `k_j = 0`.

- Then `p ∈ [v]` and `α(p) = p`. So for each `i`, both `u_i` and `v_i` are prefixes
  of `p_i`.
- For `i = j`, `|u_j| = |v_j|` because `k_j = 0`. Two prefixes of `p_j` of equal
  length are equal, so `u_j = v_j`, and `α` is the identity in coordinate `j`.
- Let `y ∈ [v]` have `y_i = p_i` for all `i ≠ j`. For `i ≠ j`, coordinate `i` of `α(y)`
  equals coordinate `i` of `α(p) = p`, since `α` acts on each coordinate separately
  (F3). Coordinate `j` is unchanged. So `α(y) = y`.
- The set `F = {y : y_i = p_i (i ≠ j), y_j ∈ [v_j]}` is homeomorphic to the cylinder
  `[v_j] ⊆ C`. This is a Cantor set containing `p`, so `p` is not isolated in
  `Fix(α)`.
- The same holds for every smaller basic bisection through `(p,k,p)`, so `(p,k,p)` is
  not regular at `p`.

## Step 2. Transport of bisections

Let `a ∈ A`, and let `S` be a compact open bisection of `G` containing `a`.

- `ι(a) ∈ G_2^n` has range and source `p`, so `ι(a) = (p, k(a), p)`, where
  `k(a) = c(ι(a)) ∈ Z^n`.
- Pick a basic bisection `Z(u,v) ∋ ι(a)` (F2). By continuity of `ι`, there is an open
  bisection `S_a ⊆ S` with `a ∈ S_a` and `ι(S_a) ⊆ Z(u,v)`.
- For `g ∈ S_a`, `ι(g)` is the unique arrow of `Z(u,v)` with source `ι(s(g))`, and it
  has range `ι(r(g))`. So on `W_a := s(S_a)`, an open neighbourhood of `x`,

  `ι(α_{S_a}(y)) = α_{Z(u,v)}(ι(y))`.   (∗)

- Since `ι` is injective on units, (∗) gives `ι(Fix(α_{S_a}) ∩ W_a) = Fix(α_{Z(u,v)}) ∩ ι(W_a)`.
- `ι(W_a)` is open in `C^n`: `ι|_X` is a homeomorphism onto the open set `U*`.
  Also `ι(W_a) ⊆ [v]`, because `ι(s(g)) = s(ι(g)) ∈ s(Z(u,v)) = [v]`.

## Step 3. The lag map `k : A -> Z^n` is an injective homomorphism

- *Homomorphism.* `ι` is a groupoid homomorphism and `c` is a cocycle, so
  `k(ab) = c(ι(a)ι(b)) = k(a) + k(b)`.
- *Injective.* Suppose `a ∈ A` with `k(a) = 0`. Then `ι(a) = (p,0,p)` is the unit at `p`
  (F1). Take `Z(u,v)` in Step 2 inside the open unit space, so `α_{Z(u,v)}` is the
  identity. By (∗), `ι(α_{S_a}(y)) = ι(y)` for `y ∈ W_a`, so `α_{S_a} = id` on `W_a`.
  Then `x` lies in the interior of `Fix(α_{S_a})`, so `a` is not regular at `x`. By
  hypothesis `a` is the unit `x`, which is the identity of `A`.

So `k(A) ≤ Z^n` is free abelian of rank 2. In particular `n ≥ 2`, since `Z` contains no
`Z²`. This already settles `n = 1`.

## Step 4. A rank-two lag group has a nonzero vector with a zero coordinate

Let `L = k(A)` and `V = L ⊗ Q ⊆ Q^n`, so `dim V = 2`. The coordinate functional
`e_1^* : V -> Q` has kernel of dimension at least `2 - 1 = 1`. Pick `0 ≠ w ∈ ker`. Since
`L` spans `V` over `Q`, some integer `m ≥ 1` has `m w ∈ L`. So there is `a ∈ A`,
`a ≠ x`, with `k(a)_1 = 0` and `k(a) ≠ 0`.

## Step 5. Contradiction

For this `a`, choose `S_a` and `Z(u,v)` as in Step 2.

- By Step 1 with `j = 1`, the Cantor set
  `F = {y : y_i = p_i (i ≥ 2), y_1 ∈ [v_1]}` is contained in `Fix(α_{Z(u,v)})` and
  contains `p`.
- `ι(W_a)` is an open neighbourhood of `p`, so `F ∩ ι(W_a)` contains points of `F`
  other than `p` arbitrarily close to `p`.
- By Step 2, `ι^{-1}(F ∩ ι(W_a)) ⊆ Fix(α_{S_a})`, and `ι^{-1}` is a homeomorphism near
  `p`. So `x` is not isolated in `Fix(α_{S_a})`.

This contradicts regularity of `a` at `x`. Hence no spatial realization exists, for any
`n`. ∎

## Corollary (actions)

- `Γ ⋉ X` is an ample groupoid with the discrete topology on `Γ`. The isotropy at `x`
  is `Stab_Γ(x)`.
- The bisection `{γ} × W` induces `α = γ|_W`. So `(a, x)` is regular at `x` iff `x` is
  isolated in `Fix(a)`.
- Given `ρ` and `ι` as in the Corollary, put `ι(γ, y) = [ρ(γ), ι(y)]`, the germ arrow of
  the brick map `ρ(γ)` at `ι(y)`. Each element of `nV` is locally the partial map of
  some `Z(u,v)`, and nearby points use the same `Z(u,v)`. So this is a continuous
  groupoid homomorphism `Γ ⋉ X -> G_2^n`, and it is a homeomorphism of `X` onto the
  clopen set `ι(X)`.
- The Theorem then applies.

## Applications (items 1 and 2 of the target)

**Item 1 (proved).** Let `t ∈ GL_3(K)` be diagonal in a basis `e_1, e_2, e_3` with
distinct eigenvalues. A flag `(L ⊂ P)` is `t`-stable iff `L` and `P` are `t`-invariant.
The `t`-invariant subspaces are exactly the spans of subsets of `{e_i}`, because the
eigenspaces are the lines `K e_i`. So the fixed flags are the `3! = 6` coordinate flags.
This is a finite set, so each of them is isolated in the Hausdorff space `Ω`. `Ω` is
compact, totally disconnected and perfect, hence a Cantor space. Applying the
Corollary to the coordinate flag `ω` of `A`'s torus proves item 1. A projective element
has a repeated eigenvalue for one lift iff it has one for every lift, so the condition
is well defined in `PGL_3`.

**Item 2 (a remark, not established here).** Two inputs are needed.

- *Distinct eigenvalues.* For `γ ∈ D^×` not central, `E[γ]` is a subfield of `D` of
  degree dividing 3 and greater than 1, so of degree 3. The minimal polynomial of `γ`
  over `E` is therefore irreducible of degree 3, and separable in characteristic 0. So
  the eigenvalues of `γ` in `M_3(K)` are distinct.
- *A rank-two regular flat.* The needed input is an `F`-torus of `SU(D, τ)` that is
  `K`-split, together with the S-unit theorem for tori, which gives it rank 2 in `Γ`.
  This is standard (Prasad–Raghunathan; Platonov–Rapinchuk, *Algebraic Groups and
  Number Theory*, Thm 5.12 and §7.1), but it is *not* cited verbatim here. Item 2 is
  therefore an unestablished remark, and nothing downstream may use it as ESTABLISHED.
