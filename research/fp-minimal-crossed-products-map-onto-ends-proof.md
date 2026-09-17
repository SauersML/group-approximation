---
rg: 2
id: fp-minimal-crossed-products-map-onto-ends-proof
kind: route
title: Gluing two undetermined components gives a split difference set, and nesting the unique undetermined component defines the end
target: fp-minimal-crossed-products-map-onto-ends
requires: [fp-crossed-products-force-connected-differences, fp-crossed-products-force-sft-over-any-group]
---

Notation as in the target. Metric `d(g, h) = |g^(-1) h|`. `N(Δ)` is the set of points within
distance `2r` of `Δ`. Lemma G is the gluing lemma of
`fp-crossed-products-force-connected-differences-proof`, Section 2.

## 1. Separation

Fix a centre `c`, and radii `ρ` and `R` as in part 1. `P \ B_ρ(c)` has finitely many components,
since each meets the finite sphere `S_(ρ+1)(c)`. So `R` exists, and every point outside `B_R(c)` lies
in an infinite component.

- **(S1)** If `C ≠ C'` are components of `P \ B_ρ(c)`, then
  `d(C \ B_R(c), C' \ B_R(c)) >= 2(R - ρ) > max(2D, 2r)`. A geodesic from one to the other passes
  through `B_ρ(c)`.
- **(S2)** For a component `C`, `N(C \ B_R(c)) \ (C \ B_R(c)) ⊆ B_R(c)`. A point within `2r` of
  `C \ B_R(c)` that is outside `B_R(c)` lies in some component. By (S1) and `2r < 2(R - ρ)`, that
  component is `C`.

## 2. At most one undetermined component

Let `p ∈ L_(B_R(c))(X)`, and suppose `p` is undetermined on distinct components `C_1` and `C_2`. Fix
an extension `x ∈ X` of `p`.

- **For `i = 1, 2`, there is an extension `w_i` of `p` with `w_i ≠ x` somewhere in `C_i`.** Two
  extensions differ somewhere in `C_i`, so at least one of them differs from `x` there. All
  differences lie outside `B_R(c)`, where both agree with `p`.
- **Glue.** Apply Lemma G to `x` with `Δ_i = C_i \ B_R(c)` and `y_i = w_i`.
  - The regions are `> 2r` apart by (S1).
  - `w_i = x` on `N(Δ_i) \ Δ_i ⊆ B_R(c)`, by (S2).
- The glued configuration `z ∈ X` equals `w_i` on `Δ_i` and `x` elsewhere. So
  `Δ(x, z) = (Δ(x, w_1) ∩ Δ_1) ⊔ (Δ(x, w_2) ∩ Δ_2)`, with both parts nonempty and at distance `> 2D`
  by (S1).

This contradicts part 1 of `fp-crossed-products-force-connected-differences`.

## 3. At least one

If `p` is undetermined on no component, all extensions of `p` agree on every component and on
`B_R(c)`. So the cylinder `[p]` is a single point `{x}`, and `x` is isolated.
- By minimality, the orbit `P.x` is open with closed invariant complement, so `X = P.x`.
- `X` is then a compact space that is a union of open singletons, so it is finite. This contradicts
  `X` infinite.

The undetermined component is infinite, since differences lie outside `B_R(c)`, where only infinite
components live. This proves part 1.

## 4. Nesting and the end map

**Monotonicity.** Let `(c, ρ, R)` and `(c', ρ', R')` be admissible triples with
`B_(ρ')(c') ⊇ B_R(c)`, and let `x ∈ X`.
- Write `C'` for the undetermined component of `x|_(B_(R')(c'))` in `P \ B_(ρ')(c')`, and `C` for
  that of `x|_(B_R(c))` in `P \ B_ρ(c)`.
- `C'` is connected and misses `B_ρ(c)`, so it lies in one component `C''` of `P \ B_ρ(c)`.
- Two extensions of `x|_(B_(R')(c'))` differing in `C'` are also extensions of `x|_(B_R(c))`,
  since `B_R(c) ⊆ B_(R')(c')`. They differ in `C''`, so `C'' = C` by Section 2. So `C' ⊆ C`.

**Definition.** Take any sequence of admissible triples `(c_j, ρ_j, R_j)` with
`B_(ρ_(j+1))(c_(j+1)) ⊇ B_(R_j)(c_j)` and `ρ_j -> ∞`. The undetermined components form a decreasing
sequence of infinite components of complements of balls exhausting `P`. Such a sequence is exactly an
end. Call it `ξ(x)`.

**Independence of choices.** Two such sequences can be interleaved into a third, since balls about
any centres are eventually contained in each other. By monotonicity, the ends of both agree with the
end of the interleaved sequence.

**Continuity.** The `j`-th component depends only on `x|_(B_(R_j)(c_j))`.

**Equivariance.** `(g.x)|_(g B_R(c))` is the translate by `g` of `x|_(B_R(c))`, and `X` is invariant.
So the undetermined component of `g.x` for `(gc, ρ, R)` is `g` times that of `x` for `(c, ρ, R)`.
With independence of choices, `ξ(g.x) = g ξ(x)`. This proves part 2.

## 5. Surjectivity

`ξ(X)` is compact and invariant, hence closed. If the action on `Ends(P)` is minimal, `ξ(X)` is all of
`Ends(P)`. Minimality of that action for infinitely-ended `P` is recalled (Hopf; not re-read), and
the claim marks it so. This proves part 3.

## 6. Free groups

Let `P = F_d` with its free basis, `ρ = 0` and `R = D + r + 1`. `F_d \ {g}` has no finite
components, so every triple `(g, 0, R)` is admissible.
- For `x ∈ X`, let `g ∈ S_(N+1)` be the point at distance `N + 1` on the geodesic ray from `1` to
  `ξ(x)`.
- The undetermined component of `x|_(B_R(g))` contains the end `ξ(x)`, by Section 4. So it is the
  branch at the neighbour of `g` toward `ξ(x)`, whose points have length `>= N + 2`, and it misses
  `B_N`.
- Hence every `x' ∈ X` with `x'|_(B_R(g)) = x|_(B_R(g))` agrees with `x` on `B_N`.
- For each `π ∈ L_(B_N)(X)`, choose an extension `x_π` and its point `g_π`. Assign to `π` the pair
  `(g_π, (g_π^(-1) . x_π)|_(B_R))`. The pair determines `x_π|_(B_R(g_π))`, and hence `π`, so the
  assignment is injective.
- So `|L_(B_N)(X)| <= |S_(N+1)| · |L_(B_R)(X)|`. This proves part 4. `∎`
