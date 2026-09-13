---
rg: 2
id: thompson-v-elements-need-unboundedly-many-non-f-letters-proof
kind: route
title: Prove that the order-break count on Thompson's group V is subadditive and unbounded
target: thompson-v-elements-need-unboundedly-many-non-f-letters
requires: []
---

Conventions: `(gh)(ζ) = g(h(ζ))`. An element `g ∈ V` is given by complete
prefix codes `u_1, …, u_m` and `v_1, …, v_m` with `g(u_i ζ) = v_i ζ`. On each
cone `u_i C`, `g` is an order isomorphism onto the cone `v_i C`, and cones are
intervals. So the cones `u_i C` form an admissible partition and `br(g) ≤ m` is
finite.

**(1)** F is the subgroup of V whose elements preserve the lexicographic order
(Cannon–Floyd–Parry), so `C` itself is an admissible one-piece partition. If
`g|I` is an order isomorphism onto the interval `g(I)`, then `g^(-1)|g(I)` is an
order isomorphism onto `I`. So the images of an admissible partition for `g`
form one for `g^(-1)`.

**(2)** Let `I_1, …, I_k` be admissible for `h` with `k = br(h)`, and let
`J_1 < ⋯ < J_l` be admissible for `g` with `l = br(g)`. There are `l − 1` cut
positions between consecutive `J_t`. Fix `j`. The set `h(I_j)` is an interval,
so the `t` with `h(I_j) ∩ J_t ≠ ∅` form a run `a_j ≤ t ≤ b_j`, and
`b_j − a_j` counts the cut positions interior to `h(I_j)`, meaning `h(I_j)`
meets `J_t` and `J_(t+1)`. The sets `h(I_j)` are disjoint intervals, so each cut
position is interior to at most one of them. Hence
`Σ_j (b_j − a_j + 1) ≤ k + l − 1`.

Now put `P_(j,t) = I_j ∩ h^(-1)(J_t)` for the nonempty cases.

- `h(I_j) ∩ J_t` is clopen and order-convex, so `P_(j,t)`, its preimage under
  the order isomorphism `h|I_j`, is an order-convex subset of `I_j`, hence of
  `C`. It is clopen because `h` is a homeomorphism.
- On `P_(j,t)`, `gh` is a composite of order-preserving maps.
- `(gh)(P_(j,t)) = g(h(I_j) ∩ J_t)` is the image of an order-convex subset of
  `J_t` under the order isomorphism `g|J_t` onto the interval `g(J_t)`, so it is
  an interval.

These at most `k + l − 1` pieces partition `C`, so `br(gh) ≤ br(g) + br(h) − 1`.
The word bound follows by induction on `L`, using (1) for letters in F.

**(3)** The cones `w_i C` of depth `k` are consecutive intervals and `r_k` maps
each onto a cone order-preservingly, so `br(r_k) ≤ 2^k`. Suppose instead that
`I_1, …, I_q` is admissible with `q < 2^k`. If every `I_p` lay inside a single
cone, each cone would be a union of pieces and `q ≥ 2^k`. So some `I_p` contains
`ζ ∈ w_i C` and `ζ' ∈ w_j C` with `i < j`, hence `ζ < ζ'`. But
`r_k(ζ) ∈ w_(2^k+1−i) C` and `r_k(ζ') ∈ w_(2^k+1−j) C`, and the second cone lies
entirely below the first, so `r_k(ζ') < r_k(ζ)`. Then `r_k` is not
order-preserving on `I_p`, a contradiction. Hence `br(r_k) = 2^k`.

**(4)** Apply (2) to a word representing `r_k`:
`2^k − 1 = br(r_k) − 1 ≤ Σ_(letters not in F) (br(s) − 1) ≤ b_S · #(letters not in F)`.

**(5)** An element of T matches `u_i` to `v_(i+r mod m)` in cyclic order, so it
is order-preserving from the union of the cones `u_1, …, u_(m−r)` onto an
interval, and from the union of the remaining cones onto an interval. Both
unions are intervals, so `br ≤ 2`.

**Model check.** A trivial model fails the conclusion: for `S ⊂ F` we get
`b_S = 0` and no word represents `r_k` for `k ≥ 1`, consistent with (3), since
`r_k ∉ F`. In T every element has `br ≤ 2`, matching Migliorini's
one-letter normal form.
