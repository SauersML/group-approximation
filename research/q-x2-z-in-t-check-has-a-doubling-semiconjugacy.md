---
rg: 2
id: q-x2-z-in-t-check-has-a-doubling-semiconjugacy
kind: claim
title: Every copy of Q x|_2 Z in T-check = <T-bar, x -> 2x> is semiconjugate to the affine one, never by a PL map, and never with doubling element conjugate to x -> 2x
distinct_from:
  pl-quasi-similarity-groups-scale-rational-lines-by-ratio: that shows an element normalizing a copy of (Q,+) scales it by its own ratio, which leaves Q x|_2 Z <= T-check open; this is the finer structure theorem for that remaining case.
  fg-pl-quasi-similarity-groups-contain-no-gl-2-q: that excludes Aff(Q), B_2(Q), SL_n(Q), GL_n(Q) from these hosts; this studies the one stepping stone Q x|_2 Z <= Aff(Q) that it leaves open.
  lifts-add-no-unipotent-divisibility: that excludes central and covering lifts of Q-free groups; T-check contains (Q,+) and is not such a lift.
  t-check-contains-q-rtimes-2-z: that is the open question whether a copy exists at all; this constrains every copy.
---

**ESTABLISHED** through `q-x2-z-in-t-check-has-a-doubling-semiconjugacy-proof`.
Not independently reviewed. No priority is claimed.

## Setting

- `τ_L(x) = x + L`, `δ(x) = 2x`. `T-bar` is the group of lifts to `R` of Thompson's
  circle group `T`: the PL homeomorphisms of `R` with dyadic breakpoints, slopes in
  `2^Z`, preserving `Z[1/2]` and commuting with `τ_1`.
- `T-check = <T-bar, δ>`. Conjugation by `δ^-1` maps `T-bar` into itself, so
  `T-check` is an ascending HNN extension of `T-bar` and is finitely presented
  (`pl-quasi-similarity-groups-scale-rational-lines-by-ratio`, Examples).
- `T-bar_∞ = ⋃_{k>=0} δ^k T-bar δ^-k` is the set of elements of `T-check` that commute
  with some `τ_(2^k)`. It is normal, `T-check = T-bar_∞ x| <δ>`, and
  `χ : T-check -> Z`, `g δ^j ↦ j`, is a homomorphism with kernel `T-bar_∞`.
- `D_2 = Q x|_2 Z = <Q, t | t q t^-1 = 2q>`. It is a subgroup of
  `Aff(Q) <= GL_2(Q)`, and every host of `GL_2(Q)` must contain it.

## Statement

Let `D <= T-check` be a subgroup isomorphic to `(Q,+)` and let `t in T-check`
satisfy `t q t^-1 = q^2` for all `q in D`. Then:

1. **Where they live.** `D <= T-bar_∞`, and `D` acts freely on `R`. The translation
   number `ρ` restricts to an isomorphism `D -> Q`. And `χ(t) = 1`, so `t = g δ`
   with `g in T-bar_∞`.
2. **Doubling semiconjugacy.** After conjugating the pair `(D, t)` by a power of `δ`,
   we may take `g in T-bar`. Then `h = lim_{m -> ∞} δ^-m t^m` exists uniformly. It
   is a continuous, non-decreasing surjection `R -> R` with `sup |h - id| < ∞`, and
   ```
   h ∘ τ_1 = τ_1 ∘ h,   h ∘ t = δ ∘ h,   h ∘ q = τ_(ρ(q)) ∘ h   (q in D).
   ```
3. **Not the linear doubling.** `t` is not conjugate in `T-check` to `δ`. In
   particular there is no `D` normalized by `δ` itself with `δ q δ^-1 = q^2`.
4. **Nowhere affine.** `h(Z[1/2]) + Q ⊆ h(Z[1/2])`, and `h` is affine with positive
   slope on no nonempty open interval. So `h` is not piecewise linear on any interval.
5. **Circle reformulation (minimal case).** If `h` is injective, then `t` is the lift of
   a PL-dyadic degree-2 circle map `u` with `u(θ + 1/2) = u(θ)`. PL-dyadic means dyadic
   breakpoints, slopes in `2^Z`, and dyadic points mapped to dyadic points. The map `η` induced by `h`
   conjugates `u` to the doubling map `D(θ) = 2θ`, with `η^-1 R_s η in T` for all
   `s in Q/Z` (`R_s` is rotation by `s`). Conversely, such a pair `(u, η)` gives
   `D_2 <= T-check`.

## Consequence

`Q x|_2 Z <= T-check` holds only through a singular, nowhere-affine doubling
semiconjugacy. The doubling element can be neither the linear map `δ` nor any
conjugate of it. What is left open is recorded in `t-check-contains-q-rtimes-2-z`.
