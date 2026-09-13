---
rg: 2
id: thompson-f-two-transitive-actions-satisfy-grid-condition-proof
kind: route
title: Rule out a regular [F,F] by support components, then apply Le Boudec–Matte Bon Proposition 5.1
target: thompson-f-two-transitive-actions-satisfy-grid-condition
requires:
  - thompson-f-two-transitive-actions-are-faithful
  - thompson-f-transitivity-degree-at-most-two
---

The action is faithful by `thompson-f-two-transitive-actions-are-faithful`.
Identify `(0,1)` with `R`. `F` has no global fixed point there, and its
compactly supported elements form `F^0 = [F,F] ≠ 1`. So Proposition 5.1 of
`thompson-f-transitivity-degree-at-most-two` applies.

1. Suppose `N = [F,F]` were regular on `Ω`. Fix `ω` and let `N → Ω`,
   `n ↦ nω`, which is a bijection. For `h ∈ F_ω` and `n ∈ N`,
   `hnh^{-1}ω = hnω`. So the bijection carries conjugation by `F_ω` on
   `N \ {1}` to the action of `F_ω` on `Ω \ {ω}`, and 2-transitivity makes
   `F_ω` transitive on `N \ {1}` by conjugation. Every nontrivial element of
   `N` would then be conjugate in `F`. But the number of connected components
   of the open support `{t : f(t) ≠ t}` is a conjugacy invariant in
   `Homeo^+(0,1)`, and `N` contains elements with one component and with two
   (take two elements of `N` with disjoint supports and one component each).
   Contradiction.
2. By Proposition 5.1, case (2) holds: `|O^- ∩ O^+| ≤ 1` for all orbits `O^-`
   of `F_x^-` and `O^+` of `F_x^+`.
3. `F_x^-` and `F_x^+` commute, so `abω = baω`, and the map is well defined
   and onto the `F_x`-orbit of `ω`. For injectivity, suppose `abω = a'b'ω`.
   The point lies in the `F_x^-`-orbits `bO^-` and `b'O^-`, where `O^-` is the
   orbit of `ω`. Distinct orbits are disjoint, so `bO^- = b'O^-`. This orbit
   contains both `bω` and `b'ω`, and both lie in the `F_x^+`-orbit of `ω`, so
   `bω = b'ω` by step 2. Symmetrically, `aω = a'ω`.
