---
rg: 2
id: stein-elements-with-hyperbolic-periodic-points-bound-roots
kind: claim
title: In a Stein interval-exchange group, an element with a hyperbolic periodic point has roots of only finitely many orders, so copies of Q or BS(1,m) consist of elements without hyperbolic periodic points
distinct_from:
  nv-rational-subgroups-with-power-conjugacy-are-flat: that is the Brin–Thompson nV version for periodic exponents on Cantor bricks; this is the interval-exchange (Stein group) version, via one-sided slopes at periodic points.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

G = V(1; A, Λ) is the group of right-continuous, increasing-on-pieces, piecewise-affine bijections of [0,1), with finitely
many pieces, breakpoints in A ⊆ Q and slopes in a finitely generated Λ ≤ Q_{>0}^×. A periodic point x of g
(g^k x = x) is *hyperbolic* if a one-sided slope of g^k at x is ≠ 1.

## Statement

1. If g ∈ G has a hyperbolic periodic point, then the set of n for which g has an n-th root in G is finite.
2. Hence, in any copy of Q in G, no nontrivial element has a hyperbolic periodic point.
3. In any copy of BS(1,m) = ⟨s, u | u s u^{-1} = s^m⟩ with |m| ≥ 2 in G, the element s has no hyperbolic periodic point,
   because u^{-j} s u^{j} is an m^j-th root of s.

## Proof of 1

- Fix k and let P be the set of points x with g^k x = x at which a one-sided slope of g^k is ≠ 1. On each affine piece of
  g^k that is not the identity, the equation g^k x = x has at most one solution. So P is finite. By hypothesis, P ≠ ∅ for
  some k.
- If h^n = g, then h commutes with g^k. By the chain rule for increasing affine pieces, h maps P to P and preserves
  one-sided slopes. So each x ∈ P has an h-cycle of length ℓ ≤ |P|.
- Since h^{nk}(x) = g^k(x) = x, we have ℓ | nk. Let τ be the one-sided slope of h^ℓ at x on the side where g^k has slope
  σ ≠ 1. Then σ = τ^{nk/ℓ}, with τ ∈ Λ.
- Λ ≅ Z^r is free abelian of finite rank, so σ ≠ 1 is an e-th power in Λ only for e ≤ E(σ), where E(σ) is finite (the gcd of
  σ's exponents in a basis). So n ≤ E(σ)·ℓ/k ≤ E(σ)|P|.

Items 2 and 3 follow directly.

## Calibration and open point

- **V calibration.** For V (A = Z[1/2], Λ = ⟨2⟩), every infinite-order element has an attracting periodic point
  (revealing pairs; Brin, recalled, not re-read). So 1 recovers that V has no nontrivial infinitely divisible elements,
  consistent with Q ⊄ V.
- **Open.** The analogous attractor statement for general Stein groups: *every infinite-order element of V(1; Z[1/M],
  ⟨p|M⟩) has a hyperbolic periodic point*. If it holds, item 2 gives Q ⊄ V(1; Z[1/M], ⟨p|M⟩), and the premise
  `aff-q-embeds-in-a-stein-interval-exchange-group` fails. That would kill the factorial-odometer radix-changing host.
