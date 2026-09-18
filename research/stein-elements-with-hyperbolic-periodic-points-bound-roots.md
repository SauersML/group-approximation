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
- **Decided (false in general, below).** The analogous attractor statement for general Stein groups: *every infinite-order element of V(1; Z[1/M],
  ⟨p|M⟩) has a hyperbolic periodic point*. If it holds, item 2 gives Q ⊄ V(1; Z[1/M], ⟨p|M⟩), and the premise
  `aff-q-embeds-in-a-stein-interval-exchange-group` fails. That would kill the factorial-odometer radix-changing host.

## The attractor statement is false (decided 2026-09-18, lane bh-free-31)

- **Counterexample.** Boshernitzan's map φ(t) = 2t + 1/2 on [0,1/4) and (2/3)(t − 1/4) on [1/4,1) is a PL homeomorphism
  of R/Z. Its breakpoints and coefficients lie in Z[1/6] and its slopes in ⟨2,3⟩, so φ ∈ T(Z[1/6],⟨2,3⟩) ⊂
  V(1; Z[1/6], ⟨2,3⟩). Its rotation number is log 2/log 3, which is irrational, so φ has infinite order and no periodic
  point at all.
  - Source: Boshernitzan, "Dense orbits of rationals", Proc. AMS 1993. Read only as quoted in the TeX of Belk–Hyde–Moore,
    arXiv:2211.05825v4 (on MSI), whose Theorem `main` gives another example in T_{2,3}, with rotation number √2 − 1.
  - Direct check: with E(t) = (3^t − 1)/2, one has φ = E ∘ R_α ∘ E^{-1} for α = log 2/log 3. This is because
    E(t + s) = 3^s E(t) + E(s).
  - For any two primes p < q, the same formula with a = (q−p)/(p(q−1)) and b = (p−1)/(q−1) lies in the Stein group once M
    is divisible by p, q and the primes of q − 1. So for every M divisible by 6, V(1; Z[1/M], ⟨p|M⟩) contains
    infinite-order elements with no hyperbolic periodic point. For slopes that are powers of one integer, circle elements
    have rational rotation numbers (Calegari, Kleptsyn, Liousse, as quoted there). So the statement can survive only in the
    Higman–Thompson case.
- **What survives (proved, elementary).**
  - Work on the doubled-rationals Cantor model D. If g has no hyperbolic periodic point, every Fix(g^k) is clopen, because a
    periodic point with slope 1 on the relevant side is fixed on a one-sided neighbourhood.
  - For circle elements: infinite order with no hyperbolic periodic point holds exactly when the rotation number is
    irrational. If rot = r/q and every fixed point of f^q is flat, then f^q = id.
  - So copies of Q, and BS(1,m) bases, in a Stein group must be built from elements whose non-periodic part is
    minimal (rotation-like).
- **Boshernitzan's φ is root-free in every rational-slope PL group.**
  - A root h, with h^n = φ, commutes with the minimal map φ. So h = E R_β E^{-1} with nβ ≡ α mod 1, and h has slopes
    3^β and 3^{β−1}.
  - Slopes in Q_{>0} force β log 3 ∈ Σ_p Z log p. With β = (α + j)/n this gives log 2 + j log 3 = n Σ_p e_p log p, so
    n e_2 = 1 by unique factorization, and n = 1.
  - So this particular minimal element carries no divisibility. Whether some other minimal Stein element is infinitely
    divisible is OPEN.
