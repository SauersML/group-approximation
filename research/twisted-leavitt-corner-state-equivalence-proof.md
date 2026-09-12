---
rg: 2
id: twisted-leavitt-corner-state-equivalence-proof
kind: route
title: Halve the unit class through the diagonal endomorphism, then apply the state criterion
target: twisted-leavitt-corner-fullness-equals-absence-of-k0-states
requires:
  - cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
  - leavitt-unit-group-algebras-split-over-scalar-characters
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

In the monoid `V(A)` of finitely generated projective classes, write `a <= b` when `b = a + c`. Put
`p = [e_H A]`, so `u = mp`.

- **Corner as a Cohn form.** Part 3 of the matrix-structure claim: item 1 holds iff `m[T] <= [T]`,
  that is, `mp <= p`.
- **Diagonal homomorphism.**
  - `D(h) D(h') = D(h h')`, because `t_i s_j = delta_ij`.
  - `D(1) = sum_i s_i t_i = 1` and `D(lambda) = lambda`.
  - `g D(h) = D(h) g = sum_i s_(i+1) h t_i`.
  So `D` extends to a unital endomorphism of `F_q[G]` that fixes `eps_iota` and commutes with `e_H`,
  and `psi(x) = e_H D(x)` is a unital ring homomorphism `A -> T`.
- **Halving.** `M_m(psi)`, followed by `M_m(T) ~= A`, is a unital map `M_m(A) -> A`. Through Morita
  equivalence it induces a monoid homomorphism `F: V(A) -> V(A)` with `F(mu) = u`. Put `x = F(u)`,
  so `mx = u`.
- **1 => 2.** From `mp <= p`, substituting repeatedly gives `p + k(m-1)p <= p` for every `k`. Taking
  `k = m` and adding `(m-1)p` gives `mu <= u`, and hence `2u <= u`.
- **2 => 1.** `psi` carries a two-pair Cohn family of `A` to one of `T`. So `2[T] <= [T]`, hence
  `m[T] <= [T]`.
- **2 => 3.** Take `n = 1`.
- **3 => 2.** Pad `(n+1)u <= nu` to `n = mj`. Applying `F` gives `ju + x <= ju`, and iterating gives
  `ju + mx <= ju`, that is `(j+1)u <= ju`. Since `ceil(n/m) < n` for `n >= 2`, repeating reaches
  `n = 1`.
- **3 <=> 4.** `A^n ~= A^(n+1) (+) Q` gives `-u = [Q]`. Conversely, `-u = [Q]` in `K_0` is a stable
  isomorphism `Q (+) A (+) A^N ~= A^N`. Also `ku <= 0` gives `-u = (k-1)u + (-ku)` in the cone.
- **4 <=> 5.** The Hahn–Banach state criterion, Theorem A(b) of the artifact, which uses only that `u`
  is the class of the unit.
- **Surjunctivity.** Item 4 gives a one-sided pair in some `M_N(A)`. Padded by `1 - eps_iota`, it is a
  one-sided pair in `M_N(F_q[G])`, and the stable-finiteness lemma gives the automaton.

Section 7 of the artifact.
