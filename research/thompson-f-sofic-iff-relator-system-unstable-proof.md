---
rg: 2
id: thompson-f-sofic-iff-relator-system-unstable-proof
kind: route
title: Fixed-point characters of almost-actions of F are regular plus abelian, and the abelian part is stable
target: thompson-f-sofic-iff-relator-system-unstable
requires:
  - thompson-f-character-simplex
  - almost-commuting-permutations-are-near-commuting
artifacts:
  - research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md
---

Full proof: artifact, Sections 1--3. Numbering follows the claim.

- **Finite quotients are abelian.** `F'` is infinite and simple, so a homomorphism to a finite group
  kills it. Hence solutions of the relator system in `Sym(n)` are exactly the commuting pairs.
- **Character.** For an almost-homomorphism, `chi(g) = lim_omega |Fix phi_n(g)|/k_n` is a character: it is
  normalized, a class function by bi-invariance, and positive definite by the permutation identity
  `sum c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) |sum_i c_i [sigma_i x = y]|^2`. By
  `thompson-f-character-simplex`, `chi = t tau_reg + (1-t) chi_ab`, and `chi = 1 - t` on `F' \ {e}`.
- **`1 => 4` (amplification).** If `t > 0`, act on `[k_n]^m × (Z/N)^2` by `phi_n^(× m) × tau_N o ab`.
  The defect grows at most by a factor `m`. Elements outside `F'` translate the torus without fixed
  points once `N` is large. Elements of `F' \ {e}` fix a proportion tending to `(1-t)^m`. Choosing `m`,
  `N`, `n` gives sofic approximations, so `F` is sofic.
- **`4 => 3`.** A sequence of `delta_n`-solutions with `d(A_n B_n, B_n A_n) >= epsilon` defines an
  almost-homomorphism (evaluate fixed words; defects are bounded by van Kampen areas times `delta_n`)
  with `chi([a,b]) <= 1 - epsilon`. So `t >= epsilon`.
- **`3 => 2`.** Almost-solutions almost commute, so by `almost-commuting-permutations-are-near-commuting`
  (`k = 2`) they are near commuting pairs, which are solutions.
- **`2 => 1`.** In a separating almost-homomorphism, `phi_n([a,b])` is far from `id`. Stability puts
  `(phi_n(a), phi_n(b))` near commuting pairs, which makes `phi_n([a,b])` near `id`.
