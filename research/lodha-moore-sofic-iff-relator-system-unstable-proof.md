---
rg: 2
id: lodha-moore-sofic-iff-relator-system-unstable-proof
kind: route
title: Fixed-point characters of almost-actions of G_0 are regular plus abelian, and the abelian part is stable
target: lodha-moore-sofic-iff-relator-system-unstable
requires:
  - lodha-moore-group-character-simplex
  - lodha-moore-commutator-simple-abelianization-z3
  - almost-commuting-permutations-are-near-commuting
---

This follows `thompson-f-sofic-iff-relator-system-unstable-proof`, with `Z^3` in
place of `Z^2`.  `pi : G_0 -> Z^3` is the abelianization, with `pi(a), pi(b),
pi(c)` a basis (`lodha-moore-commutator-simple-abelianization-z3`, item 3).

**Solutions are commuting triples.**
- A solution of `S` in `Sym(n)` is a homomorphism `G_0 -> Sym(n)` with finite image.
  The image is a finite quotient of the infinite group `G_0`, hence proper, hence
  abelian (item 2).  So the images of `a, b, c` commute.
- Conversely, let `A, B, C` be commuting permutations.  The homomorphism
  `Z^3 -> Sym(n)` with `pi(a), pi(b), pi(c) -> A, B, C` composes with `pi` to a
  solution of `S`.

**Fixed-point characters.**  Let `phi_n : G_0 -> Sym(k_n)` be an
almost-homomorphism, i.e. `d(phi_n(gh), phi_n(g) phi_n(h)) -> 0` for all `g, h`.
- `chi(g) = lim_omega |Fix phi_n(g)| / k_n` is normalized and a class function.
- It is positive definite, by the identity
  `sum_(i,j) c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) |sum_i c_i [sigma_i x = y]|^2`.
- By `lodha-moore-group-character-simplex`, `chi = t tau_reg + (1-t) chi_ab`, and
  `chi = 1 - t` on `G_0' \ {e}`.

**1 => 4 (amplification).**  Suppose some `chi` has `t > 0`.  Fix a finite
`E ⊂ G_0 \ {e}`.  Let `G_0` act on `[k_n]^m × (Z/N)^3` by `phi_n^(× m)` times
translation by `pi(g) mod N`.
- The defect grows at most by a factor `m`.
- Every `g in E \ G_0'` has `pi(g) != 0`.  Once `N` exceeds every coordinate of
  `pi(E)`, it translates the torus without fixed points.
- Every `g in E ∩ G_0'` fixes a proportion tending to `(1-t)^m`.
- Choosing `m`, then `N`, then `n` gives `(E, epsilon)`-approximations for every
  `E` and `epsilon`.  So `G_0` is sofic.

**4 => 3.**  Suppose (3) fails.  Then for some `epsilon > 0` there are
`delta_n`-solutions `(A_n, B_n, C_n)` in `Sym(k_n)`, with `delta_n -> 0`, and one
pair, say `(A_n, B_n)`, with `d(A_n B_n, B_n A_n) >= epsilon`.
- Evaluating fixed words defines an almost-homomorphism: the defect of each pair
  `g, h` is at most `delta_n` times the van Kampen area of the corresponding
  relation over `S`.
- If `[a,b] = e` in `G_0`, then `d(A_n B_n, B_n A_n) -> 0`, a contradiction.
- Otherwise `e != [a,b] in G_0'`, and `chi([a,b]) <= 1 - epsilon`.  So `t >= epsilon`
  and `chi` has a regular component, contradicting (4).
- The other pairs are the same.

**3 => 2.**  Almost-solutions almost commute by (3).  By
`almost-commuting-permutations-are-near-commuting` with `k = 3`, they are close to
commuting triples, and these are solutions.

**2 => 1.**  Suppose `G_0` is sofic.  Take an almost-homomorphism `phi_n` with
`d(phi_n(g), id) -> 1` for a fixed `e != g in G_0'`.
- The triples `(phi_n(a), phi_n(b), phi_n(c))` are `o(1)`-solutions.  By (2) they
  are `o(1)`-close to commuting triples.
- `g` is a fixed product of commutators of the generators.  Evaluating words is
  Lipschitz in each letter, so `phi_n(g)` is `o(1)`-close to its value on a
  commuting triple, which is `id`.
- That contradicts `d(phi_n(g), id) -> 1`. ∎
