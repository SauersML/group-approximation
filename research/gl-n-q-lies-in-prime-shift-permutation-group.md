---
rg: 2
id: gl-n-q-lies-in-prime-shift-permutation-group
kind: claim
title: GL_n(Q) and Aff(Q) lie in finitely generated 2-transitive permutation groups in which all prime dilations are conjugate
distinct_from:
  gl-n-q-generated-by-gl-n-z-and-prime-dilations: that writes GL_n(Q) as GL_n(Z) plus infinitely many commuting prime dilations; this adds one non-linear permutation conjugating each dilation to the next, so finitely many generators suffice.
  gl-n-q-in-permutational-boone-higman-class: that is the open type (A) target; this gives explicit finitely generated 2-transitive permutation groups containing PGL_n(Q) and Aff(Q), for which type (A) reduces to finite presentation plus one finitely generated point stabilizer, both unknown.
  gl-n-q-explicit-natural-fp-overgroup: that is Problem 2.7, asking for a finitely presented overgroup; these overgroups are explicit and finitely generated but not known to be finitely presented.
artifacts:
  - research/artifacts/gq-deep-typeA-2-register-dilations.md
---

**ESTABLISHED (2026-09-18)** through
`gl-n-q-lies-in-prime-shift-permutation-group-proof`. Lane proof, not
independently reviewed; it is elementary and no novelty is claimed.

**Setup.**
- Fix a bijection `k -> p_k` from `Z` onto the primes, with `p_0 = 2`. For
  example `p_k` is the `2k`-th prime for `k > 0` and the `(1-2k)`-th prime for
  `k < 0`.
- By unique factorization `Q^x = {±1} × ⊕_(k in Z) p_k^Z`. So there is a unique
  automorphism `σ` of the multiplicative group `Q^x` with `σ(-1) = -1` and
  `σ(p_k) = p_(k+1)`. Put `σ(0) = 0`; then `σ` is a permutation of `Q`.
- `σ` is not additive: `σ(1+1) = σ(2) = p_1`, while `σ(1)+σ(1) = 2`.
- Let `σ_n` be the permutation of `Q^n` applying `σ` in every coordinate, and
  `e = diag(2,1,...,1)`.

**Statement.**
1. For `n >= 1`, `K_n = <GL_n(Z), e, σ_n> <= Sym(Q^n)` contains `GL_n(Q)` with
   its linear action, and `K_n = <GL_n(Q), σ_n>`.
2. `σ_n^k e σ_n^-k = diag(p_k,1,...,1)` for every `k in Z`. `σ_n` commutes with
   every signed permutation matrix and normalizes the diagonal group
   `(Q^x)^n`, acting on it by `σ` in each coordinate. `<e, σ_n> ≅ Z ≀ Z`.
3. `σ_n` maps lines through `0` onto lines, so `K_n` acts on `P^(n-1)(Q)`. Let
   `PK_n` be the image in `Sym(P^(n-1)(Q))`. For `n >= 2`, `PK_n` contains
   `PGL_n(Q)`, and so it is 2-transitive: one orbit of two-element subsets.
4. **Affine version.** `A_1 = <x -> x+1, x -> 2x, x -> -x, σ> <= Sym(Q)`
   contains `Aff(Q) = Q ⋊ Q^x` and is 2-transitive on `Q`.
5. **What type (A) needs.** The actions of `PK_n` on `P^(n-1)(Q)` and of `A_1`
   on `Q` are faithful and have one orbit of two-element subsets. So each is of
   type (A) (`type-a-action-gives-boone-higman-for-subgroups`) exactly when the
   group is finitely presented and one point stabilizer is finitely generated.
   Neither condition is known for any `n`. If both held for `PK_n` for every
   `n >= 2`, then every `PGL_n(Q)` would lie in `B_A`, and by
   `gl-n-q-targets-are-cofinal-in-n` so would every `GL_n(Q)`. That is
   `gl-n-q-in-permutational-boone-higman-class`.

**Universal form.** Let `N_n(Q)` be the monomial group (diagonal times signed
permutations), and `α` the automorphism of `N_n(Q)` applying `σ` to the diagonal
entries. The HNN extension `Π_n = <GL_n(Q), s | s m s^-1 = α(m), m in N_n(Q)>`
is finitely generated, and `s -> σ_n` induces a surjection `Π_n -> K_n`
(item 2). So `K_n` is the permutation image of the HNN extension that makes all
prime dilations conjugate.

**Why the known obstructions do not apply.** `σ` is continuous for neither the
real nor any `p`-adic topology. So the natural-action obstructions for
piecewise-projective, piecewise-linear, adelic and germ-extension hosts say
nothing about `K_n` or `A_1`. Both groups contain `(Q,+)` and `BS(1,2)`, so they
are not residually finite (O1) and have distorted cyclic subgroups (O4), as any
host must.

**Why finite presentation is not evident.** In `Π_n` the conjugates
`s^k e s^-k` satisfy relations such as
`(s^k e s^-k) x_12(1) (s^k e s^-k)^-1 = x_12(1)^(p_k)`. Their exponents grow
with `k`, and conjugating by `s` does not derive them from finitely many,
because `s` does not normalize `GL_n(Z)`. In `K_2`, with the example indexing
(`p_1 = 3`, `p_-1 = 5`, `p_2 = 7`), `σ_2 x_12(1) σ_2^-1` sends `(0,1)`, `(1,1)`,
`(2,1)` to `(1,1)`, `(3,1)`, `(21,1)`. A linear map would send `(2,1)` to
`(5,1)`, so it is not linear. See the artifact, §2.

## Attempts

None beyond the statement. The smallest open test is `A_1`: is it finitely
presented, and is `Stab_(A_1)(0)` finitely generated? See the artifact, §5.
