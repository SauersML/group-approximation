---
rg: 2
id: cuntz-calkin-lifts-of-thompson-v-have-no-compression
kind: claim
title: No lift of a Cuntz-type Calkin model of Thompson's V has an asymptotically commuting matrix compression, so the Fock tree near-permutation lane to V MF is dead
distinct_from:
  thompson-v-unitaries-generate-cuntz-algebra: that is the C*-algebra equality C*(V) = O_2 inside O_2; this is the class obstruction it yields for corona models built by lifting and compressing.
  properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group: that shows a properly infinite C*-quotient does not obstruct MF for a free group; this is not about quotients of C*(V) but about the Calkin image of a specific lift, which the compression must map unitally into a finite corona.
  toeplitz-pair-algebra-is-qd-with-non-qd-irreps: that is a quasidiagonal Toeplitz-type algebra of one shift; here the Calkin image is all of O_2, and no lift is quasidiagonal.
---

**ESTABLISHED (written proof; not Lean-verified).** This obstructs a class of
approaches to `thompson-v-is-not-mf` and its negation. It decides neither.

## The class

A **Cuntz-type Calkin model** of `V` is given by the following data:

- a separable Hilbert space `H`;
- a unital *-homomorphism `theta : O_2 -> Q(H) = B(H)/K(H)`;
- the resulting Calkin representation `rho = theta o u : V -> U(Q(H))`, where `u` is the
  prefix-replacement embedding of `thompson-v-unitaries-generate-cuntz-algebra`.

The basic example is the **tree** (or **Fock**) near-permutation model.

- **The space.** `H = l^2(X*)` over the vertices of the binary tree, with
  `S_i e_w = e_{iw}`.
- **The group.** `g` with code pair `(p_k) -> (q_k)` acts by `p_k w -> q_k w` off the
  finitely many vertices above its domain code. It is completed by any bijection there, so
  it is an honest permutation `pi_g` of `X*`.
- **The relations.** The relations of `V` hold up to finitary permutations. So
  `pi_g = sum_k S_{q_k} S_{p_k}^*` modulo finite rank.

A **lift** is a choice of operators `U_s in B(H)` with `U_s + K = rho(s)`, for `s` in a
finite generating set of `V`. The lifts need not be unitary, and they need not satisfy any
relation.

A **matrix compression** of the lift is a sequence of isometries
`W_n : C^{k_n} -> H` with these properties:

- `W_n W_n^* -> 0` strongly;
- `||[W_n W_n^*, U_s]|| -> 0` and `||[W_n W_n^*, U_s^*]|| -> 0` for each generator `s`.

A quasidiagonal lift gives one. So does the block-compression route: take far-out blocks
`P_m - P_l` of an increasing quasidiagonal sequence, so that the finite-rank relator defects
fall outside the blocks.

When a matrix compression exists, `s -> (W_n^* U_s W_n)_n` is a corona model of `V` in
`prod M_{k_n} / sum M_{k_n}`. It is exactly multiplicative on relators, and it is injective
on `V` by simplicity. So it would prove `V` MF. This is the lane "V acts on its tree by
bounded-propagation near-permutations with finite-rank defects; compress quasidiagonally".

## The claim

**No lift of any Cuntz-type Calkin model of `V` has a matrix compression.** In particular:

- the set `{pi_a, pi_b, pi_c}` of tree near-permutations is not quasidiagonal, for any
  completion of the finitely many undefined vertices;
- no compact perturbation of any O_2-factoring Calkin representation is quasidiagonal.

## Where every member dies

Every member dies at one step, the descent of the compression to the Calkin image. The
invariant is `C*(rho(V)) = theta(O_2)`. That algebra has an infinite unit, and a finite
corona cannot receive it unitally.

Proof: `cuntz-calkin-lifts-of-thompson-v-have-no-compression-proof`.

## What survives

A successful MF witness for `V` built from a Hilbert-space model must have a Calkin image,
or more generally a model algebra modulo the ideal the compression kills, with the following
properties:

- it is **not** a quotient of `O_2` along `u`;
- in particular, the defects of the lift are not merely compact against any Cuntz family
  realizing `V` by prefix replacement.

This agrees with, and is independent of, the earlier representation-theoretic kills:

- `D >= sqrt 3` for permutation models;
- `D >= sqrt 2` for monomial models;
- `D >= 1/2` for amenable images.

Those bound the relator defect of finite-dimensional models. This removes the natural
infinite-dimensional source of such models.
