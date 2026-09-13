---
rg: 2
id: thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words
kind: claim
title: Thompson's V is hyperlinear exactly when unitary gluings of regular S4 and S3 representations nearly satisfy four words
distinct_from:
  thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words: that is the permutation form, where the gluing parameter ranges over C2 wr S_(L/2); this is the normalized Hilbert--Schmidt form, where it ranges over the full unitary commutant of one involution, and permutation gluings are the special case of permutation matrices.
  thompson-v-one-word-strict-hs-ceiling: that bounds the energy of one marked word over all almost-representations of a presentation; this makes every short relator exact and both finite subgroups regular, so all error sits in four words and the separation is free.
  thompson-v-ce-one-word-trace-face-is-binary: that is the zero-or-two support law for the Connes-embeddable traces of one word; this is a finitary gluing criterion for the whole group.
  thompson-v-hyperlinear: that is the open problem itself; this is an equivalent form of it, not an answer.
---

**ESTABLISHED.** Use the generators `a, b, c` and the four long words `r5, ..., r8` of
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, so that
`V = (S4 *_<a> S3) / <<r5, r6, r7, r8>>` with `S4 = <a, b | a^2, b^3, (ab)^4>` and
`S3 = <a, c | a^2, c^2, (ac)^3>`. Unitaries are evaluated on words letter by letter, `tr` is the
normalized trace and `||x||_2 = tr(x^* x)^(1/2)`.

A **unitary free gluing** of size `N = 24k` is a triple `(A, B, C)` in `U(N)` such that `a, b -> A, B`
is a representation of `S4` equivalent to `k` copies of its regular representation, and `a, c -> A, C`
is a representation of `S3` equivalent to `4k` copies of its regular representation.

**Standard form.** Let `A_0, B_0` be the permutation matrices of left multiplication by `a, b` on
`S4 x [k]`, and `C_0` the permutation matrix of a free `S3`-structure on the same set in which `a`
acts as `A_0`. The unitary free gluings of size `24k` are, up to simultaneous unitary conjugation,
exactly `(A_0, B_0, W^* C_0 W)` with `W` in the commutant of `A_0`, which is `U(12k) x U(12k)` in an
eigenbasis of `A_0`.

The following are equivalent.
1. `V` is hyperlinear.
2. For every `epsilon > 0` there are `N` and unitaries `A, B, C` in `U(N)` such that `a, b -> A, B` is a
   representation of `S4`, `a, c -> A, C` is a representation of `S3`, `|tr h(A, B, C)| <= epsilon`
   for every nontrivial `h` in either factor, and `||r_i(A, B, C) - I||_2 <= epsilon` for
   `i = 5, ..., 8`.
3. For every `epsilon > 0` there is a unitary free gluing with `||r_i - I||_2 <= epsilon` for
   `i = 5, ..., 8`.
4. For every `epsilon > 0` there are `k` and a unitary `W` commuting with `A_0` in `U(24k)` such that
   `||r_i(A_0, B_0, W^* C_0 W) - I||_2 <= epsilon` for `i = 5, ..., 8`.

So `V` is not hyperlinear exactly when some `epsilon_0 > 0` works for every `k` and every `W`
commuting with `A_0`: one of the four words has `||r_i - I||_2 > epsilon_0`.

## What it says

- **Everything but four words is exact.** In every gluing all short relators hold exactly and every
  nontrivial element of `S4` or `S3` has trace `0`. In particular `||A - I||_2^2 = 2`, the regular
  value, so no separation has to be certified.
- **One unknown unitary.** The search space is the commutant `U(12k) x U(12k)` of one involution.
  Conjugating `W` on the left by the commutant of `(A_0, C_0)` or on the right by the commutant of
  `(A_0, B_0)` gives the same gluing up to equivalence.
- **Contains the permutation form.** A permutation `nu` commuting with `A_0` is a unitary `W`, so a
  near-solution of `thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words` is a near-solution here,
  matching "sofic implies hyperlinear".
- **Mechanism of `1 => 2`.** Tensor powers of `U (x) conj(U)` push the traces of the finitely many
  nontrivial factor elements toward `0`. Gowers--Hatami rounding makes each finite subgroup exact
  after enlarging the dimension by a vanishing proportion. The two copies of `a` are then conjugated
  onto each other by a unitary close to the identity.
- **Mechanism of `2 => 3`.** Pad by `O(epsilon N)` dimensions carrying the missing irreducible
  representations, so both factors become exactly regular, and match the two `a`-spectra on the
  padding.
- **Mechanism of `4 => 1`.** The gluings define a homomorphism of `V` into a tracial matrix
  ultraproduct in which `a` has trace `0`. `V` is simple, so it is injective.

Derivation: `thompson-v-hyperlinear-iff-unitary-gluings-proof`.
