---
rg: 2
id: kms-natural-affine-actor-orbit-count-proof
kind: route
title: The KMS comparison map is injective on the module and the letter automorphisms never shorten words, so the spans over long words are invariant
target: kms-natural-affine-actor-has-infinitely-many-orbits
requires:
  - orbit-finite-affine-actions-are-type-a
artifacts:
  - research/artifacts/solve-bh-kms-lamps-2026-09-13.md
---

**Sources.** KMS, Bull. Math. Sci. 7 (2017), PDF text (lane scratch
`bhwp/kms-bms.txt`), read 2026-09-13:
- Lemma 3.15(b), p. 332: equal nonzero words of `Š` have equal exponents of every
  letter;
- the normal form of nonzero elements of `Š`, p. 338;
- the automorphisms (11) and those for `ã_j`, `A_j`, `A_0`, pp. 339--340;
- Lemmas 4.10, 4.11 and 4.13, pp. 340--341.

Some primes and tildes are lost in the extraction. The shapes below follow the
surrounding definitions, and the inverses are recomputed here rather than copied.

**Step 1: `gamma` is an isomorphism.**
- Lemma 4.10 gives the homomorphism `gamma`. By Lemma 4.11 it is surjective and
  `gamma^(-1)(T_1) = T`.
- The proof of Lemma 4.11 gives `gamma(x(i, w)) = z(i, w)`. By Lemma 4.13 the
  `x(i, w)` form a basis of `T`, so `gamma` is injective on `T`.
- `ker gamma` lies in `gamma^(-1)(1)`, which is inside `T`, so it is trivial.

**Step 2: the shapes of the letter automorphisms.** Write `T_1` additively.
- Fix a letter index `j`. For a basis word `w` and a vector `i`, write
  `e_r = z(i, w)` when `i_j = r` and the other coordinates of `i` are fixed. Write
  `S e_r = z(i, w')` at a shifted word `w'`, with the same `i`.
- By pp. 339--340, each letter acts on the basis vectors at a word `w` in one of four
  ways. Here `w' = 0` means `z(i, 0) = 0`.
  - **(P)** the identity. This covers `a_j, a'_j` on words containing `A_j`, `ã_j, ã'_j`
    on `W_0`, `A_j` on words containing `A_j`, and `A_0` on `W_0`.
  - **(N)** `e_1 |-> e_1 + e_2 + e_3 + S e_1`, `e_2 |-> e_2 - e_1`, `e_3 |-> e_1`. This is
    `a_j` on words without `A_j`, with `w' = w a_j`, and `ã_j` on `W`, with `w' = w a_j`
    or `w' = v a_j A_j` when `w = v A_j`.
  - **(N-1)** the conjoint of (N): `e_1 |-> e_2 + e_3 + S e_1`, `e_2 |-> -e_1`,
    `e_3 |-> e_1 - e_3`, with the same `w'`. This is `a'_j` and `ã'_j`.
  - **(A)** `z(i, w) |-> z(i, w) + z(i, w')`, with `w' = w A_j` (for `A_j` on words without
    `A_j`) or `w' = psi(w)` (for `A_0` on `W`).
- At the shifted word `w'`, the same letter again has shape (N) or (N-1). The reason:
  `w a_j` still has no `A_j`, and `v a_j A_j` still has the form `v' A_j` with `v' in W`.
  Likewise the vectors `z(i, w')` of shape (A) are fixed, since `w A_j` contains `A_j`
  and `psi(w) in W_0`.
- So the inverses are the following. Each is checked by applying the operator, using
  `N(S e_3) = S e_1` and `(N-1)(S e_2) = -S e_1` at `w'`:
  - `N^(-1)`: `e_1 |-> e_3`, `e_2 |-> e_2 + e_3`, `e_3 |-> e_1 - e_2 - 2 e_3 - S e_3`.
    Check: `N(e_1 - e_2 - 2e_3 - S e_3) = (e_1+e_2+e_3+S e_1) - (e_2-e_1) - 2e_1 - S e_1 = e_3`.
  - `(N-1)^(-1)`: `e_1 |-> -e_2`, `e_2 |-> e_1 + e_2 + e_3 + S e_2`, `e_3 |-> -e_2 - e_3`.
    Check: `(N-1)(e_1+e_2+e_3+S e_2) = (e_2+e_3+S e_1) - e_1 + (e_1-e_3) - S e_1 = e_2`.
  - `A^(-1)`: `z(i, w) |-> z(i, w) - z(i, w')`.
- Each letter is an automorphism (KMS p. 339), so these right inverses are the inverses.

**Step 3: `U_n` is invariant.** Every letter and every inverse of a letter sends
`z(i, w)` to a combination of basis vectors at `w` and at one shifted word `w'`.
- If `w in W_0`, then `w' in W_0 ∪ {0}`, because products are taken in `S(MM_k)`.
- If `w in W`, then `w'` is `w a_j` or `v a_j A_j`, with a-length one more; or `w A_j`,
  with the same a-length; or `psi(w) in W_0`; or `0`.
- The a-length is well defined by Lemma 3.15(b): the exponents of letters are invariant.

So each generator of `M`, and its inverse, maps `U_n` into `U_n`, and `U_n` is
`M`-invariant.

**Step 4: the spaces strictly decrease.**
- For every `n`, let `w_n = q_0 a_1^n`. The relations of `Š` (p. 325) are:
  - the commutativity relations (2), between letters with distinct indices;
  - the 0-relations `x y = 0`, where `x y` is a two-letter word that is not a subword of
    any `q_i a_1^(l_1) ... a_k^(l_k) A_1^(beta_1) ... A_k^(beta_k)` modulo (2).

  No relation (2) applies to `w_n`, so `w_n` is equal only to itself. Its two-letter
  subwords `q_0 a_1` and `a_1 a_1` are allowed, so `w_n` is nonzero. Hence `w_n in W`
  and `|w_n|_a = n`.
- The basis vector `z(1, w_n)` lies in `U_n` but not in `U_(n+1)`.

**Step 5: orbits.**
- The sets `U_n \ U_(n+1)`, `n >= 0`, are nonempty, `M`-invariant and pairwise disjoint.
  So `M` has infinitely many orbits on `T_1`.
- `M <= Aut(T_1)`, so `orbit-finite-affine-actions-are-type-a`, item 2, puts the
  `G(MM_k)`-orbits on pairs in bijection with the `M`-orbits on `T_1`.
- The affine action therefore has infinitely many orbits of pairs, and is not of
  type (A). `∎`
