---
rg: 2
id: vector-form-relator-certificate-counterexample-proof
kind: route
title: Extend partial left translations on a finite trajectory set to permutations
target: linear-norm-certificate-has-no-vector-form
requires: []
artifacts:
  - research/artifacts/linear-certificate-has-no-vector-form-2026-09-08.md
---

## Proof

Work in `G` itself, with `q : F ->> G`.

**The finite set.**  Reading a word right to left, its successive suffixes
applied to `1` by left multiplication trace a trajectory in `G`.  Let `B` be a
finite subset of `G` containing `1` and every point of the trajectories of the
finitely many words in `S u {w}`.

**The permutations.**  For each free generator `x`, left multiplication by
`q(x)` restricts to a bijection

```text
{ b in B : q(x)b in B }  -->  { b in B : q(x)^-1 b in B },
```
between two subsets of `B` of the same cardinality.  Extend it by any
bijection of the two complements to a permutation `sigma_x` of `B`.  By
construction `sigma_x(b) = q(x)b` whenever both `b` and `q(x)b` lie in `B`,
and correspondingly `sigma_x^-1(b) = q(x)^-1 b` whenever both lie in `B`.

Let `U_x` be the permutation matrix of `sigma_x` on `l^2(B)`, and put
`xi = e_1`.  Since `F` is free, any assignment of the `U_x` defines the
evaluation of every word.

**Trajectories are followed exactly.**  Let `u` be one of the words in
`S u {w}`.  Evaluating `u(U)` on `xi` applies the letters of `u` from the
right; at each step both the current point and its image lie in `B`, because
`B` was chosen to contain the whole trajectory.  So each letter acts as the
true left translation, and

```text
u(U) xi = e_(q(u)).
```

**Conclusion.**  For `s in S <= R` we have `q(s) = 1`, so `s(U)xi = e_1 = xi`
and `(s(U) - I)xi = 0`.  For `w` we have `q(w) != 1`, so `w(U)xi = e_(q(w))`
is a basis vector different from `e_1` and

```text
||(w(U) - I)xi|| = ||e_(q(w)) - e_1|| = sqrt 2.
```
This is `(VF1)`, and it contradicts `(VF2)` for every constant `C`, since the
right-hand side is zero.

## The compression remark

Let `P` be the orthogonal projection onto `C xi`.  Then `(s(U) - I)P = 0` for
every `s in S`, while `||(w(U) - I)P|| = sqrt 2`.  But `P U_x P` is a
`1 x 1` matrix whose entry is the coefficient of `e_1` in `U_x e_1`, which is
`0` whenever `sigma_x` moves `1`.  So the compressions are not unitary and do
not define a representation.  This is exactly why a common fixed vector for
the relators cannot be converted into a finite-dimensional model of the
quotient.

## Why this does not touch the operator certificate

`mf-radical-words-have-linear-certificates` bounds `||w(U) - I||` by the
largest `||s(U) - I||` over the **whole** space.  In the witness above the
permutations `sigma_x` were extended arbitrarily off the trajectory set, so
`s(U)` is typically far from `I` there, and the right-hand side of that
certificate is large.  Nothing here supplies matrix models satisfying the
relators in operator norm.
