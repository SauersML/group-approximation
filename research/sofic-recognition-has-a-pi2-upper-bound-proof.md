---
rg: 2
id: sofic-recognition-has-a-pi2-upper-bound-proof
kind: route
title: Void-challenge normal form with permutation tuples and area bookkeeping
target: sofic-recognition-has-a-pi2-upper-bound
requires: []
---

Use the local definition `Sofic.IsSofic`: `H` is sofic iff for every finite
`F <= H` and `eps > 0` there is a finite set `Y` and a map `phi : H -> Sym(Y)`
with `d(phi(gh), phi(g) phi(h)) <= eps` for `g, h in F` and
`d(phi(g), phi(h)) >= 1 - eps` for distinct `g, h in F`.  Throughout, `d` is
bi-invariant, symmetric, subadditive, and invariant under conjugation and
inversion.

**(=>)**  Let `H` be sofic and let `(W, N, k)` be a challenge all of whose
words are nontrivial in `H`.  Let `n` bound the lengths of the words in `W`
and of `r_1, ..., r_N`, let `F` be the ball of radius `n` in `H`, and take a
model `phi` of `F` at accuracy `eps`.  Put `sigma(x) = phi(x)` for `x in X`.
For a word `u = x_1 ... x_m` with `m <= n`, all prefixes lie in `F`, and
induction on `m` with right-invariance gives

```text
d(sigma(u), phi(u-bar)) <= (m - 1) eps.
```

Also `d(phi(1), id) <= eps`, from `d(phi(1), phi(1)^2) <= eps` and
left-invariance.  Hence for `j <= N`, since `r_j = 1` in `H`,
`d(sigma(r_j), id) <= n eps`, and for `w in W`,
`d(sigma(w), id) >= d(phi(w-bar), phi(1)) - n eps >= 1 - (n + 1) eps`.
Taking `eps = 1 / (k (n + 1))` produces the certificate.

**(<=)**  Assume (SOF1) for every challenge.  Fix a finite `F <= H` and a
target accuracy `delta`.  Choose `n` with `F` inside the ball of radius `n`,
and for every `g` in the ball of radius `2n` fix a word `u_g` of length
`<= 2n`.  Let `W` be the list of all words of length `<= 4n` that are
nontrivial in `H`.  Every word of length `<= 4n` that *is* trivial in `H` has
a finite derivation; let `N` be a relator index and `A` an area such that
each of these finitely many words is a product of at most `A` conjugates of
`r_1^{+-1}, ..., r_N^{+-1}`.  Take `k >= max(A, 1) / delta`.

The challenge `(W, N, k)` is not void, so a certificate `sigma` exists.
Define `phi(g) = sigma(u_g)` on the ball of radius `2n` and `phi = id`
elsewhere.  For `g, h in F` the word `u_{gh}^{-1} u_g u_h` has length
`<= 4n` and is trivial, hence is a product of `<= A` conjugates of relators;
conjugation-invariance, inversion-invariance and subadditivity give

```text
d(phi(gh), phi(g) phi(h)) = d(id, sigma(u_{gh}^{-1} u_g u_h)) <= A / k <= delta.
```

For distinct `g, h in F` the word `u_g^{-1} u_h` has length `<= 4n` and is
nontrivial, so it is in `W`, and left-invariance gives
`d(phi(g), phi(h)) = d(id, sigma(u_g^{-1} u_h)) >= 1 - 1/k >= 1 - delta`.
Thus `phi` is a model of `F` at accuracy `delta`, and `H` is sofic.

**Quantifier count.**  The first disjunct of (SOF1) is the r.e. word
problem.  In the second, `Y` may be taken to be `{1, ..., m}`, the tuple
`sigma` is a finite list of permutations, evaluation of words and Hamming
distances are exact rational computations, and the comparison with `1/k`
is decidable; so the disjunct is an existential over a decidable predicate.
The relators `r_j` are produced by the enumerator of the presentation, so
everything is uniform in its index.  A universal quantifier over challenges
followed by a `Sigma^0_1` matrix is `Pi^0_2`.

Finite presentation codes are recursive presentations with a constant
enumerator, and a finitely generated subgroup of a finitely presented group
given by a generating tuple has an induced recursive presentation uniformly
in the tuple, so both variants follow.
