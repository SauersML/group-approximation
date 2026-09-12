---
rg: 2
id: linear-soficity-recognition-has-a-pi2-upper-bound
kind: claim
title: Linear soficity over any computable field is Pi-zero-two for recursive presentations, so its recognition is either trivial or Pi-zero-two complete
distinct_from:
  sofic-recognition-has-a-pi2-upper-bound: that uses permutations and Hamming distance; this uses matrices over a computable field and the normalized rank metric, with exact Gaussian elimination as the checker.
  weak-soficity-recognition-has-a-pi2-upper-bound: that arithmetizes weak soficity through Glebsky's product-quotient characterization because it has no canonical metric; linear soficity has the rank metric, so the sofic-style void-challenge certificate works directly.
  nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound: that needs real-closed-field decision for unitary matrices in Hilbert--Schmidt distance; this needs only exact rank computation over the field, since the rank metric is discrete-valued.
---

ESTABLISHED.  Fix a computable field `F` (a finite field, `Q`, a number
field, or the algebraic closure of any of these) and a separation constant
`delta > 0`.  Say `K` is `delta`-linear sofic over `F` if for every finite
`S <= K` and `eps > 0` there are `n` and `phi : S -> GL_n(F)` with
`rho(phi(g) phi(h), phi(gh)) <= eps` for `g, h, gh in S` and
`rho(phi(g), 1) >= delta` for `g != 1`, where `rho(A, B) = rank(A - B)/n`.
Arzhantseva--Paunescu (Trans. AMS 369 (2017)) show that linear soficity in
their sense coincides with the `delta`-version for `delta = 1/4`.

For a finitely generated recursive presentation `<X | r_1, r_2, ...>`,

```text
K is delta-linear sofic over F   iff   for all (W, N, k):
      (exists w in W, w = 1 in K)
   or (exists n and M : X -> GL_n(F) with
         rho(M(r_j), 1) <= 1/k   for j <= N,
         rho(M(w),   1) >= delta  for w in W).                          (LS1)
```

Both disjuncts are `Sigma^0_1`: the word problem is r.e., and matrices
over a computable field are enumerable with ranks computed exactly by
Gaussian elimination.  Hence `LINEAR-SOFIC_rec` is `Pi^0_2`.  Linear
soficity is hereditary, local, and contains the sofic hence the residually
finite groups (permutation matrices), so
[[second-level-rice-theorem-for-local-approximation-properties]] applies:
either every group is linear sofic over `F`, or linear soficity over `F`
is `Pi^0_2`-complete on two-generator recursive presentations,
undecidable with non-r.e. complement on finite presentations.

This dichotomy also has one fixed target. Let `V` be the two-generator
finitely presented group of
[[universal-local-approximation-fixed-two-generator-test-group]]. For each
fixed computable field `F`, separately,

```text
V is linear sofic over F
  <=> every group is linear sofic over F
  <=> F-linear soficity is closed under arbitrary quotients.
```

Hence the trivial side for `F` occurs exactly when `V` is
`F`-linear-sofic, and the `Pi^0_2`-complete side occurs exactly when it
is not. The same group `V` works for every `F`; the equivalence does not
choose a field and does not decide either fieldwise value. The quotient
equivalence is
[[fixed-finite-relator-quotient-tests-local-permanence]].
