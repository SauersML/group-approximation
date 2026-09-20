---
rg: 2
id: brieskorn-lattice-345-not-matricially-stable-via-gauge-pair
kind: route
title: Stability of the Brieskorn lattice would give exact eigencorners of its centre; the gauge pair has none
target: brieskorn-lattice-345-is-not-matricially-stable
requires:
  - brieskorn-345-gauge-pair-has-no-eigencorner
  - matricially-stable-groups-have-central-eigencorners
---

1. Let `X, Y in U(Q)` be the pair of
   `brieskorn-345-gauge-pair-has-no-eigencorner`, with
   `Q = prod_q M_(N_q) / (+)_q M_(N_q)`.  That node shows that `x -> X`,
   `y -> Y` defines a homomorphism `Θ : Λ -> U(Q)`, since
   `X^4 = Y^3` and `(YX)^5 = X^12` hold in `Q`.  The element `c = x^4` is
   central in `Λ`, and `Θ(c) = u` with `||u - 1|| = 2`, so `u != 1`.
2. Suppose `Λ` were matricially stable.  Then
   `matricially-stable-groups-have-central-eigencorners` applies with
   `H = Λ` (countable), and `c` and `Θ` as above.  It gives a nonzero
   projection `P in Θ(Λ)' ∩ Q = {X, Y}' ∩ Q` and `λ != 1` with `u P = λ P`.
   Indeed `λ` can be any point of `sp(u) = {e^(iθ) : 0 <= θ <= π}`, for
   example `λ = -1`.
3. That contradicts the "no eigencorner" item of
   `brieskorn-345-gauge-pair-has-no-eigencorner`.  ∎

Direct form.  `Λ` is finitely presented.  So point-norm matricial stability
of `Λ` is equivalent to the following statement: every sequence of pairs
with defects in the two relators going to `0` is asymptotic to a sequence of
exact pairs.  The lifts `(X_q, Y_q)` have defects `O(1/log N_q)`, by the
bounds of that node.  If they were asymptotic to exact pairs, then those
exact pairs would give a lift of `Θ` through a genuine homomorphism on each
block, which is the hypothesis used in the proof of
`matricially-stable-groups-have-central-eigencorners`.  So the lifts are an
asymptotic representation that is not asymptotic to genuine ones, along
every subsequence.  This is the matrix-level statement in the target.
