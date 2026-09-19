---
rg: 2
id: torus-knot-group-k34-not-matricially-stable-via-expander-pair
kind: route
title: Stability would give exact eigencorners of the central fourth power; the expander pair has none
target: torus-knot-group-k34-is-not-matricially-stable
requires:
  - torus-knot-k34-expander-pair-has-no-eigencorner
  - matricially-stable-groups-have-central-eigencorners
---

1. Let `X, Y in U(Q)` be the pair of
   `torus-knot-k34-expander-pair-has-no-eigencorner`.  Since `X^4 = Y^3`,
   the assignment `x -> X`, `y -> Y` defines a homomorphism
   `Theta : K(3,4) -> U(Q)`.  Here `Q = prod_p M_(k_p) / (+)_p M_(k_p)`.
   `c = x^4` is central in `K(3,4)`, and `Theta(c) = u != 1`.
2. Suppose `K(3,4)` were matricially stable.  Then
   `matricially-stable-groups-have-central-eigencorners` applies with
   `H = K(3,4)`, and `c` and `Theta` as above.  It gives a nonzero
   projection `P in Theta(K)' ∩ Q = {X, Y}' ∩ Q` and `lambda != 1` with
   `u P = lambda P`.
3. That contradicts `torus-knot-k34-expander-pair-has-no-eigencorner`.  ∎

Direct form.  Point-norm matricial stability of a finitely presented group
is equivalent to the statement that every asymptotic homomorphism is
asymptotic to genuine ones.  So the lifts `(X_p, Y_p)` are an asymptotic
representation that is not asymptotic to genuine ones.  This is the
matrix-level statement in the target.
