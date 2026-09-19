---
rg: 2
id: matricially-stable-groups-have-central-eigencorners
kind: claim
title: In a matricially stable group every central element has exact eigencorners at every point of its spectrum, in the relative commutant of every corona representation
distinct_from:
  commutant-projection-extraction: that asks for eigencorners for every countable group; this proves them for matricially stable groups, which is the case where the corona representation lifts to exact representations.
  matricial-stability-identifies-radicals: that computes Rad_MF of a matricially stable group from its finite-dimensional representations; this is a statement about the relative commutant of an arbitrary corona representation, and is what is needed when a non-stable quotient (such as T-bar) is studied through a stable cover.
  corona-commutant-no-growth: its route corona-commutant-no-growth-via-uniform-stability uses uniform stability to bound commutant growth; this uses point-norm matricial stability to produce central spectral projections.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`matricially-stable-groups-have-central-eigencorners-proof`.

Let `H` be a countable group that is matricially stable in Dadarlat's
point-norm sense (`dadarlat-matricial-stability-obstruction`).  That is, every
asymptotic homomorphism `phi_n : H -> U(k_n)` is pointwise operator-norm
asymptotic to a sequence of homomorphisms `psi_n : H -> U(k_n)`.  Let
`c in Z(H)`, let `Q = prod_n M_(k_n) / (+)_n M_(k_n)`, and let
`Theta : H -> U(Q)` be a homomorphism.  Put `B = Theta(H)' ∩ Q`.

Then for every `lambda in sp(Theta(c))` there is a nonzero projection
`P in B` with

```text
Theta(c) P = lambda P.
```

In particular, if `Theta(c) != 1` then such a `P` exists with
`lambda != 1`.  This is the conclusion of `commutant-projection-extraction`
for `(H, c)`, in its exact form.  Moreover `P` can be taken to lie in the
image of `prod_n psi_n(H)'` for the exact lifts `psi_n`.

## Consequences

- Take `H = K(3,4)` and `c = x^4`.  Then
  `torus-knot-group-k34-is-matricially-stable` implies
  `torus-knot-group-k34-has-central-eigencorners` (route
  `torus-knot-group-k34-central-eigencorners-via-stability`).  Through
  `lifted-thompson-t-is-a-torus-knot-group-quotient`, it also implies
  `lifted-thompson-t-centre-has-commutant-eigencorners`.
- The general principle is this.  Let `G` be a quotient of a matricially
  stable group `H`, by a map sending a central `c` to a central `c-bar`.
  Then every corona representation of `G` has exact eigencorners of
  `c-bar`, even when `G` itself is far from stable.  For example `T̄` is
  not residually finite, so it is not matricially stable unless it fails
  to be MF.  This is also the conclusion of `matricial-stability-identifies-radicals`
  for a group with no finite-dimensional representations.  The same remark
  is in Eilers-Shulman-Sørensen, arXiv:1808.06793, Section 4.4, which says
  verbatim: "if G is ﬁnitely generated then it cannot be matricially
  stable by Proposition 2.19".
