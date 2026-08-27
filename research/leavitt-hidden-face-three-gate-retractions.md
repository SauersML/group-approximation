---
rg: 2
id: leavitt-hidden-face-three-gate-retractions
kind: claim
title: The first hidden collision face alone retains all three visible base gates
artifacts:
  - research/leavitt-hidden-face-three-gate-retractions-proof.md
  - research/artifacts/verify-leavitt-nielsen-collision-red-team.py
distinct_from:
  leavitt-length-six-nielsen-collision-candidate: that supplies the formal repeated gate; this fences the first additional exact Leavitt face after the fold.
  leavitt-nielsen-collision-has-a-hidden-first-side-relation: that proves the hidden relation; this proves its normal closure alone does not kill x, y, or u and states the stronger one-factor criterion needed for KL.
  kl-violating-equation-over-leavitt-unit-group: that needs a nontrivial word in one original coefficient copy to die; a mixed paired kernel is not sufficient, and no such word is produced here.
---

Let `Q_form -> C=G_0*G_1` be the folded corner map, let `N` be its kernel,
and let `psi:Q_form -> L` be the injective Tietze map.  A strict normal-closure
intersection

```text
psi^(-1)(<<psi(N)>>_L) > N
```

only yields a KL certificate when the surviving coefficient word lies
nontrivially in one factor `G_i`, or the same picture explicitly implies such
a one-factor relation.  A mixed word of `G_0*G_1` is insufficient.

For the exact hidden relation
`Omega=[u,b^2ub^(-2)]`, its Tietze image alone does not kill any of the visible
base gates.  The quotient by its normal closure has explicit quotient maps
onto `<x>`, `C_2(y)`, and `C_2(u)`, retaining the named gate and killing the
other base generators and the bridge `s`.  Therefore any successful picture
must use at least one further actual corner relation and must return a
nontrivial boundary to a single coefficient copy.

The pair consisting of the literal collision `k_0k_1` and `Omega` gives no
second transport: the first relation merely folds `k_0,k_1` to `u`, after
which the quotient is exactly the one-hidden-face model above.  Moreover the
current corners expose `a_1=u` and `r_1=h_0h_1`, but not `a_0` or `r_0`
separately.  Thus a shifted copy of `Omega` is not a cheap corner relation of
this candidate.
