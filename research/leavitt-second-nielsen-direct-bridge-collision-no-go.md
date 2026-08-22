---
rg: 2
id: leavitt-second-nielsen-direct-bridge-collision-no-go
kind: claim
title: Direct equality of the two length-six Tietze bridge images forces a freely reducible word
artifacts:
  - research/leavitt-second-nielsen-direct-bridge-collision-no-go-proof.md
distinct_from:
  leavitt-length-six-nielsen-collision-candidate: that collides the first corner map by duplicating a coefficient gate; this proves why the analogous direct collision cannot occur in the second Tietze map of a reduced word.
  leavitt-nielsen-collision-has-a-hidden-first-side-relation: that gives a kernel with the wrong pushout variance; this isolates the stable-letter obstruction to reversing its variance by equating the two bridge images.
---

For the two eliminated length-six bridge corners,

```text
psi(h)=s x^(-1)s^(-1)y^(-1)s,
psi(k)=s v^(-1)s u^(-1)s^(-1).
```

If all fixed gates are nonidentity, their reduced stable-letter sign
sequences differ.  Equality is possible only after setting both sign-change
gates `y=E_0` and `u=A_1` to one (and then `v=x^(-1)`).  Those identity
coefficients freely cancel the two sign changes, so the equation is no longer
a reduced length-six candidate.

Thus the minimal second-side collision cannot be a direct equality of these
two bridges.  It must use a different sign type or transport a multi-generator
coefficient relation, and its coefficient image must lie nontrivially in one
copy rather than merely mix `G_0` and `G_1`.
