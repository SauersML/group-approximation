---
rg: 2
id: leavitt-nielsen-collision-has-a-hidden-first-side-relation
kind: claim
title: The collided corner group has a hidden Steinberg relation, but it is not yet a coefficient-boundary filling
artifacts:
  - research/leavitt-nielsen-collision-has-a-hidden-first-side-relation-proof.md
  - research/artifacts/verify-leavitt-nielsen-collision-red-team.py
distinct_from:
  leavitt-length-six-nielsen-collision-candidate: that finds the formal equality k0=k1; this finds a second, genuinely Leavitt relation in the folded first corner group and audits its image after Tietze elimination.
  kl-violating-equation-over-leavitt-unit-group: that requires a nontrivial coefficient word to die in the relative quotient; the relation here is already trivial in the coefficient group and its Tietze image still contains the bridge letter.
---

For the collided word, put `r=qp`.  The actual corner subgroup contains

```text
u=a_1,             b=h_0h_1=(qp)_1=r_1.
```

It has the exact relation

```text
Omega=[u,b^2 u b^(-2)]=1.
```

The corresponding word is nontrivial in the formal group
`<u,b | u^2=1> = C_2*Z`.  Thus folding `k_0=k_1` does not repair the first
corner map: even the tempting replacement of its copy-one vertex group by
`C_2*Z` is not injective.

After eliminating the two bridge corners with `s=z^(-1)`, the image of
`Omega` is a nonempty reduced word with 49 alternating free-product
syllables, 24 of them nonzero powers of `s`.  Consequently this hidden
relation is not by itself a coefficient-boundary word.  It supplies an exact
additional internal face for a future relative-picture search, but does not
prove that a nontrivial coefficient dies and therefore does not establish a
Kervaire--Laudenbach violation.
