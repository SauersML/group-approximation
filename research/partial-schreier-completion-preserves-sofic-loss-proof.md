---
rg: 2
id: partial-schreier-completion-preserves-sofic-loss-proof
kind: route
title: A completed word changes only when an intermediate point enters a missing generator domain
target: partial-schreier-completion-preserves-sofic-loss
requires: []
---

Because `|D_s|=|R_s|`, any bijection `D_s->R_s` extends to a permutation by
choosing an arbitrary bijection between the complements.

Fix a word

```text
w=s_1...s_L
```

and evaluate the completed composition from right to left (the convention is
irrelevant).  For each step `r`, the preceding completed maps form a
permutation of `X`.  Therefore the set of starting points whose intermediate
point immediately before applying `s_r` lies outside `D_(s_r)` has cardinality
exactly `|X\D_(s_r)|<=eta N`.  By the union bound, at most `L eta N` starting
points encounter any missing domain.  On every other starting point, each
completed generator agrees with the given partial bijection at every step, so
the completed and partial word values coincide.

For a tested equality `w=v`, apply this to both sides.  Outside the union of
the original `theta N` bad roots and the two word-exception sets, the completed
values still agree.  If both words have length at most `L_0`, the new bad set
has size at most

```text
(theta+2L_0 eta)N.
```

For a relator `w=e`, only the `w` exception set is needed, giving
`theta+L_0 eta`.  The same one-word estimate proves freeness: if the partial
word moves a root and no missing domain is encountered, its completion has the
same non-fixed value there.  Thus at most `theta+L_0 eta` of the completed
roots can be fixed.
