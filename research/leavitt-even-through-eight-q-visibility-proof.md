---
rg: 2
id: leavitt-even-through-eight-q-visibility-proof
kind: route
title: Screen every Q-nontrivial even necklace by exact free-factor moved-vector witnesses
target: leavitt-even-relations-through-eight-are-q-visible
requires: []
---

Generate cyclically formally reduced necklaces at lengths two, four, six,
and eight, modulo rotation and inversion.  Discard the words trivial in the
free-product normal form of `Q`.  Expand every remaining word under

```text
h_1=q_0p_1,  k_2=p_0e_1
```

and reduce maximal `G_0` and `G_1` syllables by the commuting-root relations.
The faithful infinite-word module supplies an explicit moved basis vector
for every nonempty reduced syllable.  MSI certifies respectively
`18`, `332`, `10014`, and `361656` Q-nontrivial orbit representatives, with
zero extra identities and zero unwitnessed blocks.  Hence no even identity
through length eight lies outside `Q`.
