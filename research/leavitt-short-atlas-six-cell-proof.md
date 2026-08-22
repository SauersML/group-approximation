---
rg: 2
id: leavitt-short-atlas-six-cell-proof
kind: route
title: Add the missing q involution and commuting-root cells, then reduce the sole surviving mixed boundary by free-product normal form
target: leavitt-short-atlas-does-not-close-six-cells
requires:
  - leavitt-three-gate-square-picture-area-eight
---

Recall

```text
q=x_34(s_1)x_(11,12)(t_0).
```

The two roots are disjoint, so the factors commute.  In characteristic two
each elementary root element squares to one.  Hence `q^2=1`, proving the
previously omitted relation `k_1^2=1`.  The elements `a=x_12(s_0)` and
`e=x_12(t_1)` lie in the same abelian root subgroup, while both commute
with the two disjoint roots occurring in `q`.  This proves

```text
[h_0,h_2]=1,   [k_0,k_1]=1.                              (SCP1)
```

On the other hand `h_1=q_0p_1` and `k_2=p_0e_1` alternate between the two
free factors.  Every displayed syllable is nonidentity, so both words are
cyclically reduced of length two and have infinite order.  Thus `(SCA1)`
is the entire length-two involution and commuting-root atlas involving the
three nongate labels.

The six-cell ribbon census can now use the normal forms

```text
<h_0,h_2 | h_0^2,h_2^2,[h_0,h_2]>
  * <k_0,k_1 | k_0^2,k_1^2,[k_0,k_1]>
  * F(h_1,k_2).
```

The candidate count remains zero.  The three nearest coefficient words are
cyclic rotations of `(SCA2)`.  Expand one of them:

```text
h_0 h_1^(-1) h_2 h_1
 = a_0 p_1^(-1) q_0^(-1)e_0q_0 p_1.                     (SCP2)
```

Because `q_0` commutes with `e_0`, its reduced free-product normal form is

```text
(a_0) (p_1^(-1)) (e_0) (p_1).                           (SCP3)
```

All four syllables are nonidentity and consecutive syllables lie in
different free factors.  Hence `(SCP3)` is nontrivial.  Cyclic rotation
does not change triviality, so none of the three candidates closes.  The
two- and four-cell lower bound was already exhaustive, proving the stated
short-atlas exclusion through area six.
