# Short exact coefficient relations for the length-six Leavitt candidate

## Labels

The star graph has coefficient corners

```text
h_0=a_0,  h_1=q_0p_1,  h_2=e_0,
k_0=a_1,  k_1=q_1,     k_2=p_0e_1,
```

inside `G_0*G_1`, where

```text
a=x_12(s_0),
e=x_12(t_1),
q=x_34(s_1)x_(11,12)(t_0).
```

## Root-calculus atlas

Characteristic two makes every elementary root element an involution.
The two roots in `q` are disjoint, so they commute and `q^2=1`.  Thus the
short torsion list contains `k_1^2=1` in addition to the three original
gate squares.

The elements `a` and `e` occupy the same root subgroup and commute.  Both
also commute with `q`, whose root supports are disjoint.  The label-level
relations visible at the shortest scale are therefore

```text
h_0^2=h_2^2=k_0^2=k_1^2=1,
[h_0,h_2]=[k_0,k_1]=1.
```

In contrast, `h_1=q_0p_1` and `k_2=p_0e_1` are cyclically reduced
two-syllable words in the free product and consequently have infinite
order.  No missing power relation exists for either mixed bridge.

## Six-face test

Using the enlarged normal form

```text
V_4(h_0,h_2) * V_4(k_0,k_1) * F(h_1,k_2)
```

in the already complete six-vertex ribbon census still gives no disk.  The
only closest words, up to cyclic rotation, are

```text
h_0 h_1^(-1) h_2 h_1.
```

In the actual coefficient free product this is

```text
a_0 p_1^(-1) q_0^(-1)e_0q_0 p_1
 =a_0 p_1^(-1)e_0p_1.
```

The latter has four nonidentity alternating syllables, hence is reduced and
nontrivial.  Therefore the omitted involution and commuting-root cells do
not create a six-face boundary relation.

The remaining logical possibility is sharply fenced: any six-face kernel
picture must exploit one or more longer coefficient identities not generated
by this shortest atlas.  Pure squares, the missing `q` square, and all
immediate commuting-root relations are exhausted.
