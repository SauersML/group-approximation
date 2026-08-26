---
rg: 2
id: leavitt-compression-root-support-proof
kind: route
title: Compare the fixed root positions of Leavitt compression with the first Singer conjugate
target: leavitt-compression-preserves-root-position-support
requires:
  - leavitt-whitehead-20x20-compression-cell
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
---

For an elementary matrix `x_ab(r)=I+rE_ab`, `a!=b`, the definition of the
Leavitt compression gives

```text
alpha(x_ab(r))
 =p_1I+s_0(I+rE_ab)t_0
 =(p_1+s_0t_0)I+(s_0rt_0)E_ab
 =I+(s_0rt_0)E_ab.                                    (1)
```

This is `(LCR2)`.  In particular, an entry which is zero before compression
is zero afterwards, and every matrix fixing `e_7` for index-support reasons
still fixes `e_7` after applying `alpha` entrywise.

The signed-Hecke calculation supplies `d=x_28(1) in L_0` and shows that all
generators of `L_0` fix `e_7`.  Hence all of `alpha(L_0)` fixes `e_7`.
The same calculation gives `tdt^(-1)=x_27(1)`, which does not fix `e_7`.
This proves `(LCR5)`.

The map `alpha` is injective: multiplying its matrix value on the left by
`t_0I` and on the right by `s_0I` recovers the original matrix.  Therefore
the distinct terms in

```text
Q=|L_0|^(-1) sum_(h in L_0) lambda_0(h)^(-1)h
```

remain distinct after applying `alpha`, and its support is precisely
`alpha(L_0)`.  Conjugation by `t` gives support `tL_0t^(-1)`.  Unequal
supports prove `(LCR6)`.

Finally, on every block where the 20-by-20 Whitehead cell `T` implements
the compression endomorphism, `TQT^(-1)=alpha(Q)`.  Thus `TQ` has source
Gram `Q` and range Gram `alpha(Q)`, not `tQt^(-1)`.  Conjugating the entire
calculation by `t^k` proves the same failure at each moving stage.
