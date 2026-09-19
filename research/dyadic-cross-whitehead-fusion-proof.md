---
rg: 2
id: dyadic-cross-whitehead-fusion-proof
kind: route
title: Split each cross matrix unit by its next suffix and multiply the orthogonal Whiteheads
target: dyadic-cross-whitehead-fusion-has-finite-product-gauge
requires:
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
  - individual-cross-whiteheads-miss-native-hecke-target
---

Insert `1=s_0t_0+s_1t_1` between the leading source and trailing target of
`p=s_0t_1` and `r=s_1t_0`.  This proves the first line of `(DCF2)`.
The other products follow from

```text
t_(ij)s_(kl)=delta_(i,k)delta_(j,l).                  (DCFP1)
```

For a partial inverse pair `ab=e`, `ba=f`, direct elementary multiplication
in characteristic two gives

```text
W(a,b)=[[1+e,a],[b,1+f]].                             (DCFP2)
```

Apply `(DCFP2)` to `(p_j,r_j)`.  Products between the `j=0` and `j=1`
blocks vanish by `(DCF2)`, while

```text
e_(00)+e_(01)=q_0,       e_(10)+e_(11)=q_1.          (DCFP3)
```

Multiplication therefore gives the coarse block
`[[q_1,p],[r,q_0]]`.  Reversing `p,r` gives the complementary coarse block,
proving `(DCF4)`.

Conjugating `x_28(1)` by an involutory block reads off its second row.  This
is `(DCF5)`.  Since `L_0` consists of matrices over the embedded `F_2`, the
displayed private matrix units exclude membership in `L_0`.

On ordered coordinates `(7,8)`, the native Whitehead block is

```text
J_1=[[1-q_0,y_1],[x_1,1-e_00]].                      (DCFP4)
```

For the row `(r_j,1+e_(1j))`, prefix cancellation gives

```text
r_j(1-q_0)=0,              (1+e_(1j))x_1=x_1,
r_jy_1=s_(1j)t_jt_00,
(1+e_(1j))(1-e_00)=1+e_(1j)+e_00.                    (DCFP5)
```

Substitution proves `(DCF6)`.  Its first coefficient `x_1` is already
nonconstant, so no cancellation in the second coefficient can change the
typing conclusion.  Multiplication on the left by the normalizer `v_1`
proves the Singer statement.

For the reversed row `(p_j,1+e_(0j))`, one similarly has

```text
p_jq_0=0,          p_jy_1=0,
e_(0j)x_1=delta_(j,0)x_1,
(1+e_(0j))(1+e_00)=
  {1+e_00 if j=0; q_1 if j=1}.
```

This gives `(DCF6b)` and closes both refined orientations.

The constant swap interchanges rows and columns in `(DCFP2)`, proving
`(DCF7)`.  Finally, the double transpositions in each copy of `S_4` form a
Klein four group, `d` exchanges `b,c`, and `de` is a three-cycle.  Direct
substitution verifies `(DCF8)--(DCF9)`.  Independent copies indexed by the
suffix leaves prove the fixed-depth extension.
