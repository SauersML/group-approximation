---
rg: 2
id: first-cross-whitehead-return-equation-proof
kind: route
title: Solve the elementary and same-pair Whitehead return equations after K0
target: first-cross-whitehead-has-no-alternative-low-depth-return
requires:
  - individual-cross-whiteheads-miss-native-hecke-target
  - signed-hecke-normalizer-has-eight-external-root-returns
---

For `(CRQ3)`, use `v=r e_7^*+q_0e_8^*`.  Left multiplication changes the
column `e_2` only when `b=2`, while right multiplication changes `v` only
when `a` is `7` or `8`.  If `a=7,b=8`, the coefficient `r` at `(2,7)` is
unchanged; if `a=8,b=7`, the coefficient `q_0` at `(2,8)` is unchanged.
For any other `b`, right multiplication merely creates an extra column and
leaves both original columns.  If `b=2`, it creates extra rows but the
coefficient-one `e_2` component leaves the original row-two entries in
place.  Since `r,q_0` are nonconstant reduced Leavitt matrix units, the
result cannot lie in the constant matrix group `L_0`.  This proves `(CRQ4)`.

To prove first that a supported normalizer is constant, write its block as
`G=[[A,B],[C,D]]`.  Conjugation of the literal `L_0` root `x_79(1)` has
coefficients `A,C` in positions `(7,9),(8,9)`, while conjugation of
`x_86(1)` has coefficients `B,D` in positions `(7,6),(8,6)`.  Membership in
the constant matrix group `L_0` forces all four entries into the embedded
`F_2`.

Now inspect `h=x_28(1)`.  Of the six matrices in
`GL_2(F_2)` on `(7,8)`, precisely the identity and `x_78(1)` have second row
`(0,1)`.  Every other one sends `h` to a root product containing
`x_27(1)`, which is not in `L_0`.  The exact signed-root normalizer audit
shows that `x_78(1)` does preserve `(L_0,lambda_0)`.  This gives the claimed
intersection.

If `LK=N`, involutivity of `K` forces `L=NK`.  For `N=x_78(1)`, direct row
addition gives `(CRQ7)`.  Since

```text
(p+q_0)r=pr+q_0r=q_0,                                (CRQP1)
```

the necessary Whitehead diagonal identity gives `(CRQ8)` and the
contradiction.

Finally write the native block as

```text
J_1=[[q_1,y_1],[x_1,1+e_00]].                        (CRQP2)
```

Multiplying `J_1K` gives upper-left `q_1`, upper-right `y_1`, and
lower-left `r`.  Inserting `x_78(1)` between `J_1` and `K` changes the
upper-left entry to `q_1+r` but leaves those two off-diagonal entries.
Prefix cancellation gives `y_1r=0`.  A block of the form `(CRQ5)` must have
upper-left entry `1+L_12L_21=1`, which proves `(CRQ11)` and completes the
return classification.
