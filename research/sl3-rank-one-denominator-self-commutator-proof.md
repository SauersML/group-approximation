---
rg: 2
id: sl3-rank-one-denominator-self-commutator-proof
kind: route
title: Expand the rank-one Weyl decomposition and telescope the relative commutator
target: sl3-rank-one-denominator-self-commutator-removes-target-phase
requires: []
---

In the `(1,3)` coordinate plane define

```text
w(r)=x(r)y(-r^(-1))x(r).
```

Direct multiplication gives

```text
w(r)=[[0,r],[-r^(-1),0]],
w(2)w(-1)=diag(2,1/2).
```

After restoring the middle coordinate this is

```text
h=x(2)y(-1/2)x(2)C.
```

Conjugation by `h` sends `y(r)` to `y(r/4)`, so
`y(-1/2)=h y(-2)h^(-1)`.  This proves `(RSC1)`.

First suppose all displayed identities and commutations are exact.  Since
`U` commutes with `Y`,

```text
U Z U^*
 =U H Y H^*U^*
 =W H Y H^* W^*
 =W Z W^*.
```

Conjugating `(RSC1)` by `U`, using commutation with `X,C`, and then
multiplying by `H^*` gives

```text
W
 =X W Z W^* Z^* X^*
 =X[W,Z]X^*,
```

which is `(RSC2)`.

For the robust estimate, put `R=XZXC`.  Replacing the two occurrences of
`H` in `UHU^*H^*` by `R` costs at most `2 eta`.  In

```text
U R U^* R^*
 =U X Z X C U^* C^* X^* Z^* X^*,
```

move `U` through the first `X`, and move `U^*` back through `C` and the
second `X`.  These three moves cost

```text
2 epsilon_X+epsilon_C
```

and leave `X[U,Z]X^*`.  The displayed exact calculation comparing
`UZU^*` with `WZW^*` used only `UY=YU`; without that equality the error is
at most `epsilon_Y`.  This proves `(RSC3)`.

Choose `z in T` with `z tr(W)>=0`.  Then

```text
||W-zI||_2^2
 =2-2|tr(W)|
 <=2(1-|tr(W)|^2)=2e_h.
```

Because scalar phases cancel in a commutator,

```text
||[W,Z]-I||_2 <=2||W-zI||_2 <=2 sqrt(2e_h).
```

Combining this with `(RSC3)` proves `(RSC4)`.  Finally, fixed-word
telescoping bounds `eta` by a constant times the presentation defect, and
`(PTS4)` bounds the three integral-word commutators by a constant times
`sqrt(q_Lambda)+delta`.  This proves `(RSC5)`.

