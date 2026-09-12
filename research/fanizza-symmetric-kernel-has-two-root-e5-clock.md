---
rg: 2
id: fanizza-symmetric-kernel-has-two-root-e5-clock
kind: claim
title: The Fanizza symmetric frame has a two-root one-sided E5 rank clock
artifacts:
  - experiments/fanizza_symmetric_kernel_e5_clock.py
distinct_from:
  e5-heisenberg-word-realizes-rank-one-boundary-pulse: that moves both two-dimensional root coordinates and produces degree 4n-2 for the decomposable support kernel; this moves only the p-coordinate and produces degree 2n for the symmetric Fanizza kernel.
  paired-frame-moving-kernel-is-a-rank-one-veronese-clock: that moves a decomposable line through the Veronese conic; this moves the nondecomposable cross line e03+e12 by left multiplication.
---

Let `R=F_2[x]` and

```text
S=[[1+x^2,x],[x,1]],  T_L=diag(S,I_2) in GL_4(R).
```

For the Fanizza frame kernel

```text
K_0=span_R{e_01,e_23,e_03+e_12},
K_n=wedge^2(T_L^n)K_0,
```

write `S^n=[[a_n,c_n],[c_n,d_n]]`.  Then

```text
K_n=span_R{e_01,e_23,
  c_n e_02+a_n e_03+d_n e_12+c_n e_13}.                 (SKE1)
```

For `n>=1`, the last four coefficient degrees are

```text
(2n-1,2n,2n-2,2n-1).                                   (SKE2)
```

Thus distinct levels intersect in exactly the fixed two-dimensional core,
and the moving line has the unique top coefficient `e_03 x^(2n)`.

This transporter is an honest two-root word in `E_5(R)`.  In the `(2,1,2)`
upper Heisenberg block,

```text
D_L=e_01(x)e_10(x)=diag(S,1,I_2),                       (SKE3)
```

so conjugation moves the p-column by `S` and fixes the q-row.  For the
stationary atom-normalized hard form

```text
H=e_02^*+e_13^*,
Delta_n=H o wedge^2(T_L^n)+H,
```

`Delta_0=0`, while for `n>=1` its unique degree-`2n` coefficient is
`e_02^*`.  A relative character first nontrivial at that degree therefore
sees exactly one Pauli qubit.

By `(SKF5)`, every Fanizza escape is already `e_02^*` or becomes `e_02^*`
after the fixed simultaneous coordinate swap which preserves `K_0`.  Hence
the clock requires no atom-dependent additive-character decoder: all 26
finite escapes enter the same top-root coordinate and the same `J=+1`
reverse reservoir.

Finally, hold the coefficient commutator map fixed and transport only the
source map.  The combined map has rank three at level zero and rank four at
every positive level.  Its Smith invariants are

```text
(1,1,1,c_n),   deg c_n=2n-1.                            (SKE4)
```

Hence the full finite-frame discrepancy is one polynomial additive-character
coordinate, with a strictly increasing degree clock and only two stationary
relations.  No quotient by the union of the moving kernels is imposed.
