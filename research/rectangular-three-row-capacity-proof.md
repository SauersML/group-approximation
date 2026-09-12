---
rg: 2
id: rectangular-three-row-capacity-proof
kind: route
title: Compare the two rectangular ranges by their positive Gram sum
target: rectangular-three-row-cell-forces-double-target-capacity
requires: []
---

First compare the first return with the Hilbert adjoint of its forward map.
Using the trace to expand the other square gives

```text
||t_0-s_0^*||_2^2
 =tau(t_0t_0^*)+tau(s_0^*s_0)-2 Re tau(t_0s_0).
```

Both positive terms are at most `q`, while Cauchy--Schwarz and `(RTC1)` give

```text
Re tau(t_0s_0)>=q-sqrt(q)epsilon_0.
```

Therefore

```text
||t_0-s_0^*||_2^2<=2sqrt(q)epsilon_0.                 (RTP1)
```

Contraction by `s_1` and the crossed row now show

```text
c:=||s_0^*s_1||_2
 <=sqrt(2sqrt(q)epsilon_0)+eta.                        (RTP2)
```

The diagonal rows also imply

```text
||s_i||_2>=||t_is_i||_2>=sqrt(q)-epsilon_i,
```

so, with negative lower bounds interpreted harmlessly,

```text
tau(s_i^*s_i)>=q-2sqrt(q)epsilon_i.                    (RTP3)
```

Put

```text
A=s_0s_0^*+s_1s_1^* in F M F.
```

Then `(RTP3)` gives

```text
tau(A)>=2q-2sqrt(q)(epsilon_0+epsilon_1).              (RTP4)
```

Since each `s_i` is a contraction,

```text
tau(A^2)
 =tau((s_0^*s_0)^2)+tau((s_1^*s_1)^2)
   +2||s_0^*s_1||_2^2
 <=tau(A)+2c^2.                                       (RTP5)
```

The support of `A` lies under `F`, so Cauchy--Schwarz yields

```text
tau(A)^2<=r tau(A^2).
```

For `x,y>=0`, `x^2/(x+y)>=x-y`.  Combining this scalar inequality with
`(RTP4)--(RTP5)` gives

```text
r>=tau(A)-2c^2
 >=2q-2sqrt(q)(epsilon_0+epsilon_1)-2c^2.              (RTP6)
```

Finally `(RTP2)` and `(a+b)^2<=2a^2+2b^2` imply

```text
2c^2<=8sqrt(q)epsilon_0+4eta^2.
```

Substitution in `(RTP6)` is exactly `(RTC2)`.

Under `(RTC5)`, rearranging `(RTC2)` proves `(RTC6)`.  If all three row
defects are at most `delta` and `zeta<=c delta^2`, put `x=sqrt(q)` to obtain

```text
kappa x^2<=12delta x+(4+c)delta^2.
```

The positive root of this quadratic is `(RTC7)`.
