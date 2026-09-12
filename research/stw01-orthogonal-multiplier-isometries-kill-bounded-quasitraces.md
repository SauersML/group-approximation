---
rg: 2
id: stw01-orthogonal-multiplier-isometries-kill-bounded-quasitraces
kind: route
title: Amplify one positive element along orthogonal multiplier isometries
target: stw01-stable-algebras-are-bounded-quasitrace-invisible
requires: []
---

Let `tau` be a bounded `2`-quasitrace on the stable algebra `S`.  Stability
provides, for every `n`, isometries `s_1,...,s_n in M(S)` with pairwise
orthogonal range projections.  For `a in S_+`, put

```text
a_i=s_i a s_i*,       i=1,...,n.
```

The `a_i` are mutually orthogonal and therefore commute.  They have equal
quasitrace: with `x=s_i a^(1/2) in S`, the quasitrace identity gives

```text
tau(a)=tau(x*x)=tau(xx*)=tau(a_i).                     (1)
```

Let `C` be a bound for `tau` on the positive unit ball.  Orthogonality gives
`||sum_i a_i||=||a||`, while commuting additivity and boundedness give

```text
n tau(a)=tau(sum_(i=1)^n a_i)
          <= C ||sum_(i=1)^n a_i||=C||a||.             (2)
```

Since (2) holds for every `n`, `tau(a)=0`.  Thus `tau` vanishes on `S_+` and
hence is zero.  The multiplier isometries need not belong to `S`; the
products `s_i a^(1/2)` and `s_i a s_i*` do, because `S` is an essential
ideal in `M(S)`.

**Trust boundary.**  The standard stability input is the existence of
arbitrarily many orthogonal multiplier isometries.  The rest uses only
`tau(x*x)=tau(xx*)`, additivity on commuting positive elements, and boundedness.
