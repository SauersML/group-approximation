---
rg: 2
id: one-bounded-type-coefficient-separates-unbounded-exits
kind: claim
title: One bounded-type coefficient separates a positive packet head from every unbounded-type exit
distinct_from:
  kazhdan-bounded-types-form-central-summand: that constructs the central projection selecting all bounded old-group types; this turns one finite group-algebra approximation to it into an explicit quantitative head-placement test.
  regular-trace-forbids-universal-bounded-type-placement: that rules out an exact universal carrier inclusion; this identifies the single coefficient residual that succeeds in finite matrices and simultaneously computes why it cannot be imposed as an ordinary exact relation.
  toeplitz-self-embedding-fixes-unbounded-congruence-types: that constructs exact stationary exits with zero bounded-type mass; this proves that every such exit carrying positive forbidden-head mass pays one fixed coefficient residual.
---

**ESTABLISHED CONDITIONAL SEPARATOR.**  Let `Lambda` be an infinite
property-`(T)` group, let

```text
p=p_<=K in C*_max(Lambda)
```

be the bounded-type central projection, and choose a selfadjoint finite
group-algebra coefficient `a in C[Lambda]` with

```text
||a-p||_max <= epsilon.                                  (BTC1)
```

Let `z` be a projection in a finite forbidden packet algebra.  In any
finite-dimensional representation `pi` of an ambient group containing the
packet and `Lambda`, put

```text
P=pi(p),       Z=pi(z),       q=tr(Z),
eta=||Z(1-pi(a))||_2.                                   (BTC2)
```

Then

```text
tr(P) >= q-(eta+epsilon sqrt(q))^2.                      (BTC3)
```

In particular, if `q>0` and `eta<=c sqrt(q)` with `c+epsilon<1`, then

```text
tr(P) >= (1-(c+epsilon)^2)q>0.                          (BTC4)
```

Thus one finite coefficient relation does exactly what the bounded-type
formulation of `parity-compressor-old-commutant-has-positive-density` asks:
small one-sided residual `Z(1-a)` converts positive forbidden-head mass into
positive bounded-type mass.  Every unbounded irreducible congruence stationary
exit has `P=0`, and hence necessarily

```text
eta >= (1-epsilon)sqrt(q).                              (BTC5)
```

The result does **not** close the group-presentation gate.  In the regular
representation `p` vanishes while every nonzero packet projection `z` has
positive trace, so the same lower bound `(BTC5)` holds there.  Consequently
`Z(1-a)=0` cannot be an ordinary exact coefficient consequence while the
packet and old group remain embedded.  Compiling its finite-matrix residual
into ordinary-word energy, while retaining the regular marked completion, is
already the sought matrix-only instability/nonhyperlinearity step.

