---
rg: 2
id: soundness-unique-neighbors-give-erasure-cleaning
kind: claim
title: Linear soundness plus many unique neighbors gives common erasure cleaning
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that uses only one unique neighbor to prove a zero-versus-nonzero support statement; this uses quantitatively many unique neighbors to control the union of every erased-syndrome coset leader.
  collective-cofilling-is-common-erasure-cleaning: that identifies the target with collective cofilling; this gives an elementary Tanner-graph sufficient criterion.
---

Let `H:F_2^L -> F_2^M`, `C=ker(H)`.  Assume constants `a,alpha,gamma>0`
such that:

```text
for every x, some c in C has wt(x+c) <= a wt(Hx);         (SUN1)
for every U with 0<|U|<=alpha L,
  at least gamma|U| rows meet U in exactly one coordinate. (SUN2)
```

Then whenever

```text
|E| < min(alpha L/(2a), gamma alpha L/2),                (SUN3)
```

there is a single coordinate set `S(E)` with

```text
|S(E)| <= |E|/gamma,
ker(H_(rows outside E)) <= C+F_2^S(E).                   (SUN4)
```

Thus a bounded-degree family with `M=Theta(L)`, linear classical soundness,
and robust many-unique-neighbor expansion supplies exactly the cleaning
hypothesis needed for projective rounding.  Ordinary unique-neighbor
expander-code results and ordinary LTC soundness separately do not assert
that both properties hold for the same parity-check presentation; `(SUN1)`
plus `(SUN2)` is the precise combined construction target.
