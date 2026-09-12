---
rg: 2
id: stw01-central-tail-quasitrace-splitting-proof
kind: route
title: Split central corners and descend an ultralimit of the complementary quasitraces
target: stw01-central-projection-ideal-extensions-preserve-qt-linearity
requires: []
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `tau` be a bounded `2`-quasitrace on `A` and put `r_n=1-p_n`.  Since
`p_n` is central,

```text
A=p_n A direct_sum r_n A.                                  (CP1)
```

The two summands are orthogonal and commute.  Hence for every self-adjoint
`x in A`, commuting additivity gives

```text
tau(x)=tau(p_n x)+tau(r_n x).                              (CP2)
```

The restriction of `tau` to `p_n A` is a bounded `2`-quasitrace and is a
trace by hypothesis.

Fix a free ultrafilter `omega` on the natural numbers and define

```text
sigma(a)=lim_(n -> omega) tau(r_n a).                       (CP3)
```

This is legitimately a bounded `2`-quasitrace on `A`.  Indeed
`a |-> r_n a` is a star homomorphism because `r_n` is central, so each
`tau(r_n -)` is a bounded `2`-quasitrace, uniformly bounded by the norm of
`tau`; all quasitrace axioms, including the `M_2(A)` extension and additivity
on commuting self-adjoints, pass through the scalar ultralimit.

If `i in I`, then `||r_n i|| -> 0` because `(p_n)` is an approximate unit
for `I`.  Norm continuity of bounded quasitraces gives
`sigma(i*i)=0`.  Thus `I` lies in the closed square-null ideal `N_sigma`.
By the standard trace-kernel factorization lemma, `sigma` factors as

```text
sigma=bar_sigma o q,               q:A -> A/I,              (CP4)
```

for a bounded `2`-quasitrace `bar_sigma` on `A/I`.  The quotient hypothesis
makes `bar_sigma`, and therefore `sigma`, a trace.

It remains to recover `tau`, without subtracting positive functionals.  For
self-adjoint `x,y`, apply `(CP2)` to `x`, `y`, and `x+y`.  Since
`tau|p_n A` is a trace, its three terms cancel and give the exact identity

```text
tau(x+y)-tau(x)-tau(y)
 =tau(r_n(x+y))-tau(r_n x)-tau(r_n y)                       (CP5)
```

for every `n`.  Take the `omega`-limit.  The right side becomes the
additivity defect of the trace `sigma`, hence is zero.  Therefore `tau` is
additive on all self-adjoint pairs.  Its complexification is linear, and
the quasitrace identity `tau(a*a)=tau(aa*)` makes it tracial.

Finally, the centrality boundary is exact.  If the compression
`a |-> (1-p)a(1-p)` is multiplicative, then for all `a`,

```text
(1-p)a p a*(1-p)=0.
```

Thus `(1-p)ap=0`; applying this to `a*` also gives `pa(1-p)=0`, so `p`
commutes with every `a`.  Conversely centrality plainly makes the cut a star
homomorphism.  For merely quasicentral `p_n`, the defect is
`(1-p_n)a p_n b(1-p_n)`, which tends to zero in norm but does not make
`a |-> tau((1-p_n)a(1-p_n))` a quasitrace at any finite stage.  No
quotient descent is asserted in that setting.
