---
rg: 2
id: stw01-qt-radical-tail-splitting-proof
kind: route
title: Centralize each projection in the individual square-null quotient and descend the tail ultralimit
target: stw01-qt-central-projection-extensions-preserve-linearity
requires: []
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Fix a bounded `2`-quasitrace `tau` on `A`.  Its square-null set `N_tau` is a
closed two-sided ideal, and `tau` factors through a bounded `2`-quasitrace
`hat_tau` on

```text
B=A/N_tau.
```

Write `pi:A -> B`.  By `(QTC1)`, every `q_n=pi(p_n)` is a central projection
in `B`; put `r_n=1-q_n`.  For self-adjoint `x in A`, orthogonal commuting
additivity in `B` gives

```text
tau(x)=hat_tau(q_n pi(x))+hat_tau(r_n pi(x)).                (QTC2)
```

The first term equals `tau(p_n x p_n)`.  The restriction of `tau` to
`p_n A p_n` is a trace by hypothesis, so this first summand has zero
additivity defect.

Fix a free ultrafilter `omega` and define

```text
sigma(a)=lim_(n -> omega) hat_tau(r_n pi(a)).                (QTC3)
```

For every `n`, the map `a |-> r_n pi(a)` is a star homomorphism because
`r_n` is central in `B`.  Consequently the scalar functions in `(QTC3)`
are uniformly bounded `2`-quasitraces on `A`, including at the `M_2(A)`
level, and their ultralimit `sigma` is a bounded `2`-quasitrace.

If `i in I`, then `||(1-p_n)i|| -> 0`.  Therefore

```text
||r_n pi(i)|| <= ||(1-p_n)i|| -> 0,
```

and norm continuity gives `sigma(i*i)=0`.  Hence `I subset N_sigma`, so the
standard square-null factorization lemma produces a bounded `2`-quasitrace
`bar_sigma` on `A/I` with `sigma=bar_sigma o quotient`.  The quotient
hypothesis makes `sigma` a trace.

Apply `(QTC2)` to self-adjoint `x`, `y`, and `x+y`.  The `q_n`-corner terms
cancel because `tau|p_n A p_n` is a trace.  Thus, for every `n`,

```text
tau(x+y)-tau(x)-tau(y)
 =hat_tau(r_n pi(x+y))-hat_tau(r_n pi(x))-hat_tau(r_n pi(y)). (QTC4)
```

Taking the `omega`-limit turns the right side into the additivity defect of
the trace `sigma`, hence zero.  Thus `tau` is additive on all self-adjoint
pairs and is a trace.

To verify the claimed threshold, let `q=pi(p)`.  The tail cut
`a |-> (1-q)pi(a)` is multiplicative exactly when

```text
(1-q)pi(a)q pi(a*) (1-q)=0                         (a in A).
```

Positivity then gives `(1-q)pi(a)q=0`; applying this to `a*` gives the other
off-diagonal corner, so `q` is central in `B`.  This is equivalent to
`[p,A] subset N_tau`.  Mere norm-smallness of `[p_n,a]` would only make the
cuts asymptotically multiplicative and would not make their compositions
with `hat_tau` quasitraces.

**Trust boundary.**  The ambient quasitrace itself is factored only through
its own square-null ideal.  The tail ultralimit descends to `A/I` only after
its vanishing on `I` is proved.  No subtraction of quasitraces, quotient
descent of `tau`, or additivity on approximately commuting elements is
used.
