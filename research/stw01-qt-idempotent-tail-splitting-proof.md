---
rg: 2
id: stw01-qt-idempotent-tail-splitting-proof
kind: route
title: Turn positive cuts into central projections inside each quasitracial quotient
target: stw01-qt-idempotent-approximate-units-preserve-linearity
requires:
  - stw01-stable-algebras-are-bounded-quasitrace-invisible
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Fix a bounded `2`-quasitrace `tau` on `A`.  Factor it through its square-null
ideal:

```text
pi:A -> B=A/N_tau,                 tau=hat_tau o pi.
```

Condition `(QTI)` makes `q_n=pi(e_n)` a central projection in `B`.  Put
`r_n=1-q_n`.  For self-adjoint `x in A`, orthogonal commuting additivity gives

```text
tau(x)=hat_tau(q_n pi(x))+hat_tau(r_n pi(x)).                 (QTI1)
```

Because `q_n` is a projection and is central,

```text
hat_tau(q_n pi(x))=hat_tau(q_n pi(x)q_n)=tau(e_n x e_n).
```

The elements `e_n x e_n` lie in `Her_A(e_n)`.  The restriction of `tau` to
that hereditary algebra is a bounded `2`-quasitrace and hence is a trace by
hypothesis.  Therefore the first summand in `(QTI1)` is additive on
self-adjoint pairs.

For a free ultrafilter `omega`, define

```text
sigma(a)=lim_(n -> omega) hat_tau(r_n pi(a)).                 (QTI2)
```

Each map `a |-> r_n pi(a)` is a star homomorphism because `r_n` is central.
Consequently `(QTI2)`, together with the corresponding matrix-level formula,
is a bounded `2`-quasitrace.  If `i in I`, then

```text
r_n pi(i)=pi((1-e_n)i),             ||(1-e_n)i|| -> 0.
```

It follows that `sigma(i*i)=0`.  Hence `I subset N_sigma`, so `sigma`
factors through a bounded `2`-quasitrace on `A/I`; the quotient hypothesis
makes `sigma` a trace.

Apply `(QTI1)` to self-adjoint `x`, `y`, and `x+y`.  The hereditary terms
cancel by their tracial additivity.  Taking the ultralimit of the remaining
tail identity gives

```text
tau(x+y)-tau(x)-tau(y)=sigma(x+y)-sigma(x)-sigma(y)=0.
```

Thus `tau` is a trace.

For completeness, `(QTI)` is the exact algebraic threshold used above.  If
`0<=e<=1` and `q=pi(e)`, then `q` is a central projection exactly when

```text
e-e^2 in N_tau,                    [e,A] subset N_tau.
```

Equivalently, the `B`-valued tail map `a |-> (1-q)pi(a)` is a star
homomorphism.  Thus no estimate for approximately multiplicative cuts and no
additivity on approximately commuting elements is hidden in the proof.

To verify strictness, let `D=C_0((0,1]) tensor K`.  It is stable, so
`stw01-stable-algebras-are-bounded-quasitrace-invisible` applies.  It is also
stably projectionless: for any projection-valued section in a matrix algebra
over `D`, the nonzero set is clopen because its fibre norm lies in `{0,1}`,
and compact because the section vanishes at zero.  The connected noncompact
space `(0,1]` has no nonempty compact-open subset.

For `h_n(t)=min(1,nt)k_n`, the sequence `(h_n)` is an increasing positive
contractive approximate unit for `D`, and

```text
Her_D(h_n)=C_0((0,1]) tensor M_(rank(k_n)).
```

Every bounded `2`-quasitrace on this finite-homogeneous algebra is a trace.
In `A=C direct_sum D~`, all commutators and idempotence defects of
`e_n=(1,h_n)` lie in the quasitrace-null ideal `0 direct_sum D`.  The corner
and quotient hypotheses follow, while `I=C direct_sum D` has neither a
projectional approximate unit nor quasitrace invisibility.  This proves the
strictness assertion.
