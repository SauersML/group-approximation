---
rg: 2
id: stw01-qt-central-projection-extensions-preserve-linearity
kind: claim
title: Projectional extensions split when their commutators are universally quasitrace-null
distinct_from:
  stw01-central-projection-ideal-extensions-preserve-qt-linearity: that requires the approximate-unit projections to be central in A; this only requires centrality after passage to every bounded-quasitrace square-null quotient.
  stw01-qt-invisible-ideal-extension-principle: that requires every bounded quasitrace to annihilate the entire ideal; here only the projection commutators are universally null, and the ideal may carry nonzero traces.
  stw01-stable-ideal-extensions-force-qt-linearity: that makes the whole stable ideal quasitrace-null; this permits a traced central part of the ideal together with quasitrace-null noncentral noise.
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

For a unital C-star algebra `A`, define its bounded-quasitrace radical by

```text
J_bQT(A)=intersection_(tau in QT_b(A)) N_tau,
N_tau={x in A:tau(x*x)=0}.
```

Let `I triangleleft A` have an increasing approximate unit of projections
`(p_n)` satisfying

```text
[p_n,A] subset J_bQT(A)                         (n>=1).     (QTC1)
```

Suppose every bounded `2`-quasitrace on every nonzero corner `p_n A p_n`
is a trace, and every bounded `2`-quasitrace on `A/I` is a trace.  Then every
bounded `2`-quasitrace on `A` is a trace.

Condition `(QTC1)` says exactly that each `p_n` is central in every quotient
`A/N_tau` seen by a bounded quasitrace.  It is strictly weaker than
`p_n in Z(A)` and does not require `I subset J_bQT(A)`.

For example, let `K` be the compact operators, put

```text
A=C direct_sum K~,             I=C direct_sum K,
p_n=(1,e_n),
```

where `(e_n)` is an increasing finite-rank approximate unit for `K`.
The `p_n` are not central.  Their commutators lie in the stable ideal
`0 direct_sum K`, which every bounded quasitrace annihilates, so `(QTC1)`
holds.  The ideal `I` is not quasitrace-invisible because projection onto
its scalar summand is a nonzero bounded trace.  Each corner is
`C direct_sum M_(rank(e_n))` and the quotient is `C`, so the theorem applies.

For a fixed bounded quasitrace `tau` and projection `p`, `(QTC1)` is also the
exact algebraic threshold for the tail-cut argument: the map

```text
A -> (1-pi_tau(p))(A/N_tau),
a |-> (1-pi_tau(p))pi_tau(a)
```

is a star homomorphism if and only if `[p,A] subset N_tau`.  Thus no
approximate-commutation-to-exact-additivity principle is used.
