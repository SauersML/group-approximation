---
rg: 2
id: stw01-stable-ideal-extension-proof
kind: route
title: Kill a bounded quasitrace on the stable ideal and factor through its trace kernel
target: stw01-stable-ideal-extensions-force-qt-linearity
requires: []
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `tau` be a bounded 2-quasitrace on `A`; its restriction to `I` is a
bounded 2-quasitrace.  Stability supplies isometries `s_i in M(I)` with
pairwise orthogonal range projections.  For `a in I_+`, put

```text
a_i=s_i a s_i*,       i=1,...,n.
```

These elements are mutually orthogonal and commute.  Moreover they have
equal quasitrace: for `x=s_i a^(1/2) in I`, the defining identity gives

```text
tau(a)=tau(x*x)=tau(xx*)=tau(a_i).                      (SI2)
```

Commuting additivity and boundedness, with bound `C` on the positive unit
ball, now give

```text
n tau(a)=tau(sum_(i=1)^n a_i)
            <= C ||sum_(i=1)^n a_i||=C||a||.            (SI3)
```

Let `n` tend to infinity.  Thus `tau(a)=0` for every `a in I_+`.

For completeness, use the standard trace-kernel lemma for a bounded
2-quasitrace:

```text
N_tau={x in A: tau(x*x)=0}
```

is a closed two-sided ideal, and `tau` induces a bounded 2-quasitrace on
`A/N_tau`.  The ideal assertion follows from monotonicity,
`tau(x*x)=tau(xx*)`, and the quasitrace Cauchy--Schwarz/subadditivity
inequalities; those same inequalities show that changing a lift by an
element of `N_tau` does not change the induced quasitrace.  Since `tau`
vanishes on `I_+`, one has `I subset N_tau`.  The quotient map
`A/I -> A/N_tau` pulls the induced quasitrace back to a bounded
2-quasitrace `bar_tau` on `A/I`.  Therefore `tau` factors as

```text
tau=bar_tau q,       q:A -> A/I.                        (SI4)
```

for a bounded 2-quasitrace `bar_tau` on `Q`.  By hypothesis `bar_tau` is a
trace.  Equation `(SI4)` then makes `tau` a trace.
