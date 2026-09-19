---
rg: 2
id: stw22-omega-power-rank-escape-core
kind: claim
title: The first limit-rank fibre gap reduces exactly to a nonzero escaping-rank core
distinct_from:
  stw22-derived-set-gap-trace-reduction: that theorem removes one successor Cantor--Bendixson layer and proves all finite-rank gaps trace-free; the present theorem takes the closure of all finite-layer kernels at the first limit ordinal and identifies the exact residual obstruction.
  stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap: that theorem gives a nonzero rank-one corona; the present quotient survives every finite derivative and records norm mass whose Cantor--Bendixson rank escapes to infinity.
artifacts:
  - research/artifacts/stw22-omega-power-rank-escape-audit-2026-08-30.md
---

Let

```text
X=[0,omega^omega],       x=omega^omega,
X_n=X^(n),               I_n=K_x(X_n)/J_x(X_n),
```

and let these gaps come from the uniform tracial completions of
`C(X_n) tensor U`, where `U` is an infinite-dimensional UHF algebra.  Let

```text
r_n:I_0 -> I_n
```

be restriction, put `L_n=ker(r_n)`, and define

```text
L_(<omega)=closure(union_(n<omega) L_n),
Q_omega=I_0/L_(<omega).                                 (ORE)
```

Then:

1. every `L_n`, and hence `L_(<omega)`, has no nonzero bounded positive
   trace;
2. pullback along `I_0 -> Q_omega` is a bijection from bounded positive
   traces on `Q_omega` to bounded positive traces on `I_0`;
3. `Q_omega` is nonzero.

Consequently the top fibre gap over `[0,omega^omega]` is bounded-trace-free
if and only if the explicit escaping-rank quotient `Q_omega` is
bounded-trace-free.  This is the exact first limit-height obstruction: no
bounded trace can live on any fixed finite Cantor--Bendixson layer, but
finite successor reduction alone does not exhaust the norm fibre gap.

The simplest nonzero projections in `Q_omega` still cannot support a
bounded trace.  Namely, let `U_k` be pairwise disjoint clopen sets converging
to `x`, with `U_k` containing a point of Cantor--Bendixson rank at least
`k`, and let `p_k in R` be projections with `tau(p_k)->0`.  The section

```text
p|_(U_k)=p_k,       p=0 off union_k U_k
```

defines a nonzero projection in `Q_omega` whenever infinitely many `p_k`
are nonzero, but every bounded positive trace on `Q_omega` annihilates it.
Thus a negative answer at the first limit rank cannot be obtained from a
cofinal packet of shrinking clopen projections.

The construction above isolates rather than by itself eliminates
`Q_omega`.  The subsequent weighted-selection theorem
`stw22-zero-dimensional-trivial-field-trace-continuity` proves that this
residual quotient is bounded-trace-free; the present theorem records why
finite derivative reduction alone could not show that.
