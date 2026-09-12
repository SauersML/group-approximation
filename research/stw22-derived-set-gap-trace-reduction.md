---
rg: 2
id: stw22-derived-set-gap-trace-reduction
kind: claim
title: Restriction to the derived set preserves exactly the bounded traces on a trivial-field fibre gap
distinct_from:
  stw22-height-three-scattered-trace-continuity: that theorem performs the two-level calculation explicitly at rank two; the present theorem isolates the successor-rank mechanism and iterates it through every finite Cantor--Bendixson rank.
  stw22-rank-one-scattered-fibre-gaps-are-tracefree: that theorem computes the rank-one gap as a cofinite corona; the present theorem shows that passing from a compact zero-dimensional base to its derived set introduces only a bounded-trace-free kernel.
artifacts:
  - research/artifacts/stw22-derived-set-gap-reduction-audit-2026-08-30.md
---

Let `X` be compact, metrizable, and zero-dimensional, put `Y=X^(1)`, and
let `x in Y`.  Let `U` be an infinite-dimensional UHF algebra with unique
trace and let `M(X)` and `M(Y)` be the uniform tracial completions of
`C(X) tensor U` and `C(Y) tensor U`.  Write

```text
I_x(X)=K_x(X)/J_x(X),
I_x(Y)=K_x(Y)/J_x(Y).
```

Restriction induces a surjective star homomorphism

```text
rho_x:I_x(X) -> I_x(Y).                                 (DSR)
```

Its kernel has no nonzero bounded positive trace.  Consequently pullback
along `rho_x` gives a bijection between bounded positive traces on the two
gap ideals.  In particular,

```text
I_x(X) is bounded-trace-free
  iff I_x(Y) is bounded-trace-free.                      (DSR-TF)
```

It follows by finite induction that if `X` is compact, metrizable, and
scattered, then the gap at every point of finite Cantor--Bendixson rank is
bounded-trace-free.  Hence every trace on the uniform completion of
`C(X) tensor U` is uniformly `2`-norm continuous whenever `X` has finite
Cantor--Bendixson height.

The theorem is a successor-rank reduction.  It does not cross a genuinely
limit Cantor--Bendixson rank, and it does not treat nontrivial tracial
bundles.
