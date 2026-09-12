---
rg: 2
id: stw22-zero-dimensional-trivial-field-trace-continuity
kind: claim
title: Every trivial UHF field over a zero-dimensional compact metric base has only uniform traces
distinct_from:
  stw22-omega-power-rank-escape-core: that theorem isolates a nonzero residual quotient after all finite derivative layers; the present theorem kills every bounded trace on that quotient by a selection argument which does not use Cantor--Bendixson rank.
  stw22-derived-set-gap-trace-reduction: that theorem removes one derived layer and therefore stops at limit rank; the present theorem instead continuously embeds each small spectral cut into fixed orthogonal factor corners.
  stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap: that theorem makes independent choices at isolated coordinates; the present theorem permits support jumps over an arbitrary zero-dimensional compact metrizable base by selecting weighted partial isometries rather than support projections.
artifacts:
  - research/artifacts/stw22-zero-dimensional-weighted-selection-audit-2026-08-30.md
---

Let `X` be compact, metrizable, and zero-dimensional, let `U` be an
infinite-dimensional UHF algebra with unique trace, and let `M` be the
uniform tracial completion of

```text
C(X) tensor U.
```

Then every norm/`2`-norm fibre gap `K_x/J_x` has no nonzero bounded positive
trace.  Consequently every tracial state on `M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and is continuous for the uniform
`2`-norm.

More precisely, let `c in K_x` be a positive contraction for which

```text
sup_(t in V) tau(supp(c(t))) < 1/m                      (ZDS)
```

on a clopen neighbourhood `V` of `x`.  There are
`v_1,...,v_m in K_x`, supported on `V`, such that

```text
v_j^*v_j=c,
(v_i v_i^*)(v_j v_j^*)=0       (i!=j)                  (ZDO)
```

in the fibre gap.  The construction does not select the jumping support
projections continuously.  It selects the weighted operators
`u_j c^(1/2)` into fixed orthogonal corners; low-spectrum jumps are then
small in `2`-norm, and zero-dimensional clopen refinement gives a global
section.

In particular the escaping-rank quotient `Q_omega` of
`stw22-omega-power-rank-escape-core` is bounded-trace-free.  Thus the first
limit-height trivial-field model `[0,omega^omega]` does not produce a
singular trace.

This theorem concerns the trivial hyperfinite-factor bundle.  It does not
assert the same weighted selection for a nontrivial tracial bundle.
