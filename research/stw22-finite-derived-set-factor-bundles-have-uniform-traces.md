---
rg: 2
id: stw22-finite-derived-set-factor-bundles-have-uniform-traces
kind: claim
title: Factorial tracial bundles over arbitrary compact bases with finite derived set have only uniform traces
distinct_from:
  trace-problem-holds-over-convergent-sequence-boundaries: that assumes a countable compact metric base and treats convergent sequences; this removes both countability and metrizability and permits one-point compactifications of discrete sets of arbitrary cardinality.
  stw22-norm-fibre-gap-is-the-trace-obstruction: that identifies the abstract norm-fibre gap; this proves directly that every such gap is bounded-trace-free when the base has only finitely many nonisolated points.
  stw22-expectation-fields-have-uniform-traces: that assumes a zero-dimensional metrizable base and a common ambient factor with continuously varying fibre expectations; this needs neither metrizability nor a common ambient representation.
artifacts:
  - research/artifacts/stw22-uncountable-cofinite-bundle-audit-2026-08-30.md
---

Let `K` be a compact Hausdorff space whose derived set `K'` is finite.  Let
`M` be a unital C*-algebra containing `C(K)` centrally and let

```text
E:M -> C(K)
```

be a unital tracial conditional expectation.  Assume that

```text
||a||_(2,u)=sup_(x in K) E(a*a)(x)^(1/2)
```

is faithful, that the operator-norm unit ball of `M` is complete for this
uniform `2`-norm, and that every `2`-norm fibre

```text
M_x=M/{a:E(a*a)(x)=0}
```

is a finite factor.  Then every tracial state on `M` is uniquely

```text
a |-> integral_K E(a)(x) dmu(x)                         (UCF1)
```

for a Radon probability measure `mu` on `K`.  In particular every trace is
continuous for the uniform `2`-norm.

No cardinality, first-countability, metrizability, separability, property
Gamma, or common-ambient-factor hypothesis is imposed.  In particular the
result applies over the one-point compactification of an arbitrary discrete
space.  Thus the countable convergent-sequence theorem is not the endpoint of
the cofinite orthogonal-replication argument.
