---
rg: 2
id: stw22-zero-dimensional-factor-bundles-have-uniform-traces
kind: claim
title: Every zero-dimensional factorial tracial bundle has only uniform traces
distinct_from:
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem selects weighted copies in one fixed hyperfinite factor; the present theorem works intrinsically in arbitrary finite-factor fibres and requires neither a trivialization nor hyperfiniteness.
  stw22-expectation-fields-have-uniform-traces: that theorem embeds all fibres in one ambient factor and assumes continuous variation of the fibre expectations; the present theorem removes both requirements by lifting and correcting weighted tuples inside the abstract bundle.
  stw22-finite-derived-set-factor-bundles-have-uniform-traces: that theorem permits arbitrary cardinality but only finitely many nonisolated points; the present theorem permits every compact zero-dimensional base, including perfect and arbitrarily high scattered bases.
artifacts:
  - research/artifacts/stw22-intrinsic-zero-dimensional-selection-audit-2026-08-30.md
---

Let `K` be a compact zero-dimensional Hausdorff space.  Let `M` be a
unital C*-algebra containing `C(K)` centrally, equipped with a faithful
unital tracial conditional expectation

```text
E:M -> C(K),
```

such that the operator-norm unit ball of `M` is complete for

```text
||a||_(2,u)=sup_(x in K) E(a*a)(x)^(1/2),
```

and every `2`-norm fibre

```text
M_x=M/{a:E(a*a)(x)=0}
```

is a finite factor.  Then every tracial state on `M` is uniquely

```text
a |-> integral_K E(a)(x) dmu(x)                         (ZFB1)
```

for a Radon probability measure `mu` on `K`.  In particular every trace
on `M` is continuous for the uniform `2`-norm.

Equivalently, the trace problem has a positive answer for every factorial
tracially complete C*-algebra whose compact base is zero-dimensional.  No
metrizability, separability, hyperfiniteness, property Gamma, complemented
partitions of unity, common ambient factor, local triviality, or bound on
Cantor--Bendixson height is assumed.

Consequently, if a unital separable nuclear C*-algebra `A` has a Bauer
trace simplex with zero-dimensional extreme boundary, then every trace on
its canonical uniform tracial completion is uniformly `2`-norm
continuous.  This includes every countable compact extreme boundary, all
compact scattered extreme boundaries, and perfect zero-dimensional
boundaries such as the Cantor space.
