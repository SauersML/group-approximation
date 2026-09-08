---
rg: 2
id: finite-kernel-nonrf-has-central-prime-reduction
kind: claim
title: A non-residually-finite finite-kernel extension of an RF group reduces virtually to a central prime kernel
distinct_from:
  finite-central-extension-rf-iff-virtually-splits: that tests an already central extension for residual finiteness; this starts with an arbitrary finite kernel and constructs a prime central extension over a finite-index subgroup of the same base.
  finite-normal-quotient-residual-formula: that computes residuals after finite quotienting; this uses it after isolating the actual residual and centralizing the original kernel.
  hyperbolic-prime-torsion-residual-dichotomy: that studies the normal closure of an invisible torsion element; this assumes a finite kernel over an RF base and constructs a new extension whose entire residual has prime order.
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Let `1->K->E->H->1` be exact with `K` finite, `H` residually finite,
and `E` not residually finite. Set `R=R(E)`. Then `1<R<=Z(K)`, and there
exist a finite-index normal subgroup `L` of `E`, `H_0=image(L)` in `H`, a
prime `p`, and `B<=R` such that

```text
L intersect K = R <= Z(L),
R/B ~= C_p,
1 -> R/B -> L/B -> H_0 -> 1 is central,
R(L/B) = R/B,
[E:L] = [H:H_0] [K:R].
```

If `H` is word-hyperbolic, all total and base groups in these sequences
are word-hyperbolic. The complete proof is Section 3 of the artifact.

The statement is a conditional elementary reduction, with no novelty or
Lean-verification claim. It does not construct a non-residually-finite
hyperbolic group. In particular, the original RF-base and finite-kernel
hypotheses cannot be dropped.
