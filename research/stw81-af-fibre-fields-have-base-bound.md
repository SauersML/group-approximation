---
rg: 2
id: stw81-af-fibre-fields-have-base-bound
kind: claim
title: Every finite-dimensional-base C0-field with AF fibres has nuclear dimension at most the base dimension
distinct_from:
  stw81-continuous-simple-af-fields-have-base-bound: that theorem assumes a continuous field and unital fibres; the present result shows that neither continuity of norm functions nor unitality or simplicity of the fibres is needed.
  stw81-zero-dim-simple-fields-obey-trichotomy: that theorem allows arbitrary simple nuclear fibres but only a zero-dimensional base; the present theorem allows every finite-dimensional base and arbitrary ideal structure but uses AF fibres.
artifacts:
  - research/artifacts/stw81-usc-af-fibre-field-audit-2026-08-30.md
---

Let `X` be a second-countable locally compact Hausdorff space with
`dim(X)=n<infinity`, and let `A` be a separable `C_0(X)`-algebra.  No
continuity-field assumption is imposed: the fibre-norm functions are only
the upper-semicontinuous functions supplied by the definition of a
`C_0(X)`-algebra.  If every fibre `A_x` is AF, possibly zero or nonunital,
then

```text
dim_nuc(A) <= n.
```

Neither simplicity nor local triviality nor a locally constant fibre type is
required.  The previous continuous-unital AF-field theorem is a special
case.

If, in addition, every nonzero fibre is simple and non-elementary, then no
quotient of `A` has a nonzero commutative hereditary subalgebra.
Consequently, when `dim(X)<=1`, these upper-semicontinuous fields satisfy
the hypothesis and conclusion of Problem LXXXI.

The mechanism is local and exact.  A finite-dimensional approximation in a
single AF fibre has a star-homomorphic return map.  Semiprojectivity lifts
that return map to the restriction over a closed neighborhood.  Upper
semicontinuity shrinks the neighborhood on which it approximates the chosen
sections.  An `(n+1)`-decomposable base refinement and central cutoffs turn
the neighborhood homomorphisms into c.p.c. order-zero maps back to `A`.
