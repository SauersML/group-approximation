---
title: STW XCV checkpoint --- scattered-spectrum tensor localization (2026-08-30)
---

## Intrinsic local-to-global theorem

Let `B` be separable with topologically scattered primitive spectrum.  For
an arbitrary C*-algebra `A`, assume that every nonzero simple subquotient
`L` of `B` is nuclear and that `A tensor_min L` is pure.  Then

```text
A tensor_min B
```

is pure.

The point is that no filtration is supplied in the hypotheses.  Successive
isolated-point removal in `Prim(B)` canonically produces a continuous
ordinal ideal filtration with simple successor layers.  Nuclearity of each
layer makes the corresponding extension semisplit after tensoring by the
possibly nonexact algebra `A`.  Purity then propagates at successor stages,
while Cu continuity and separable stabilization handle limit stages.

## Concrete Problem XCV class

Suppose `A` is pure and is either simple or residually stably finite.  If
every simple subquotient of `B` is ASH, the Seth--Vilalta product theorem
verifies the local purity hypothesis, including for nonunital layers.  Thus
`A tensor_min B` is pure.  When `B` is itself pure, this gives a new positive
class for Problem XCV.

The conclusion is not a disguised ASH theorem for `B`: an arbitrarily long
extension tower of ASH simple layers need not itself be ASH.  Nor does the
argument infer Z-stability of `B`; only its scattered ideal topology and
the local product theorems enter.

## Trust boundary

Topological scatteredness is essential to this proof because it guarantees
a simple layer at every nonterminal stage.  If a nonempty residual primitive
subspace has no isolated point, the peeling stops and the argument supplies
no layer on which the local hypothesis can be applied.  Nuclearity is used
layerwise to preserve exactness of the tensor extension without assuming
that `A` is exact.
