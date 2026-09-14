---
rg: 2
id: zero-divisor-supports-have-no-quasimorphism-isolated-extremes
kind: claim
title: No homogeneous quasimorphism separates one point of a zero divisor's support from the others by more than twice its defect
distinct_from:
  zero-divisor-support-vertex-cones-contain-positive-relations: that gives positive relations among the left differences at each support point; this turns them into a quantitative obstruction for every homogeneous quasimorphism.
  small-non-up-left-support-has-no-orderable-quotient: that forbids a strict minimum under an orderable quotient; this forbids a strict minimum under any homogeneous quasimorphism, up to twice its defect.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is an established necessary condition on the support of a counterexample.
---

**ESTABLISHED.** A *homogeneous quasimorphism* on a group `G` is a function
`phi: G -> R` with `phi(g^m) = m phi(g)` for all `g in G`, `m in Z`, and finite
defect `D(phi) = sup_(g,h) |phi(gh) - phi(g) - phi(h)|`.

Let `G` be torsion-free, `k` a field, and `alpha in k[G]` a left or right zero
divisor (`alpha beta = 0` or `beta alpha = 0` with `beta != 0`), with support
`A`. Then for every homogeneous quasimorphism `phi` on `G`, with `D = D(phi)`,
there is no `a in A` with

```text
phi(c) - phi(a) > 2D for all c in A \ {a},   or   phi(a) - phi(c) > 2D for all c in A \ {a}.
```

So the values of `phi` on `A` have neither a minimum nor a maximum separated
from all other values by more than `2D`. With `D = 0` this recovers the
statement that no homomorphism to `R` has a strict minimum or maximum on `A`.

*Scope.* Elementary, given the positive relations of
`zero-divisor-support-vertex-cones-contain-positive-relations`. No novelty is
claimed.

DERIVATION
[[zero-divisor-quasimorphism-isolated-extremes-proof]]
