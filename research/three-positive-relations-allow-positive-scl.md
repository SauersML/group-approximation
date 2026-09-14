---
rg: 2
id: three-positive-relations-allow-positive-scl
kind: claim
title: The three positive relations of a support-three zero divisor are compatible with nonzero quasimorphisms on all three differences in a torsion-free hyperbolic group
distinct_from:
  support-three-zero-divisor-quasimorphism-bound-five-thirds: that bounds quasimorphisms on the differences using the positive relations; this shows those relations cannot force the values to vanish.
  zero-divisor-support-vertex-cones-contain-positive-relations: that derives the positive relations from a zero divisor; this realizes all three relations in a group where quasimorphisms do not vanish on the differences.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that is the open nonexistence statement in hosts containing the torsion-free hyperbolic groups; this is a no-go for proving it from the positive relations and quasimorphism inequalities alone.
artifacts:
  - research/artifacts/hl-zd-amplification-2026-09-13.md
---

**ESTABLISHED.** Let `G = <x, y | R_1, R_2, R_3>`, writing `X = x^-1`, `Y = y^-1`:

```text
R_1 = xxyyyxxyyxyyyxxyxxxyyxxxxyxyxyyyxxxyxxxyyyyxxxyxyyyxxxyyyyxxxxyyyyxyyxxxxyyyy
R_2 = xxYxYxYxxYxYxYxxYxYxYxYxxYxYxYxYxxxxYxxxxYxYxYxxxxxYxYxYxxxxYxxxxYxxxxxYxYxYxxYxYxYxxxYxYxxxYxYxYxxxxxYxxYxYxxxxYxYxYxYx
R_3 = yyyXyXyyyyyXyXyXyXyyyyXyXyyXyyyXyXyXyXyyyyXyyyyXyXyXyyyyyXyyyXyyyyyXyXyXyyyXyXyXyyyyXyXyXyXyyyyyXyyyyXyXyXyXyyXyXyyyyXy
```

of lengths `77`, `120`, `119`. Then:

1. *The relations.* `R_1` is a positive word in `x, y`; `R_2` is a positive word in the
   two elements `x` and `y^-1 x`; `R_3` is a positive word in `y` and `x^-1 y`; each uses
   both. So `G` has positive relations using both letters among each of
   `{x^-1, y^-1}`, `{x, y^-1 x}` and `{y, x^-1 y}`: exactly the three relations of
   consequence 4 of `zero-divisor-support-vertex-cones-contain-positive-relations`.
2. *The group.* The presentation is classical `C'(1/6)`: the longest pieces have lengths
   `11`, `17`, `17`, at most `1/7` of the relator lengths, and no relator is a proper
   power. So `G` is torsion-free and word-hyperbolic with an aspherical presentation
   complex; `H_1(G; Z) = 0` and `b_2(G) = 1`.
3. *Quasimorphisms.* `x`, `y`, `x^-1 y` are nontrivial, some homogeneous quasimorphism
   on `G` is nonzero on all three, and each of them has positive stable commutator
   length.

**Consequence (barrier).** The proofs of
`support-three-zero-divisor-differences-bounded-quasimorphism` and
`support-three-zero-divisor-quasimorphism-bound-five-thirds` use only torsion-freeness,
these three positive relations and the defect inequality. All of that holds in `G` while
quasimorphisms do not vanish on the differences. So no argument with only those inputs
can prove the amplification target of `research/artifacts/hl-zero-divisor-2026-09-13.md`
§4 (`phi = 0` on the differences), nor derive a contradiction in a torsion-free
hyperbolic host. Any proof of `cyclic-centralizer-groups-have-no-support-three-zero-divisors`
through quasimorphisms must use the finite cofactor `B` beyond its cycle relations.
In `G` the bounds give `0 < scl <= 5/6` on the three elements.

*Scope.* The presentation was found by random search and certified by two independent
exact programs (artifact). No zero divisor in `k[G]` is claimed or excluded. No novelty
is claimed.

DERIVATION
[[three-positive-relations-positive-scl-small-cancellation-proof]]
