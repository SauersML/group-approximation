---
rg: 2
id: fixed-finite-relator-quotient-local-permanence-proof
kind: route
title: Combine the universal tester with one rank-two presentation map
target: fixed-finite-relator-quotient-tests-local-permanence
requires:
  - universal-local-approximation-fixed-two-generator-test-group
  - fp-quotient-iff-kernel-finitely-normally-generated
  - sofic-implies-hyperlinear
  - mf-positive-controls
  - weak-soficity-recognition-has-a-pi2-upper-bound
  - linear-soficity-recognition-has-a-pi2-upper-bound
artifacts:
  - GroupApproximation/Sofic/FreeGroupResiduallyFinite.lean
  - GroupApproximation/Sofic/HyperlinearReduction.lean
  - GroupApproximation/Sofic/LEFSofic.lean
---

Choose the fixed two-generator finitely presented group `V` of
[[universal-local-approximation-fixed-two-generator-test-group]], fix two
generators, and let `pi:F_2->>V` be the induced epimorphism. Since both
`F_2` and `V` are finitely presented,
[[fp-quotient-iff-kernel-finitely-normally-generated]] gives a finite set
`R subseteq F_2` with `ker(pi)=<<R>>`. This fixes
`V=<a,b | R>` independently of every model predicate.

Now fix a local approximation property `P_M` with `P_M(F_2)`. The
universal tester gives

```text
P_M(V) <=> P_M(G) for every group G.
```

If `P_M(V)` holds, every group has `P_M`, so `P_M` is tautologically
closed under arbitrary quotients. Conversely, if `P_M` is quotient-closed,
apply it to `pi` and `P_M(F_2)` to obtain `P_M(V)`. This proves all
three conditions equivalent and proves that failure is witnessed by the
one fixed finite-relator quotient `pi`.

The hypothesis `P_M(F_2)` holds in every named case. The free group
`F_2` is residually finite, hence LEF and sofic; it is operator-MF by
[[mf-positive-controls]], hyperlinear by [[sofic-implies-hyperlinear]], and
weakly sofic. Permutation matrices over any field make it linear sofic over
that field, as recorded in
[[linear-soficity-recognition-has-a-pi2-upper-bound]]. The upstream universal
tester proves that `V` is nonsofic and non-MF, while LEF implies sofic.
These facts give the negative LEF/sofic/MF specializations. Applying the
three-way equivalence without deciding `P_M(V)` gives exactly the displayed
hyperlinear, weak-sofic, and fieldwise linear-sofic reductions. QED
