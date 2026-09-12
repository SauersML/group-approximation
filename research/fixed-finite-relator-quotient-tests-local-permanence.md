---
rg: 2
id: fixed-finite-relator-quotient-tests-local-permanence
kind: claim
title: One fixed finite-relator quotient tests quotient permanence for every local approximation property containing F2
distinct_from:
  universal-local-approximation-fixed-two-generator-test-group: that identifies one fixed group whose membership is equivalent to universal membership; this adds the equivalence with arbitrary quotient permanence and shows that one fixed finite-relator quotient is a complete permanence test.
  hyperlinear-quotient-permanence-equivalence: that treats only hyperlinearity and uses free groups of unrestricted rank; this works uniformly for every local approximation property containing F2 and uses one fixed quotient of the rank-two free group.
  sofic-quotient-nonclosure: that is the known negative sofic specialization; this is the uniform theorem whose hyperlinear, weak-sofic and fieldwise linear-sofic values remain exact open horns.
  mf-quotient-nonclosure: that records a concrete rank-eight MF counterexample; this uniform theorem sharpens the MF specialization to the same fixed finite-relator quotient of F2.
artifacts:
  - GroupApproximation/Sofic/FreeGroupResiduallyFinite.lean
  - GroupApproximation/Sofic/HyperlinearReduction.lean
  - GroupApproximation/Sofic/LEFSofic.lean
---

There are one fixed two-generator finitely presented group `V`, one fixed
finite set `R subseteq F_2`, and an epimorphism

```text
pi : F_2 ->> V,
ker(pi)=<<R>>,
V = <a,b | R>,
```

with the following simultaneous property. Let `P_M` be any local
approximation property covered by
[[local-approximation-properties-are-marked-closed]], and assume
`P_M(F_2)`. Then the following are equivalent:

```text
P_M(V),
P_M(G) for every group G,
P_M is closed under arbitrary quotients.
```

Thus the single quotient `pi` is a complete test for quotient permanence:
if `P_M(V)` fails, `pi` itself is a finite-relator counterexample; if
`P_M(V)` holds, every group has `P_M`, so quotient permanence is
automatic. The group `V`, the presentation, and the quotient are fixed
before `M` is chosen.

For the named approximation properties this has two kinds of consequence.

- `V` is already known to be nonsofic and non-MF. Since `F_2` is
  residually finite, the same `pi` simultaneously refutes quotient closure
  for LEF, soficity, and operator-MF. For LEF, use that LEF implies sofic.
- The remaining values are exact reductions, not solved horns:

  ```text
  V is hyperlinear
    <=> hyperlinearity is closed under arbitrary quotients,

  V is weakly sofic
    <=> weak soficity is closed under arbitrary quotients,

  V is linear sofic over k
    <=> linear soficity over k is closed under arbitrary quotients
                                                    (for each field k).
  ```

  The same `V` is used for every field `k`; no existential choice of
  field is intended. If `V` is hyperlinear, its known nonsoficity makes it
  a fixed two-generator finitely presented witness for
  [[hyperlinear-nonsofic-group]]. If `V` is not hyperlinear, it is instead
  a fixed finitely presented witness for [[non-hyperlinear-group]], and
  `pi` is a finite-relator counterexample to hyperlinear quotient
  permanence. Neither alternative is asserted here.

**ESTABLISHED 2026-08-31** by
[[fixed-finite-relator-quotient-local-permanence-proof]].
