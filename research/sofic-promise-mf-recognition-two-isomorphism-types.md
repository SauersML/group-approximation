---
rg: 2
id: sofic-promise-mf-recognition-two-isomorphism-types
kind: claim
title: MF recognition is Pi-zero-two complete on a computable family of sofic groups with only two isomorphism types
artifacts:
  - GroupApproximation/Computability/SoficPromiseTwoType.lean
  - GroupApproximation/Computability/SoficPromiseMFRecognition.lean
distinct_from:
  sofic-recognition-under-hyperlinear-promise-dichotomy: that promises hyperlinearity and asks about soficity, and is open exactly as Pestov's question; this promises soficity and asks about MF, and is unconditional because the literal non-MF group is sofic.
  mf-recognition-recursive-presentations-is-second-level-complete: that classifies MF on all recursive presentations; this restricts the inputs to a computable family every member of which is sofic and isomorphic to one of two fixed groups, and shows the level does not drop.
---

ESTABLISHED (route `sofic-promise-mf-recognition-two-isomorphism-types-proof`;
Lean `Computability/SoficPromiseTwoType.compiled_two_isomorphism_types`,
`Computability/SoficPromiseMFRecognition.sofic_promise_recognition_package`).
There is a computable `compile : Code -> PresentationCode` into enumerated
presentation codes such that every `G_c = Carrier(compile(c))` is sofic and

```text
InfiniteDomain(c)  =>  G_c ~= 1,
FiniteDomain(c)    =>  G_c ~= E,
```

with `E` the fixed literal sofic non-MF group.  Hence operator-MF
recognition is `Pi^0_2`-complete and non-MF recognition
`Sigma^0_2`-complete already under the promise that the input is sofic
(indeed one of two isomorphism types).
