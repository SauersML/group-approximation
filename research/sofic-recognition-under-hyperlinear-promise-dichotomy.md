---
rg: 2
id: sofic-recognition-under-hyperlinear-promise-dichotomy
kind: claim
title: Sofic recognition under a hyperlinear promise is Pi-zero-two hard iff a recursively presented hyperlinear nonsofic group exists
distinct_from:
  hyperlinear-nonsofic-group: that asks for the group; this is the recognition-theoretic reformulation, established as a dichotomy whichever way that question goes.
  approximation-property-recognition-dichotomy: that reformulates the existence of a non-hyperlinear group as undecidability of hyperlinearity; this reformulates the existence of a hyperlinear nonsofic group as promise-hardness of soficity, the same pattern one notch down.
  sofic-recognition-two-generator-recursive-is-pi2-complete: that is unconditional hardness with no promise on the input; this restricts inputs to hyperlinear groups, where hardness is exactly as open as Pestov's question.
---

ESTABLISHED (as a dichotomy).  Let `SOFIC_enum` be soficity on enumerated
presentation codes and `HYP_enum` the hyperlinear promise.  Exactly one of:

```text
(A) every hyperlinear recursively presented group is sofic; then
    SOFIC_enum restricted to HYP_enum is the whole promise set.
(B) some recursively presented hyperlinear group is not sofic; then
    SOFIC_enum is Pi^0_2-hard and NONSOFIC_enum is Sigma^0_2-hard under
    the promise HYP_enum (every output of the reduction is hyperlinear,
    with exactly two isomorphism types), and both remain so under the
    two-generator bridge whenever the bridge preserves hyperlinearity.
```

Since recursively presented groups include the finitely presented ones,
(B) holds as soon as a finitely presented hyperlinear nonsofic group
exists; and any hyperlinear nonsofic group has a finitely generated
hyperlinear nonsofic subgroup, so (B) is exactly the recursively
presentable case of [[hyperlinear-nonsofic-group]].  In the promise
world the hardness is the witness: a proof that soficity is not decidable
on hyperlinear inputs would resolve Pestov's Question 3.4 negatively in
the same non-constructive way that
[[non-hyperlinear-from-hyperlinear-recognition-undecidable]] resolves the
goal.
