---
rg: 2
id: nonamenable-factorization-regular-quotient-not-liftable
kind: claim
title: The full-to-reduced quotient of a nonamenable factorization-property group is not locally liftable
distinct_from:
  stw99-problem-x1-fails-on-full-group-algebras: this is a quotient-lifting obstruction and does not produce an amenable non-QD trace; for F2 the amenable full canonical trace is itself QD.
  exact-gns-kernel-amenability-reduction: that proves amenability descends through exact GNS quotients; this supplies explicit nonexact GNS quotients where descent and local liftability fail.
  amenable-trace-descends-through-locally-liftable-quotient: that is the positive descent theorem; this is its group-theoretic obstruction consequence.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `G` be a nonamenable discrete group with Kirchberg's factorization
property.  Then the regular quotient

```text
q:C*(G) -> C*_r(G)                                    (1)
```

is not locally liftable.  Moreover, the amenable canonical trace on the full
algebra does not remain amenable on its faithful GNS image.

In particular, (1) is not locally liftable for `G=F_2`.  This is an
unconditional warning that the faithful GNS-image reduction used for exact
algebras fails in the nonexact setting.
