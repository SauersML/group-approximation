---
rg: 2
id: amenable-nonqd-descends-liftable-quotients
kind: claim
title: Amenable non-QD traces descend through locally liftable quotients
distinct_from:
  amenable-trace-descends-through-locally-liftable-quotient: that descends amenability alone; this observes that non-QD also survives because QD always pulls back through a quotient.
  exact-gns-kernel-amenability-reduction: that specializes to the faithful GNS quotient of an exact algebra; this applies to any locally liftable trace-preserving quotient.
  stw99-problem-x1-amenable-traces-quasidiagonal: this is a counterexample permanence theorem conditional on already having a counterexample, not a construction of one.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `q:A -> B` be a unital locally liftable quotient and let `tau_B` be a
trace on `B`.  If

```text
tau_A=tau_B o q
```

is amenable but not quasidiagonal on `A`, then `tau_B` is amenable but not
quasidiagonal on `B`.

Thus a counterexample to STW Problem X(1) descends through every locally
liftable quotient by an ideal on which it vanishes.
