---
rg: 2
id: fixed-non-mf-mark-query-enumerated-presentations-is-second-level-complete
kind: claim
title: The fixed non-MF marked query is exactly second-level complete on enumerated presentations
distinct_from:
  fixed-non-mf-mark-query-is-second-level-complete: that concerns finite-presentation codes and uses a separate finite-presentation compiler; this theorem concerns the standard partial-recursive enumeration syntax for countably generated presentations.
  mf-recognition-recursive-presentations-is-second-level-complete: that classifies MF itself on recursive presentations; this classifies one fixed homomorphism-and-mark query whose positive instances are sound non-MF certificates.
---

Fix the literal finitely presented non-MF group `E` and its nontrivial
MF-invisible mark `w`.  For a standard partial-recursive code `c` enumerating
a countably generated presentation `P_c`, put

```text
SURV(c) := there exists phi:E->P_c with phi(w)!=1,
KILL(c) := every phi:E->P_c satisfies phi(w)=1.
```

Then `SURV` is `Sigma^0_2`-complete and `KILL` is `Pi^0_2`-complete under
computable many-one reductions.  Neither predicate is recursively enumerable
or co-recursively enumerable.  Every `SURV` instance is non-MF, because the
surviving image of `w` remains MF-invisible by functoriality.

The reduction is uniform and uses the explicit countable ray switch: an
infinite event stream gives the trivial group, while a finite event stream
leaves exactly one tail copy of `E`.  This statement makes no claim about
finite-presentation codes.
