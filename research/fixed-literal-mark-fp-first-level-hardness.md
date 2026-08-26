---
rg: 2
id: fixed-literal-mark-fp-first-level-hardness
kind: claim
title: The fixed invisible-mark query on finite presentations is undecidable on both sides
distinct_from:
  fixed-non-mf-mark-query-is-second-level-complete: that asserts exact second-level completeness and needs a stronger finite-presentation switch; this theorem is the unconditional first-level lower bound supplied directly by the explicit Adian--Rabin transform.
  fixed-mark-query-enumerated-second-level-complete: that obtains exact second-level completeness for countably generated enumerated presentations; this keeps the target presentations finite.
---

Fix the literal finitely presented non-MF group `E` and its nontrivial
MF-invisible mark `w`.  For a finite-presentation code `c`, define

```text
SURV(c) := there exists phi:E->Carrier(c) with phi(w)!=1,
KILL(c) := every phi:E->Carrier(c) satisfies phi(w)=1.
```

There is a computable transformation from every finite-presentation word
problem instance `(c,v)` to a finite-presentation code `T(c,v)` such that

```text
SURV(T(c,v)) iff v!=1 in Carrier(c),
KILL(T(c,v)) iff v=1 in Carrier(c).
```

Consequently `SURV` is not recursively enumerable, `KILL` is not
co-recursively enumerable, and neither predicate is decidable.  Every `SURV`
instance is non-MF.  This is an unconditional finite-presentation result but
does not claim second-level completeness.
