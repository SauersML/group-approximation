---
rg: 2
id: gjkepr-simple-unique-trace-bases-scalarize-selfless-expectations
kind: claim
title: A simple uniquely tracial base scalarizes every selfless expectation
distinct_from:
  robert-tracial-selfless-regularity: Robert derives regularity after a scalar tracial state is known to be selfless; this theorem produces the scalar selfless state from a relative selfless expectation.
  gjkepr-php-crossed-product-expectations-are-selfless: that theorem constructs relative selflessness for PHP crossed products; this is an action-independent composition principle for any selfless expectation over a simple uniquely tracial base.
artifacts:
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
---

Let `(A,E,B)` be a selfless operator-valued C*-probability space.  Suppose
that `B` is simple and has a unique tracial state `tau`.  Then

```text
(A,tau compose E)
```

is a selfless scalar C*-probability space.

Indeed, the scalar expectation `F:B -> C1_B`, `F(b)=tau(b)1_B`, is
approximately selfadjoint inner: this is the Haagerup--Zsidó Dixmier theorem
followed by the real-coefficient observation recorded in the proof of
Corollary 7.9 of Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert.
Theorem 7.8(iv) of the same paper then says that selflessness of `(A,E,B)`
passes to `(A,F compose E,C1_B)`.

**Established (primary-source consequence).**  The two exact ingredients
are Theorem 7.8(iv) and the proof of Corollary 7.9 in
arXiv:2607.20361v1.  They are imported here, not reproved.
