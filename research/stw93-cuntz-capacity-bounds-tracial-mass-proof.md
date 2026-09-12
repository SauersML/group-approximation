---
rg: 2
id: stw93-cuntz-capacity-bounds-tracial-mass-proof
kind: route
title: Apply a trace dimension function to orthogonal Cuntz copies of a spectral cut
target: stw93-singular-trace-needs-finite-central-cuntz-capacity
requires: []
artifacts:
  - research/artifacts/stw93-faithful-diagonal-multiplicity-escape-audit-2026-08-30.md
---

Let `q` be a normalized trace on a unital C*-algebra `D` and suppose
`q(h)>0` for `h in D_+`.  Since

```text
(h-epsilon)_+ -> h
```

in norm as `epsilon` decreases to zero, choose `epsilon>0` with
`q(a)>0`, where `a=(h-epsilon)_+`.  Its lower semicontinuous dimension
function satisfies

```text
d_q(a)=lim_(r->infinity) q(a^(1/r)) >= q(a)/||a|| >0,  (2)
```

after rescaling if necessary; equivalently, the support of `a` has positive
`q`-mass.  Whenever `n[a]<=[1_D]` in `Cu(D)`, additivity and order
preservation give

```text
n d_q(a)<=d_q(1_D)=1.                                  (3)
```

Thus `n<=1/d_q(a)`, proving that only finitely many integers occur in the
definition of `cap_D(a)`.

Apply the contrapositive in the XCIII central sequence algebra.  If all
nonzero spectral cuts of every `h in I_+` have infinite capacity, no
normalized trace can take a positive value on `h`; hence every normalized
trace kills `I`.  If an extra normalized trace exists, the exact
trace-kernel reduction supplies `h in I_+` with positive value, and the
preceding argument supplies its finite-capacity cut.
