---
rg: 2
id: pure-z-plateau-capacity-equals-quasitrace-nullity
kind: claim
title: In a pure algebra with a unital Jiang--Su copy, infinite Cuntz capacity is exactly quasitrace nullity
distinct_from:
  stw93-singular-trace-needs-finite-central-cuntz-capacity: that one-way theorem bounds the capacity of a spectral cut charged by an ordinary trace in an arbitrary unital algebra; this theorem gives the converse and treats normalized 2-quasitraces under pureness and unital Jiang--Su absorption data.
  stw93-saturated-slice-ideal-has-infinite-cuntz-capacity: that is the actual-XCIII application to one established quasitrace-null ideal; this is the abstract pointwise equivalence which explains the application.
  stw93-mixed-z-slice-si-forces-infinite-capacity: that theorem constructs Cuntz copies from a mixed property-(SI) hypothesis; this theorem uses strict comparison and requires only common quasitrace nullity of the source.
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

Let `D` be a pure unital C*-algebra admitting a unital homomorphism
`rho:Z->D`.  For `a in D_+`, define

```text
cap_D(a)=sup{n in N:n[a]<=[1_D] in Cu(D)}.
```

Then the following are equivalent:

1. `cap_D(a)=infinity`;
2. `d_q(a)=0` for every normalized lower-semicontinuous `2`-quasitrace `q`
   on `D`;
3. `q(a)=0` for every such `q`.

Thus, in the XCIII central sequence algebra, the positive infinite-capacity
cone is exactly the common normalized-quasitrace null cone.  In particular,
proving infinite capacity for the full trace-kernel ideal is pointwise
equivalent to proving that every quasitrace annihilates that ideal; capacity
is not a formally weaker escape once central pureness and the unital
Jiang--Su copy are used.
