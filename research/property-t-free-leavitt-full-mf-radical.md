---
rg: 2
id: property-t-free-leavitt-full-mf-radical
kind: claim
title: Derive binary-Leavitt full MF collapse without Kazhdan hypotheses
root: true
goal: true
artifacts:
  - research/property-t-free-leavitt-via-corona-module-decoder.md
  - research/property-t-free-leavitt-via-full-support-hs-decoder.md
---

OPEN.  Let `R` be a countable nontrivial ring carrying a binary Leavitt
family, and suppose a fixed nonzero elementary root normally generates
`E_n(R)`.  Prove

```text
Rad_MF(E_n(R)) = E_n(R)
```

without assuming property `(T)` for either the compression source or the
ambient elementary group.

The proposed route is intrinsic to norm matrix coronas.  A surviving root
has exact finite additive and Heisenberg multiplicity germs.  The remaining
step is to assemble those germs into one nonzero finitely generated
projective corona module carrying a unital action of `R`.  Rank-germ
Hilbert-hotel cancellation would then force that module to vanish.

The finite-order normal-generator theorem reduces every surviving corona
model to a uniformly positive-density active core.  Consequently there are
two exact endpoints: construct a finite-projective norm-corona coefficient
module, or construct the corresponding positive-density Hilbert--Schmidt
coefficient module.  This goal separates the completed algebraic
Hilbert-hotel obstruction and active-core reduction from the remaining
coherence theorem.
