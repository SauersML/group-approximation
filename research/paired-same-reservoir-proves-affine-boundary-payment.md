---
rg: 2
id: paired-same-reservoir-proves-affine-boundary-payment
kind: route
title: Same-reservoir closure plus cyclic trace converts the affine binary boundary into a fixed-depth mark estimate
target: affine-leavitt-boundary-shear-payment
requires:
  - paired-same-reservoir-boundary-lemma
  - bistochastic-diagonal-return-forces-aligned-permutation
  - closed-multiplicity-cycle-kills-carrier-trace
  - tensor-independent-child-carrier-gap
---

At each of the first `N` levels, apply the paired same-reservoir lemma.  Mass
which exits the source-sized reservoir is absorbed into the fixed-depth error
term.  On the surviving square part, the two diagonal Leavitt return laws are
square bistochastic pairs with near-full cyclic overlap.  The bistochastic
rigidity theorem replaces each by one aligned permutation and its inverse,
with constants independent of the label count.  The crossed-zero relation
then pays the robust paired floor unless the branch loses the corresponding
mass.

Follow every surviving branch until it returns to its initial physical
carrier.  The closed multiplicity-cycle ledger gives

```text
tr(P_0) <= 3 error + ||P_N-P_0||_2/(2^N-1).
```

All leakage and finite-window exactification losses are absorbed into one
finite coefficient `C_N`; no uniformity in `N` is required.  Equivalently,
if the mixed words provide the transverse version of the lemma, the
tensor-independent child-carrier gap pays the same mass immediately.  In
either case the residual uncharged marked mass is at most `2^-N`, yielding
the estimate required by `affine-leavitt-boundary-shear-payment`.
