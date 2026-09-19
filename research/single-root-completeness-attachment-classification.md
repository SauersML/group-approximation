---
rg: 2
id: single-root-completeness-attachment-classification
kind: route
title: Classify one-root attachments to the binary range fold
target: single-root-completeness-attachments-are-exhausted
requires:
  - leavitt-range-sum-fold-is-first-object-erasing-row
  - intermediate-fold-arm-has-finite-s6-model
  - native-opposite-arm-return-has-finite-s6-model
  - reverse-product-whitehead-fold-has-finite-fusion
---

Let `alpha=(a,b)` and let `beta=(c,d)` be a different root.  If `c=b`, the
ordinary Steinberg relation composes on the right.  If `d=a`, it composes on
the left.  The only way both endpoint sets coincide is `beta=-alpha`, the
opposite-root case.  If instead `c=a` or `d=b`, the two roots share a source
or target and their root groups commute.  If all four relevant endpoints
are distinct, they are distant and commute.  These cases are disjoint and
exhaust all ordered pairs `c!=d`.

In the right-composable case, direct substitution gives

```text
[x_ab(q_i),x_bk(r)]=x_ak(q_i r),
[x_ab(1),x_bk(r)]=x_ak(r).
```

Root addition in the output group says that the two child outputs multiply
to the parent output.  The left-composable calculation is identical with
coefficient order reversed.  Thus every non-opposite one-root reader is the
intermediate fold already fenced by the required claims.

For the opposite position there is no non-opposite commutator formula.  The
shortest ordinary occurrence retaining the coefficient is the three-factor
partial Whitehead.  Applying it separately to the orthogonal idempotents
`p,q` and their sum `1` is exactly the table proved and fenced by
`reverse-product-whitehead-fold-has-finite-fusion`.  Hence every
noncommuting incidence class has the asserted existing finite model.
