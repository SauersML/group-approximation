---
rg: 2
id: leavitt-d4-true-inverse-screen-audit
kind: claim
title: Bergman-chart inversion must be tracked multiplicatively in Leavitt screens
artifacts:
  - research/artifacts/search-degree4-shared-triangle-boundary.py
  - research/artifacts/search-degree4-length12-rank7-branch-a.py
invalidates:
  - leavitt-degree3-algebraic-corner-cycle-proof
  - leavitt-degree3-direct-pivot-screen-proof
  - leavitt-degree3-trivalent-omega-cycle-is-absent-proof
  - leavitt-degree4-five-corner-full-packet-is-absent-proof
  - leavitt-d3-length9-compound-holonomy-is-absent-proof
---

The faithful Bergman chart used by the Leavitt picture searches is an
algebraic representation, not a unitary one.  Consequently transposing the
finite prefix-pair chart computes an adjoint, not the multiplicative inverse
of a general unit.  In particular, the formerly used helper
`canon({(right,left)})` fails the mandatory check `x^-1 x=1` already for the
marked commutator.

Every corrected screen therefore carries each coefficient as a pair
`(x,x_inverse)`, multiplies pairs by

```text
(x,x^-1)(y,y^-1) = (xy,y^-1 x^-1),
```

and asserts both inverse identities on the generator library.  Symbolic
free-product/retraction theorems do not use the chart helper and are
unaffected.  Any old bounded census that used transpose-as-inverse is not an
exact census and must be rerun before its zero count is cited.

The five invalidated routes above depended on such a bounded census.  This
does not refute their target statements; it removes the defective certificate
until a true-inverse replay or a symbolic proof replaces it.
