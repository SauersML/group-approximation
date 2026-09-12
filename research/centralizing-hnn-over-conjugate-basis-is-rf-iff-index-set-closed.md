---
rg: 2
id: centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed
kind: claim
title: The centralizing HNN extension of a free group over conjugates of one generator is residually finite iff the index set is profinitely closed
distinct_from:
  index-set-profinitely-closed-is-pi3-complete: that classifies closedness of index sets; this converts closedness into residual finiteness of one explicit group.
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that uses only the two extreme cases (finite and full index sets) with a countable free product; this is the exact criterion for every index set, which is what removes the free product.
  bidirectional-hnn-bridge-trivial-value-is-residually-finite: that is an HNN extension of a free group along a nontrivial isomorphism between free subgroups; this is a centralizing HNN extension (identity isomorphism), and its residual finiteness is decided by a profinite closure criterion rather than proved outright.
---

ESTABLISHED.  In `F = F(a, b)` put `a_j = b^j a b^-j` for `j in Z`; the
`a_j` form a free basis of the normal closure of `a`.  For `J <= Z` let

```text
A_J = < a_j : j in J >,
H_J = < F, s | [s, A_J] = 1 > = F *_{A_J} (A_J x Z).                 (CH1)
```

Then

```text
(i)  the profinite closure of A_J in F is A_{cl(J)},
(ii) H_J is residually finite  iff  A_J is closed in F  iff  cl(J) = J,   (CH2)
```

where `cl(J)` is the closure of `J` in the profinite topology of `Z`.

Thus residual finiteness of the three-generator group `H_J` records exactly
whether `J` is closed in `Z-hat`.  Finite `J` (M. Hall) and `J = N` (with
`a_{-1}` in the closure) are the two cases used by
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]]; the
general criterion feeds [[residual-finiteness-three-generator-recursive-is-pi3-complete]].
