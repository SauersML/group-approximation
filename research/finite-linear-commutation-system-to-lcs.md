---
rg: 2
id: finite-linear-commutation-system-to-lcs
kind: claim
title: Finite binary linear relations with prescribed commutations compile exactly to an LCS
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that uses an already formed LCS gap to produce a nonhyperlinear group; this is the elementary exact syntax compiler into LCS form.
  zpc-readable-control-freezing-to-lcs: that is the hard existence of one perfect frozen fiber from a ZPC-IRS action; this only says that once such a fiber is present, standard LCS syntax costs nothing.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Let `S` be a finite set of involutive operator variables, let `E` be finitely
many affine `F_2` equations in them, and let `C` be finitely many unordered
pairs `{u,v}` required to commute.  There is an explicit finite binary LCS
`L(S,E,C)` such that perfect operator solutions of the original relations are
in bijective correspondence, after forgetting auxiliary variables, with
perfect operator solutions of `L(S,E,C)`.

Construction: keep every equation of `E` as an LCS row.  For every required
commuting pair `{u,v}` introduce one fresh variable `a_(u,v)` and add the row

```text
u + v + a_(u,v) = 0.
```

An LCS operator solution makes the variables in a row commute, so this row
forces `u` and `v` to commute and gives `a_(u,v)=uv`.  Conversely, if `u` and
`v` already commute as involutions, setting `a_(u,v)=uv` extends the tuple to
this row.  Thus the ancilla row enforces commutation without pruning any
commuting assignment.
