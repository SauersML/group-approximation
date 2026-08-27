---
rg: 2
id: rectangle-adjoint-symmetry-is-an-extra-relation
kind: claim
title: Adjoint symmetry of the one-letter Hecke rectangle is an extra group relation
distinct_from:
  rank-five-rectangle-is-one-letter-hecke-element: that produces the normalized letter; this computes it exactly and tests whether adjoint symmetry follows from the rectangle equations.
  finite-subgroup-hecke-literals-cannot-block-escape: that detects when one compressed literal is a projection; this concerns conjugacy of identity plus a compressed literal to its adjoint.
  subgroup-supported-one-sided-inverse-rigidity: that kills a factor when its support subgroup has directly finite group algebra; this rules out a proposed purely formal symmetry proof without assuming direct finiteness.
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

For

```text
alpha=h_0+(1+r)x(1+s)
```

in the rank-five rectangle normal form, corner-unit normalization gives

```text
e alpha e  ~  e(1+y)e,
y=s^-1 h_0^-1 r^-1 x.
```

Its adjoint is `e(1+y^-1)e`.  A normalizer element conjugating `y` to
`y^-1` would kill that particular one-sided inverse candidate, but the
rectangle equations do not supply one.  Indeed in the universal group
`C_3*Z`, the normalizer of `C_3` is `C_3`, and reduced-word normal form
forbids every such conjugacy.  Thus an adjoint argument can only eliminate
letters satisfying an additional reversible-double-coset relation; it
cannot close the rectangle branch formally.

