---
rg: 2
id: literal-full-group-cstar-is-nonexact
kind: claim
title: The full group C-star algebra of the literal group is nonexact
distinct_from:
  literal-group-fails-local-lifting-property: LLP and exactness are independent local tensor/lifting properties; the literal algebra fails both, by different obstructions.
  literal-stably-finite-non-mf-reduced-group-algebra: that concerns the reduced algebra and does not assert exactness either way; this concerns only the full/maximal algebra.
artifacts:
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

**ESTABLISHED.**  The full group algebra `C*_(max)(E)` of the literal
forty-one-relator group is not exact.

The split normal form embeds `SL_3(Z)` in `E`, so `E` is nonamenable.
The established Folner--finite-quotient construction gives `E` Kirchberg's
factorization property.  Therefore
`nonamenable-factorization-groups-have-nonexact-full-cstar` applies.

Consequently the same explicit finitely presented sofic group now separates
four finite-dimensional approximation properties at once: its full canonical
trace is amenable, but not quasidiagonal; its full algebra is neither exact
nor LLP; and the group and both group C-star algebras are not MF.
