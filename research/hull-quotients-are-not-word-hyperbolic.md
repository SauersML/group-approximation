---
rg: 2
id: hull-quotients-are-not-word-hyperbolic
kind: claim
title: Acylindrical small-cancellation quotients are not word-hyperbolic
invalidates:
  - non-rf-hyperbolic-via-hull-routing
distinct_from:
  common-quotient-onto-normal-subgroup: that is the small-cancellation construction this graph consumes, stated for acylindrically hyperbolic inputs; this is a scope statement about what its output is and is not, and its content is that word-hyperbolicity is not among the preserved properties
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/HULL_ROUTING_AUDIT_2026-08-16.md
---

Hull's small-cancellation theorem (*Small cancellation in acylindrically
hyperbolic groups*, GGD 10 (2016), arXiv:1308.4345) produces quotients that
are again **acylindrically hyperbolic**.  Word-hyperbolicity of the output is
not part of the conclusion; it survives only in the special clause where the
input is hyperbolic and the relators are chosen to keep it so.

Acylindrical hyperbolicity is much weaker.  Acylindrically hyperbolic groups
routinely contain `ℤ^2` — mapping class groups, `Out(F_n)`, right-angled Artin
groups with a square, and the wreath-type constructions this program builds —
and no word-hyperbolic group contains `ℤ^2`.

## Why this needs saying in this graph specifically

This corpus reasons with acylindrical hyperbolicity everywhere: the
Fournier-Facio skeleton (`fournier-facio-torsion-free-skeleton`), the defect
routing (`defect-normally-generates-torsion-free-quotient`), and the
common-quotient tool itself (`common-quotient-onto-normal-subgroup`).  One
existing node even writes "(acylindrically) hyperbolic" of a candidate group.
The abbreviation is harmless inside those lanes and fatal outside them: the
moment a route wants a *word*-hyperbolic conclusion, an acylindrically
hyperbolic hypothesis supplies nothing, and the difference is not a technical
gap that a sharper argument could close.

`notes/HULL_ROUTING_AUDIT_2026-08-16.md` records what Hull's Theorem 7.1 does
supply for this program's routing — six of the seven fields of
`DefectRoutingData`, finite presentation included.  Word-hyperbolicity is not
one of them and was never claimed to be; this node exists so that no route can
quietly assume it.
