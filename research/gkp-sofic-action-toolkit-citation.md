---
rg: 2
id: gkp-sofic-action-toolkit-citation
kind: route
title: Import Theorem 2.14, Proposition 2.15 and Proposition 2.16 from the published paper
target: gkp-sofic-action-toolkit
requires: []
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
---

# Citation import

Not a reproof. `requires: []` here asserts only that the cited statements say
what this graph records them as saying.

The four statements were read on 2026-08-17 from the **arXiv v3 PDF** of
arXiv:2401.04945 — pages 7 (Theorem 2.14, Proposition 2.15(1)–(3)), 8
(Proposition 2.15(4), Proposition 2.16, and the "still open" paragraph), 14
and 15 (Section 4) — rendered page by page rather than passed through a text
summariser, after the Springer copy of record turned out to sit behind an
authorisation redirect. arXiv v3 (2025-08-27) is the version the listing
labels as the published one; it is a 16-page document whose numbering matches
every external citation of the paper that this graph carries.

The two derived consequences stated in the target node — that a free action of
a sofic group on a countable set is sofic, and that soficity of an action is
equivalent to soficity of each of its orbits — are one-line combinations of
the cited statements, written out in the target's body. They are the only
places where this route does any reasoning at all, and neither uses anything
beyond Theorem 2.14 with `N = {1}`, Proposition 2.15(2) and Proposition 2.16.

## Why a `-citation` route and not a `-proof` route

House convention (`kun-thom-nonsofic-wreath-citation`,
`amenable-implies-operator-mf-citation`): an established claim whose content
is external literature gets a companion route with `requires: []` so that the
fixpoint can see it as established. Without one the claim is `OPEN` to the
compiler no matter what its body asserts, and every route requiring it stalls.
