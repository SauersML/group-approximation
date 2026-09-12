---
rg: 2
id: literal-nonsofic-via-stable-central-quotient
kind: route
title: Turn stability of the marked quotient into non-soficity of E
target: literal-group-not-sofic
requires: [literal-mark-quotient-flexibly-stable, literal-central-mark-corona-invisible, gohla-thom-stable-base-nonsofic-extension]
artifacts: [notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md, non_mf_groups_exist.tex]
---

## Why sufficient (dead — kept as the record of two corrections)

INVALIDATED by `literal-group-sofic`: `E` is sofic, so this route's target is
false.  It was wrong on its own terms as well, and both corrections are worth
keeping.

1. **Citation locus** (found by `cairn-scout` from the PDFs).  The theorem is
   Gohla--Thom `arXiv:2403.09582v2` **Theorem 3.13**, imported as
   `gohla-thom-stable-base-nonsofic-extension`.  The "Theorem 1.5" this route
   originally cited is Chapman--Dikstein--Lubotzky's numbering of a corollary
   specialized to the p-adic Deligne extension, not a general criterion.
2. **Dropped hypotheses.**  Theorem 3.13 also requires the base to be
   residually finite of finite type and to satisfy a dimension-2 cosystolic
   inequality for all finite transitive actions — the latter is what makes the
   cohomological obstruction survive on finite actions, and it holds for the
   lattices via high-dimensional expansion of a Bruhat--Tits quotient.  `E/<w>`
   has no such geometry.  Moreover Chapman--Dikstein--Lubotzky show stability
   does NOT pass from a base to its central extension in general, which is why
   the cohomological machinery was needed at all.

**What replaced it.**  `cairn-scout` extracted the elementary principle behind
all of this — a sofic group stable in finite actions is residually finite
(`sofic-stable-implies-residually-finite`) — and proposed applying it to `E`
itself.  With `literal-group-sofic` established, that principle runs in the
opposite direction from the one intended here and yields a positive result:
`literal-group-not-stable-in-finite-actions`.  The stability hypothesis was
never available; the stability *conclusion* is.
