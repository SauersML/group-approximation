---
rg: 2
id: relative-soficity-extension-theorem-withdrawn
kind: claim
title: The sofic-by-residually-amenable extension theorem is withdrawn and unavailable
invalidates: [one-relator-sofic-via-residually-amenable-quotient]
distinct_from:
  sofic-semidirect-product-closure-fails: that is a mathematical refutation — a permanence statement shown false by explicit counterexamples; this is a bibliographic fact — a claimed permanence statement whose only source retracted it. One is known false, the other merely unsupported, and confusing the two would misreport what is open.
  one-relator-groups-sofic: that is the open question this shortcut would have nearly collapsed; this only records that the shortcut has no source, and it moves the question in neither direction.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED, as a fact about the literature.  The statement

> if `N ⊴ G` is sofic and `G/N` is **residually amenable**, then `G` is sofic

has exactly one source in the literature — Ji--Ogle--Ramsey, *Relative
Amenability and Relative Soficity*, arXiv:1807.07600 — and that preprint is
**withdrawn**.  The arXiv record's comment reads verbatim

    Error in proof of Theorem 3.15

with v2 and v4 marked withdrawn and the final withdrawal dated 10 January 2019.
Read from arXiv on 2026-08-17; the transcription is in the artifact.

The statement is therefore **not available as an input**, at any quality, and
in particular is not a "published theorem" for the purposes of the standing
zero-literature order.  It is not known to be false either — no counterexample
is recorded here — so a proof of it would be a real theorem, not a rediscovery.

## Why the graph carries a bibliographic fact as a node

Because the shortcut is genuinely tempting and will be rediscovered.  Linton's
theorem hands over a one-relator group's quotient `G/R = F/<<r>>` as
**residually rationally solvable**, hence residually solvable, hence residually
amenable.  Combined with the withdrawn statement, a sofic Linton radical `R`
would immediately give `G` sofic and, with
[[residually-rationally-solvable-one-relator-sofic]], reduce all of Pestov's
Question 4.9 to soficity of the radicals.  That is a large enough prize that
anyone reading Linton next to Ji--Ogle--Ramsey will try it; the external attempt
audited here did try it, and retracted after checking the arXiv record.

Recording the withdrawal as an obstruction claim, rather than silently omitting
the route, means the next session finds the dead end already labelled.  The
route it kills is [[one-relator-sofic-via-residually-amenable-quotient]].

## What survives

Only the genuinely amenable case.  `G/E` for `E = G_Q^(n)` a **finite**
rational-derived term is solvable, not merely residually so, and
sofic-by-amenable (Elek--Szabó) is a theorem.  That is why
[[one-relator-soficity-localizes-at-rational-derived-stage]] stops at the finite
stage `E` and does not continue to `R = G_Q^(ω)`: the last step from `E` down to
`R` is exactly the one the withdrawn theorem would have supplied.
