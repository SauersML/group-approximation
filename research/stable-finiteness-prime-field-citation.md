---
rg: 2
id: stable-finiteness-prime-field-citation
kind: route
title: Import Bradford--Fournier-Facio Theorem 3.4 and Corollary 3.15
target: stable-finiteness-reduces-to-prime-field
requires: []
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Citation import.  `https://arxiv.org/html/2211.01510v2` was read on
2026-08-17 and Theorem 3.4, Corollary 3.5, Corollary 3.15 and Corollary 3.25
were transcribed verbatim into the audit artifact.  Published as
Math. Z. 308 (2024), article no. 58.

**Trust surface.** One refereed journal paper, read at v2 on arXiv rather
than in the journal version, and its proofs were not re-derived here.  Part
(1) of the claim is independently classical (Kaplansky), and this repository
was already relying on the same three results — `official/counterexample.tex`
cites BFF24 Theorem 3.4, Corollary 3.5 and Corollary 3.25 by number — so the
import adds no new dependency to the manuscript; Corollary 3.15 is the only
statement of the four that was not already in use.

The half of part (2) that a search actually consumes, "a counterexample over
some field of characteristic `p` gives one over a **finite** field of
characteristic `p`", is also proved from scratch in Section A of the artifact
(generate the coefficients, invert a surviving coefficient of `BA - I_n`,
contract a maximal ideal, apply Zariski's lemma).  Only the last step from a
finite field down to its prime subfield rests on the citation.
