# Leiden Declaration compliance map

Reference: Leiden Declaration on Artificial Intelligence and Mathematics
(2 June 2026, DOI 10.5281/zenodo.20302944).  This file maps its
individual-researcher recommendations onto this project's practices, and
records the actions taken on 2026-08-13 to close the gaps.

## Disclose tool use — GAP CLOSED

* The manuscript `non_mf_groups_exist.tex` now carries a "Tool and
  computational resource disclosure" section (drafted 2026-08-13; folded in
  by the tex lane with the final ritual).  Contents: the mathematics was
  developed and formalized with extensive use of large language models
  (Anthropic Claude models, multiple concurrent interactive sessions)
  operating under continuous human direction; formal verification in
  Lean 4 against Mathlib with the kernel as final checker; builds and
  audits on the Minnesota Supercomputing Institute cluster; literature
  search assisted by web-connected model sessions with all
  attribution-critical claims verified against primary sources by direct
  reading.
* The repository README carries the same disclosure at repo level,
  including the per-commit `Co-Authored-By` trailers as a provenance
  record.

## Retain the responsibility for correctness / affirm humanity of authorship

* The named human author is the sole author of record and retains
  exclusive responsibility for correctness, adequacy, and citations.  No
  AI system is credited as an author.  The commit trailers are tool
  provenance, not authorship claims.
* The kernel-checked Lean development (axiom closure: propext,
  Classical.choice, Quot.sound; no sorry, no project axioms, no
  literature-transcription premises) is the project's answer to the
  Declaration's warning that automated methods produce plausible but
  unreliable arguments: here the machine-checked artifact is offered so
  reviewers need not trust any generated prose.

## Support the needs of reviewing

* Formal proofs are provided for the headline results (the Declaration's
  "provide formal proofs where feasible" — done at scale).
* The claim map, signature pins, and axiom audits
  (`docs/CLAIM_SIGNATURES.md`, `scripts/Audit.lean`) let reviewers verify
  exactly which manuscript statements have formal counterparts.
* Statements without formal counterparts are explicitly marked as such in
  the manuscript (anonymous-build-guarded remarks).

## Put effort into proper attribution

* Three successive adversarial credit/priority audits are recorded in
  `docs/CREDIT_AND_PRIORITY_AUDIT.md` (results, machinery, and inheritance
  layers), with primary sources read directly where extraction tooling
  failed, MathOverflow-level provenance recorded (per the Declaration's
  spirit), and an explicit narrowed novelty claim.  Where attribution
  remains uncertain, the manuscript says so explicitly.

## Adhere to principles of open science

* The repository is public under Apache-2.0; the formal library, audits,
  and manuscript sources are all in one place; no proprietary knowledge
  or equipment is required to verify the proofs (Lean and Mathlib are
  open source; a laptop suffices for checking, if slowly).

## Insist on appropriate publication outlets / evaluation

* Standing policy (recorded in project memory and docs): no public
  priority claim before independent specialist verification; the
  manuscript is aimed at peer review, not announcement-by-press-release.
  The cautionary precedent (arXiv:2510.17003 withdrawal; the redacted
  claim in the recent sofic announcement) is documented in the audit
  file.

## Consider carefully which tools to use / ethical evaluation

* Tooling: Lean 4 + Mathlib (open source), Anthropic Claude (commercial;
  disclosed), university compute (public infrastructure, per the
  Declaration's preference).  The mathematics is foundational research in
  group theory and operator algebras with no identified application to
  warfare, surveillance, or oppression.
