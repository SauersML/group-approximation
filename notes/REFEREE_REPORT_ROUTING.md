# Routing of the 2026-08-13 referee-style report

The user supplied an adversarial referee report on `non_mf_groups_exist.tex`
(verdict: no error found across the witness, Theorem B, and the
corner→conjugation→Kazhdan→stable-finiteness chain; major revision for
presentation/attribution; independent expert verification demanded).  This
file routes its action items to lanes.

## Already satisfied by the Lean development (cite in the revision)

* **Comment 1 (CRW presentation completeness risk).**  The reusable analytic
  kill is in the robust form the referee requests:
  `MarkedCompressionInclusionData` accepts an arbitrary Kazhdan base.  The
  closed finitely presented Lean endpoint, however, instantiates it with a
  noncomputably chosen Shalom cover of the separate `ExplicitNonMFBase`; it
  is not the CRW-based literal group.  The literal Lean endpoint assumes
  property `(T)` of the abstract twenty-relator base.  Discharging that
  premise from the classical affine group requires a formal presentation-
  completeness isomorphism as well as property `(T)`, because the verified
  relators alone give a quotient in the wrong direction.  Thus the robust
  mechanism is independently checkable, but the literal CRW instance is not
  an unconditional Lean corollary.
* **Comment 2 (criterion form; W itself non-MF).**  The standalone
  criterion IS the Lean theorem `MarkedCompressionInclusionData.not_isWeakMF`,
  and the countable witness `W = ClLamp(X̄) ⋊ Ḡ` is exactly the group the
  Lean construction instantiates (`MarkedCompressionGroup`), so "W is
  itself non-MF, with E needed only for finite presentability" is available
  as a machine-checked statement.  Add both to the tex.

## Tex lane (owners: 55661 primary, 88664 generalization pass)

* Comment 3: bibliography repairs (CDE-definition vs Shulman-caveat split,
  BDL entry consistency, Dad alphabetical order, OAI marked as
  non-refereed corporate document) + engage Fournier-Facio
  (arXiv:2608.02025, torsion-free nonsofic) and Alekseev–Thom
  (arXiv:2608.05362, centralizers of sofic approximations of Kazhdan
  groups).
* Comment 4: add the soficity/hyperlinearity-of-E paragraph (we do not
  know whether E is sofic; why w is invisible to Hamming-metric methods).
* Comment 5 + minors 1–8: structural/notation fixes; align the
  formalization remarks with the actual repo state (the "unfilled
  placeholder" concession in Remark 4.6 is now stale — the assembly is
  complete and sorry-free).
* PRIORITY FACTS confirmed by the referee: OpenAI announcement 2026-08-01;
  a priority claim in that announcement was redacted within days after
  community scrutiny — keep our own claims conservative and verification
  -gated.

## Process

The referee's demand for independent re-derivation of Sections 5–7 is
addressed in part by the kernel-checked Lean development (zero premises
beyond Mathlib); external specialist review remains the user's call before
any public claim, per the frozen-status policy.

## Lane claim (2026-08-12 ~21:20, citation-audit session)

A separate session is now running the deep-web adversarial credit/citation
audit for `non_mf_groups_exist.tex`.  Sub-lane claimed, to avoid duplicate
edits by the tex-lane owners:

* Verifying every existing `\bibitem` (metadata to punctuation level) and
  every pinpoint (CRW Thm 2; BHV section numbers; CDE 2.14/2.18; Shulman
  Def 3/footnote; TWW Cor B; Dadarlat 3.18/3.19; BO Ch 7; BK; AW), plus the
  NEW keys now cited in the draft (`SlofstraProfile`, `SlofstraVidick`,
  `SlofstraCorrelations` — currently cited with NO `\bibitem`, i.e. the
  bibliography block is pending) and Fournier-Facio / Alekseev–Thom.
* Deliverables: (a) a dated findings section appended to
  `notes/CREDIT_AND_PRIORITY_AUDIT.md`; (b) edits to the tex BIBLIOGRAPHY
  BLOCK ONLY (missing bibitems, verified metadata corrections) plus any
  verified-wrong pinpoint numbers in citing text, as narrow edits.
* Tex-lane owners: please do NOT independently fill the three Slofstra
  bibitems or re-verify bib metadata; everything else in the tex remains
  yours.  This session will not touch `NegativeCornerModel.lean` or any
  Lean file, and will not run `lake`.

### Citation-audit sub-lane: COMPLETE (2026-08-13 ~02:30)

All 31 bibitems and every pinpoint source-verified (details + applied-fix
log in `notes/CREDIT_AND_PRIORITY_AUDIT.md`, third pass).  Fixes are in the
tex working copy; they will ride the tex lane's next checkpoint commit.
The bibliography block is now verified — please don't "improve" entries
from memory; if you add a NEW citation, verify against the source first
(the audit found wrong pinpoints in 6 of the first 13 entries checked).
