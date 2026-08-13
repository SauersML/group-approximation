# Routing of the 2026-08-13 referee-style report

The user supplied an adversarial referee report on `non_mf_groups_exist.tex`
(verdict: no error found across the witness, Theorem B, and the
corner→conjugation→Kazhdan→stable-finiteness chain; major revision for
presentation/attribution; independent expert verification demanded).  This
file routes its action items to lanes.

## Already satisfied by the Lean development (cite in the revision)

* **Comment 1 (CRW presentation completeness risk).**  The Lean theorem is
  ALREADY in the robust form the referee requests: the kill is stated for
  `MarkedCompressionInclusionData` over an arbitrary Kazhdan group, and the
  machine-checked witness chain never uses the CRW presentation — the
  internal base (`ExplicitNonMFBase`, rank-4 elementary over the binary
  Leavitt algebra, property (T) proved in-repo) carries it.  The tex should
  restate Definition 3.3 as "fix any finite presentation of Γ" exactly as
  the referee suggests; the CRW-explicit form becomes a corollary whose
  only burden is explicitness, and the Lean anchor makes the robust form
  independently checkable.
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
