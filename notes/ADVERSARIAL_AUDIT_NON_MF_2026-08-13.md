# Adversarial audit of non_mf_groups_exist.tex and its Lean surface (2026-08-13)

Scope: full read of the manuscript (3447 lines), the audit gate
(`scripts/Audit.lean`), and the statement surface of every Lean module named
in a margin badge; independent re-verification of the suspect literature
claims from primary sources; independent recomputation of the arithmetic in
the printed proofs.

## A. Critical findings (fixed in this pass)

1. **Wrong date attributed to Chatterji–Kassabov (two places).**  The tex
   claimed the arXiv:2601.22907v1 manuscript "is dated August 11, 2026" —
   impossible for a v1 submitted January 30, 2026, and contradicted by the
   PDF itself, whose Date footer reads **February 2, 2026** (re-verified
   from the arXiv PDF this pass; arXiv still lists only v1).  Fixed in the
   envelope subsection and in the [CK] bibitem.  Theorem 3 as quoted in the
   tex matches the source verbatim.

## B. Manuscript errors (fixed)

4. Three literal `qquad` typos (missing backslash) in prop:CEvisible would
   have rendered as the text "qquad" in the PDF (also fixed concurrently by
   another session).
5. Proof of Proposition `prop:witness` asserted "$[w,s]=[w,t]=[w,c]=1$"
   with `s` never introduced; replaced by the presentation's own
   quantification over the eight generators.
6. Dangling bibliography entries never cited in the text: **[JNVWY]**
   (MIP*=RE) and **[Ra]** (Rainone).  JNVWY is now cited at the Connes
   embedding mention in rem:nonnuclear (where only the survey [GoldbringMF]
   was cited for the CEP refutation — citing the actual refutation is
   overdue credit); Rainone removed (concurrent session).
7. **Borisov–Sapir trust caveat was missing.**  Prop. ambient(2) cites
   [BoS, Thm 1.6] (residual finiteness of mapping tori of injective
   endomorphisms of f.g. linear groups), whose proof depends on
   Hrushovski's unpublished Frobenius work.  The prior audit had recorded
   this caveat as present in the tex; it was not.  A caveat sentence is now
   in the proof, scoped to that proposition (Theorem A does not use it).
8. Badge legend now states explicitly that an unlabeled statement has no
   formal counterpart (previously only the positive labels were glossed).

## C. Literature verification results (no change needed)

- **CDE Definition 2.7** (re-extracted from arXiv:1210.4050 PDF): "A
  countable group Γ is MF if it embeds in the unitary group of Q_~n for
  some ~n", with ~n an increasing sequence and Q_~n = ∏M_{n_k}/⊕M_{n_k}.
  The manuscript's definition and coordinate model match; CDE's own remark
  (MF ⟺ embeddable with ~n=(1,2,3,…)) reconciles "increasing" vs the
  paper's "strictly increasing", and the Lean equivalences
  (`isOperatorMFIncreasing_iff`, `isCDEOperatorMF_iff_isOperatorMF`, the
  Audit.lean pin with `StrictMono`) close the loop formally.
- **Elek–Szabó [ES05] Theorem 1**: verified from the arXiv:math/0408400
  PDF — the introduction states "we prove that any countable sofic group
  can be imbedded into a countable simple sofic group … (Theorem 1)".  The
  citation in cor:simplesofic is correct.  Note for precision: the
  soficity permanence list cited to [ES05] is *stated* in that paper's
  §1.2 with references; the amenable-extension permanence is *proved* in
  Elek–Szabó, "On sofic groups" (J. Group Theory 9 (2006);
  arXiv:math/0305352), which is not in the bibliography.  Optional
  improvement: add it at the permanence citation.
- CK Theorem 3 statement: matches source verbatim.
- Facts previously verified in the closed citation audit (TWW Cor. C, BHV
  Example 1.7.4(i), AW+Valette for the Kazhdan projection, CRW Thm 2, BDL
  lemma numbers, OAI two-version record) were spot-checked for continued
  presence and are unchanged.

## D. Lean ↔ manuscript correspondence

- All 63 badge (file, declaration) pairs in the tex resolve to existing
  declarations in the named files (scripted check).
- Definitional faithfulness audited at the source level:
  - `IsOperatorMF` = injective hom into ∏U(M_{d_n})/{u_n → 1 in operator
    norm} over the cofinite filter with positive dimensions;
    `NormMatrixCStarCorona` is the genuine ℓ∞/c₀ C*-quotient with the
    Mathlib L2-operator matrix norm, and the audit pins the CDE predicate
    in expanded form (StrictMono dimensions, unitary group of the C*
    corona, injectivity).  This matches BK/CDE.
  - `HasKazhdanPropertyT` is the Kazhdan-pair definition over **real**
    orthogonal representations on complete inner-product spaces (the
    Kun/Ershov–Jaikin form), universe-annotated; equivalence with the
    complex-unitary textbook definition is classical
    (complexification/realification) but is *not* itself formalized, and
    the manuscript never claims it is.  All in-repo uses are internally
    consistent (the analytic argument consumes exactly this form).
  - `KazhdanCompressionCore` = the printed marked Kazhdan pattern
    ((M1),(M2), defect normal closure); `compressionCentralizerDefect`
    matches eq:intrinsicdefect exactly; Theorem B's Lean form
    (`map_marked_commutator_eq_one_units`,
    `compressionCentralizerDefect_le_ker`) is the printed statement, in
    fact slightly more general (Γ a mere subset in the commutator form).
  - The literal presentation module reproduces eq:E exactly: 8 generators
    (`Fin 6 ⊕ Fin 2`, cardinality proved = 8), the twenty base relators
    (independently recomputed against the matrix actions of x, y, z on
    e₁,e₂,e₃ — all columns check), six stable-letter relators, lamp
    relators, and marked-word relators; the marked word is
    [tct⁻¹, v₁(tct⁻¹)v₁⁻¹] verbatim.
  - This finding is now resolved.  `LiteralP13HodgeCertificate` proves the
    exact rational Hodge certificate by kernel-checked residual blocks,
    `LiteralBaseP13PropertyTBridge` transports property (T) to the literal
    base, and `LiteralNonMFEndpoint.manuscriptTheoremA` closes the displayed
    eight-generator endpoint without a caller premise.
- Independent recomputation of printed arithmetic: the 8/64/64 budget in
  lem:compressorcollapse sums to ε exactly; the spectral-rounding factor 2
  is right; the projection-flip bound ε′/√(1−ε′²) ≤ 2ε′ holds for
  ε′ ≤ 1/2; the word-length claims (16 for w, 34 for the centrality
  relators) are correct for the displayed reduced words; the F₈-in-F₂
  index-7 rank computation is correct; the ‖π(g)−1‖ ≥ √2 permutation
  bound is correct.

## E. Remaining issues (not fixed — author decisions)

9. **Anonymous-build badge inconsistency.**  Some badges are wrapped in
   `\ifanonymous\else…\fi` (Theorem D, cor:quotclosure, prop:W,
   prop:CEvisible, cor:soficnonmf, cor:simplesofic,
   thm:kazhdanfullradical, cor:universalCstarcontrast, thm:nonmfre,
   lem:order's support) and vanish from the anonymous PDF, while
   equally-supporting badges elsewhere print.  Reviewers of the anonymous
   version see an arbitrary subset of the formal surface.  Either drop the
   conditionals or apply them uniformly.
10. **Notation collision on `z`.**  `z` is simultaneously the third CRW
    generator matrix (eq:sl3presentation, used throughout) and the central
    Clifford sign z = −1 (con:clifford, prop:witness, prop:W, thm:C's
    z₀).  Both meanings appear in the *same proof* (prop:witness).
    Renaming the sign (e.g. ζ or ε) would remove genuine ambiguity.
11. `\tag{*}` equation in prop:CEvisible is referenced as "(∗)" only
    inside that proof; harmless but a numbered tag would be house style.
12. Optional: add Elek–Szabó "On sofic groups" (J. Group Theory 9 (2006))
    for the amenable-extension permanence proof (see C above).
13. The manuscript's PDF artifacts under `output/` and the published
    "audited" PDF predate this pass's fixes and need regeneration on the
    cluster.

## F. Process finding

The working tree was being edited concurrently by at least one other
session during this audit (Leiden line and qquad typos disappeared
mid-pass; Rainone bibitem removed).  Cross-session races were the exact
mechanism by which the Leiden regression (finding 1) survived an earlier
purge.  **Implemented this pass:** `scripts/check.py` now carries a
calibrated `fabricated citations` gate that fails CI if "Leiden
Declaration" or the fabricated Zenodo DOI reappears in any root `*.tex`,
`README.md`, or `CITATION.cff` (notes/ audit records are exempt so the
purge history remains describable).  Calibration: clean tree silent, the
planted regression is reported.
