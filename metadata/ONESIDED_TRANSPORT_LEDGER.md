# One-sided Kazhdan transport: statement-to-declaration ledger

One row per numbered statement and per displayed equation of
`non_mf_groups_exist.tex` (*One-sided Kazhdan transport and MF radicals*).
Each row names the Lean declaration that carries it.
`scripts/check_onesided_transport_ledger.py` enforces four things
mechanically:

1. every declaration named below exists in the Lean development;
2. every declaration named below is printed in
   `GroupApproximation/Endpoint/OneSidedTransportAudit.lean`, so its axiom
   closure and its zero-input status are checked by the build;
3. every `#audit_closed_axioms` line of that audit file appears below, so the
   ledger cannot silently omit a headline;
4. every `\label{...}` of the manuscript other than the section labels has a
   row, so a new numbered statement cannot be printed without one.

There is no "proof is analogous" row and no prose claim stronger than the
declaration receiving the badge.

## What the three statuses mean

`closed` — the declaration is printed with `#audit_closed_axioms`.  That macro
fails the build both when the axiom closure reaches beyond `propext`,
`Classical.choice`, `Quot.sound` and when the declaration's type begins with a
caller-supplied binder.  A green build is therefore a machine proof that the
row is unconditional: the manuscript's quantifiers live inside a named `Prop`,
and nothing is accepted as mathematical input from a caller.

`conditional` — the declaration is printed with the weaker `#audit_axioms` and
is **not** printed with the closed macro.  Its type begins with a binder.  Two
different things put a binder there, and this ledger separates them by name
rather than by status, because the status vocabulary cannot:

* **an undischarged mathematical hypothesis.**  Two rows expose the same gap:
  the explicit simplicity reduction and `thm:headline`.  Their exact wrappers
  take `NormalRootDetection`, which has no proof in the repository; see
  *Deliberately not claimed*.
* **manuscript data the statement is universally quantified over** — the
  ambient group, the coefficient ring, the Leavitt family, the homomorphism.
  Rows `eq:intrinsic-defect`, `eq:matrix-compression`,
  `eq:defect-functoriality`, `eq:corner-conjugation` and `eq:amalgam` are of
  this kind, and each is strictly more general than what the manuscript
  prints.  Nothing is assumed in them; `#audit_closed_axioms` rejects them
  only because a definition or a lemma over arbitrary data cannot have an
  empty telescope.  Every one of the five is *used* by a closed row: the
  defect rows by `manuscriptCompleteOneSidedCompressionCriterion` and
  `manuscriptDefectSaturation`, the Leavitt rows by
  `RankTwelveEndpoint.printedDefectConfiguration`, and `eq:amalgam` by
  `manuscriptPrescribedMFQuotients`.  So none of the five can be wrong without
  a closed row failing.

`MISSING` — no declaration in the development proves the row.  A `MISSING`
row's target may exist as a *statement* (a `def ... : Prop`); the gate refuses
to let it be printed in the audit under either macro, and refuses to let it
become a `theorem` without the row being updated.

Manuscript state pinned at authoring time: 1234 lines,
`sha256 0cc88f62...d8d7a778a`, 29 labelled statements.  The table has 45 rows
-- 37 `closed`, 7 `conditional`, 1 `MISSING`, naming 44 distinct declarations.
One row per label, and sixteen further rows: some split a printed theorem into
the constituents that are separately audited, the rest cover a printed
sentence that carries no number.  One declaration appears twice, because the
introduction displays a corollary that Section 3 then states.  Re-pin after
reviewing the rows an edit to the `.tex` touches.

## Rows

<!-- LEDGER-ROWS -->
| Paper | Lean declaration | Status |
| --- | --- | --- |
| `prop:mf-residual-calculus` MF residual calculus, on the literal MF closure | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculusLiteral` | closed |
| `prop:mf-residual-calculus` again, on the corona closure | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculus` | closed |
| Sec. 1 display, `cl_MF^G(N)` as the intersection of MF-target kernels, and as the quotient pullback | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptLiteralMFClosureIsQuotientPullback` | closed |
| Sec. 1 display, `Rad_MF(G) = cl_MF^G(1)` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFRadicalIsLiteralClosureOfTrivial` | closed |
| Sec. 1, a full radical kills every homomorphism to an MF group | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets` | closed |
| `eq:intrinsic-defect` the compression-centralizer defect | `GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect` | conditional |
| Theorem A `thm:compression-criterion`, all four printed clauses | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompleteOneSidedCompressionCriterion` | closed |
| Theorem A, the three MF-radical clauses | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion` | closed |
| Theorem A, fourth clause: every finite-dimensional linear representation over every field kills the defect | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFiniteDimensionalSterility` | closed |
| `eq:leavitt` the binary Leavitt relations, at the manuscript's ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.leavittFamily` | closed |
| `prop:simple`, exact reduction from the missing root-detection input | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittSimplicityClause` | conditional |
| Theorem B `thm:headline`, every printed clause, simplicity included | `GroupApproximation.Manuscript.OneSidedMFRadical.headlineConclusion_of_normalRootDetection` | conditional |
| Theorem B minus the simplicity clause, hypothesis-free | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittFullRadical` | closed |
| Theorem B, displayed conclusion `Rad_MF(H) = H` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top` | closed |
| Theorem B, structural clauses: nontrivial, countable, finitely generated, property (T), and `d` nontrivial and normally generating | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.closedStructuralProfile` | closed |
| `eq:basic-defect` the Hilbert--Schmidt display of `cor:defect-hs` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible` | closed |
| Sec. 1, faithful finite-dimensional, residually finite and finite-`L` sterility | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectSterility` | closed |
| Sec. 1, the amenable clause: property (T) plus amenable gives finite, hence a trivial defect | `GroupApproximation.manuscriptAmenableKazhdanSterility` | closed |
| Theorem C `thm:prescribed-quotients` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedMFQuotients` | closed |
| `thm:commutant` finite-dimensional commutant rigidity | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFiniteDimensionalCommutantRigidity` | closed |
| `eq:shadow-residual` `R_inf-to-2(G)` as the intersection of the `K_2(V)`, with `K_2(V)` in its printed ordinary-limit form and normal | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsIntersectionOfHSKernels` | closed |
| Sec. 3, `R_inf-to-2(G)` is normal and fully invariant | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsNormal` | closed |
| `lem:stable-finite` stable finiteness and projection comparison | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormMatrixCoronaStableFinite` | closed |
| `lem:kazhdan-projection-order` one-sided order for the Kazhdan projection | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanProjectionOrder` | closed |
| `thm:transport` one-sided Kazhdan transport, both conjugation directions | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransport` | closed |
| `cor:defect-hs` defect generators lie in the shadow residual | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible` | closed |
| `lem:central-corona-corner` central corona corners | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCentralCoronaCorner` | closed |
| `thm:normal-kazhdan` normal Kazhdan radical theorem, at the printed natural-dimension radical | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanPrintedRadical` | closed |
| `thm:normal-kazhdan` again, at the basis-free radical | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanRadical` | closed |
| Proof of `thm:normal-kazhdan`, closing sentence: every corona homomorphism kills `K` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanCoronaVanishing` | closed |
| Proof of Theorem A, the four printed links in printed order | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCriterionAssembly` | closed |
| Proof of Theorem A, first step: the printed defect lies in the shadow residual | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectShadowInclusion` | closed |
| Proof of Theorem A, second step: normal Kazhdan subgroups of the printed defect | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectNormalKazhdanRadical` | closed |
| Theorem A unfolded: such a subgroup is killed by every natural-dimension corona representation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectCoronaVanishing` | closed |
| `prop:defect-saturation` functoriality and saturation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptDefectSaturation` | closed |
| `eq:defect-functoriality` the image inequality itself | `GroupApproximation.Manuscript.OneSidedMFRadical.map_printedDefect_to_range_le` | conditional |
| `eq:pq` `q` is nonzero at the manuscript's ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.q_ne_zero` | closed |
| `eq:matrix-compression` the unital injective endomorphism `Psi` | `GroupApproximation.LeavittFamily.matrixCompression` | conditional |
| `eq:tau` `tau = diag(X, Y)` as a unit of the twelve-by-twelve matrix ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL` | closed |
| `eq:whitehead-factorization` the six block-unipotent factors | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tauUnit_eq_six_elementary` | closed |
| Sec. 5, `tau` belongs to the elementary group | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL_mem` | closed |
| Sec. 5, the upper-left corner has property (T) | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.corner_hasKazhdanPropertyT` | closed |
| `eq:corner-conjugation` `tau diag(A, I) tau^-1 = diag(Psi(A), I)` | `GroupApproximation.RankTwelve.tau_fullCorner_tauInv` | conditional |
| `eq:compresses-L` `tau L tau^-1` is contained in `L` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedDefectConfiguration` | closed |
| `prop:simple` simplicity of the rank-twelve elementary group | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.PropositionSimple` | MISSING |
| `prop:defect` the explicit centralizer mark, commutator, and normal generation | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionDefect` | closed |
| `eq:moved-mark` `tau c tau^-1 = e01(q) e34(1)` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_c` | closed |
| `eq:amalgam` the amalgam `W_Q = B *_A (Q x A)` | `GroupApproximation.MFCamouflage.Camouflage` | conditional |
| Sec. 7, the projection is a split epimorphism, both vertex maps are injective, and `d` survives | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSplitPrescribedProjection` | closed |
| `prop:universal-factorization` universal factorization through the projection | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptUniversalFactorization` | closed |
| `eq:closure-pullback` MF closure pulls back, and the MF-quotient criterion for the amalgam | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedQuotientRelationCalculus` | closed |
<!-- END-LEDGER-ROWS -->

## Deliberately not claimed

* **`prop:simple`, simplicity of `H = EL_12(L_F2(1,2))`.**  The manuscript
  proves it from Preusser's normal-subgroup theorem for general linear groups
  over exchange rings, together with pure infiniteness and simplicity of the
  binary Leavitt algebra and triviality of its unit-scalar center.  None of
  that normal-structure bridge exists in the repository: there is no Preusser
  theorem, no relative elementary subgroup, no congruence subgroup `C_n(R, I)`,
  and no `IsSimpleGroup` for any elementary group.  The statement is kept as
  the named proposition `RankTwelveEndpoint.PropositionSimple` so that no audit
  can confuse it with what *is* proved, namely that every nonzero elementary
  root normally generates `H`
  (`RankTwelveEndpoint.normalClosure_defect_eq_top`).  Root normal generation
  is strictly weaker and is not a substitute.
  The headline does not depend on it: `Rad_MF(H) = H` is a closed row above
  (`rankTwelve_actualCoronaMFResidual_eq_top`), proved through normal
  generation of the single element `d = e02(q)` rather than through simplicity.
  Only the printed adjective *simple*, and the sentence deriving triviality of
  every homomorphism to an MF group from it, remain conditional.
* **The amenable clause of the Section 1 sterility paragraph.**  "If `G` is
  amenable, its property-(T) subgroup `L` is finite" is Bekka--de la
  Harpe--Valette and is not in the repository.  The group-theoretic half that
  the manuscript then uses -- `L` finite implies `u L u^-1 = L` implies a
  trivial defect -- is proved and is the third conjunct of the closed row
  `manuscriptPrintedDefectSterility`.  The row does not claim the amenable
  hypothesis.
* **Property (T) for `EL_n` over a finitely generated ring** is cited to
  Ershov--Jaikin-Zapirain in the manuscript but is *not* a citation here: the
  two property-(T) rows above are proved in the development from
  `finiteFieldElementaryThree_hasKazhdanPropertyT` and the rank transport, with
  no external input.  The ledger claims the Lean proof, not the citation.

## Fidelity notes

Places where the Lean statement and the printed sentence are not word for word.
Each is a deliberate, recorded choice, and in every case the Lean statement is
at least as strong as the printed one.

* **`Comp_G(L)` is a set, not a group.**  The manuscript takes the normal
  closure of the commutators over the *set* of one-sided compressors.  The
  development also has `compressionCentralizerDefect`, which conjugates by the
  subgroup they generate.  `printedDefect` is the printed object, and
  `printedDefect_le_compressionCentralizerDefect` is the containment, which
  runs in the favourable direction: an obstruction theorem for the larger
  subgroup implies the printed one.  Every row above is stated on
  `printedDefect`.
* **`lem:kazhdan-projection-order` does not route through `C*_max(L)`.**  The
  printed lemma takes `P` to be the image of the Kazhdan projection under
  `C*_max(L) -> B`.  The Lean endpoint constructs the projection directly in
  the target algebra as the spectral projection of the orbit average at the
  isolated point `1`, which is what the printed proof of `thm:transport`
  actually consumes.  The order `U* P U <= P` is stated as its two absorption
  identities, because a general `CStarAlgebra` carries no global order
  instance; the module documents the one-line rewrite to the displayed
  inequality once a caller installs `CStarAlgebra.spectralOrder`.
* **`lem:stable-finite`** states the projection comparison in ring form
  (`q * p = p` for `p <= q`), for the same reason.
* **`cl_MF` has two spellings.**  `literalMFClosure` is the printed
  intersection over MF targets; `actualCoronaMFClosure` is the quotient
  pullback used elsewhere in the development.  They are equal
  (`literalMFClosure_eq_actualCoronaMFClosure`), which is why
  `eq:closure-pullback` may be carried by a statement phrased with the second.
* **`K_2(V)` uses ordinary convergence.**  The development's shadow residual is
  defined through ultrafilters; `manuscriptShadowResidualIsIntersectionOfHSKernels`
  supplies the printed ordinary-limit presentation and the identification.
* **`eq:basic-defect` and `cor:defect-hs` share a carrier.**  The introduction
  displays the corollary; there is one declaration and two rows, rather than a
  second declaration restating the first.
* **`eq:defect-functoriality` is also the first clause of the closed
  `manuscriptDefectSaturation`.**  Its own row names the standalone inequality,
  which is `conditional` only because it quantifies over `f` and `L` in front.
* **`H` is `BinaryLeavittSteinberg.ElementaryBase 12`**, which is by definition
  `elementaryGroup (Fin 12) UniversalLeavitt.BinaryLeavittAlgebra`, i.e.
  `EL_12(L_F2(1,2))`.  Universes: the analytic endpoints are stated at
  `Type 0` with `HasKazhdanPropertyT.{0,0}`, matching the manuscript's
  countable-group hypothesis.

## Auxiliary declarations

The audit file also prints, with the weaker `#audit_axioms`, the
implementation lemmas that the rows above are assembled from: the defect
generators and the bridge to `compressionCentralizerDefect`; the Leavitt
relations `p + q = 1` and `t1 q s1 = 1`; unitality, multiplicativity,
injectivity and the elementary-matrix formula for `Psi`; the matrices `X`,
`Y`, their inverse identities, the nested `tau`, and the Whitehead
factorization over an arbitrary Leavitt family; the concrete rank-twelve
compression, conjugation and commutator identities; and the amalgam's
projection and vertex injectivity.  They are not rows: a row is a printed
statement, and these are the parts.
