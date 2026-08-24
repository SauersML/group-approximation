# MF-radical paper: statement-to-declaration ledger

One row per numbered statement of the MF-radical package. Each row names the
Lean declaration that carries it. `scripts/check_mf_radical_ledger.py` enforces
three things mechanically:

1. every declaration named below exists in the Lean development;
2. every declaration named below is printed in
   `GroupApproximation/Endpoint/MFRadicalPaperAudit.lean`, so its axiom closure
   and its zero-input status are checked by the build;
3. every `#audit_closed_axioms` line of that audit file appears below, so the
   ledger cannot silently omit a headline.

There is no "proof is analogous" row and no prose claim stronger than the
declaration receiving the badge. A row is `closed` only when the declaration
has an empty outer telescope and audits to `propext`, `Classical.choice`,
`Quot.sound`.

## Rows

<!-- LEDGER-ROWS -->
| Paper | Lean declaration | Status |
| --- | --- | --- |
| Prop. 2.1 (universal MF quotient) | `GroupApproximation.Manuscript.MFRadicals.manuscriptUniversalMFQuotient` | closed |
| Prop. 2.2 (MF iff trivial radical) | `GroupApproximation.Manuscript.MFRadicals.manuscriptMFIffRadicalTrivial` | closed |
| Theorem E (semantic closure) | `GroupApproximation.Manuscript.MFRadicals.manuscriptSemanticClosure` | closed |
| Prop. 2.3 (sound saturation) | `GroupApproximation.Manuscript.MFRadicals.manuscriptSoundSaturation` | closed |
| Theorem 3.1 (compression engine) | `GroupApproximation.Manuscript.MFRadicals.manuscriptCompressionCollapse` | closed |
| Seed theorem (explicit invisible relation) | `GroupApproximation.Manuscript.MFRadicals.manuscriptExplicitSeed` | closed |
| Theorem A (f.p. Kazhdan full radical) | `GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremA` | closed |
| Theorem B (simple sofic full radical) | `GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremB` | closed |
| Theorem C (perfect-lamp exact radical) | `GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremC` | closed |
| Theorem D (radical computer) | `GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremD` | closed |
| Cor. C.1 (alternating family, four radicals) | `GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyExactRadicals` | closed |
| Cor. C.2 (common visible quotient) | `GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilySameVisibleQuotient` | closed |
| Cor. C.3 (pairwise noncommensurable) | `GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyNoncommensurable` | closed |
| Cor. C.4 (Bohr column, one direction) | `GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyBohrColumn` | closed |
| Cor. C.5 (Hom-set factorization) | `GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyTargetEquivalence` | closed |
| Theorem suite (abstract) | `GroupApproximation.Manuscript.MFRadicals.manuscriptMFRadicalPaperSuite` | closed |
<!-- END-LEDGER-ROWS -->

## Deliberately not advertised

Two statements the package could be extended with are **not** claimed anywhere
above, and no row depends on either:

* the **exact** radical of the literal seed `E`, which reduces to a single
  remaining statement -- that the symmetric double `Σ *_B Σ` is MF. The
  algebraic half is done (`Sofic/TerminalQuotientIso` identifies the quotient);
  the analytic half is isolated, not proved, in `Sofic/SymmetricDoubleMF` and
  `Sofic/SymmetricDoubleShulman`, which also rule out the tempting RF/LEF
  shortcut.
* the fifth (Bohr) radical as an **equality**. Cor. C.4 claims only what is
  proved without Peter--Weyl: the Bohr residual is contained in the lamp
  subgroup, and every homomorphism into a profinite target kills that subgroup.
  So on totally disconnected compact targets the fifth theory agrees with the
  other four, and on general compact targets it can see at most what they see.
  The missing direction, `lampSub n <= bohrResidual (WAlt n)` for a *connected*
  compact target, is Peter--Weyl -- isolated as `PeterWeyl.SeparatesPoints` in
  `Sofic/FiveRadicalsCoincide` -- and is assumed nowhere. The four-radical
  statement in Cor. C.1 does not use it either.

## Adjectives

Three different strengths of "explicit" appear in the package and are not
interchangeable:

* the literal seed `E` has actual generators and relators -- *explicit finitely
  presented group*;
* the Hilbert-hotel model is the named group `EL_16(L_{F_2}(1,2))` -- *explicit
  finitely generated group*;
* the Hilbert-hotel cover is built from chosen cover data. Lean proves finite
  presentability, and the repository does not print a canonical relator list for
  it, so Theorem A is stated as *there exists a finitely presented
  property-(T) group with full MF radical* and is never called an explicit
  finite presentation.
