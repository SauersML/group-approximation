import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.MFRadicals.MainTheorems

/-!
# Kernel audit for the MF-radical paper package

Every numbered statement of the MF-radical paper is printed here through
`#audit_closed_axioms`, which does two things: it fails the build if the axiom
closure of the proof contains anything beyond `propext`, `Classical.choice` and
`Quot.sound`, and it rejects any declaration whose type begins with a
caller-supplied binder.  The second half is the one that matters for an
existence headline: it is the machine check that a theorem is not quietly
carrying `(hShulman : ...)`, `(hRouter : ...)` or `(hPW : ...)` as an
innocuous-looking manuscript parameter.

The gate deliberately does not unfold a named proposition, so a genuinely
universal statement — "for every finite perfect lamp group, ..." — is advertised
through a named `Prop` (`PerfectLampExactRadical`, `MFSemanticClosure`, ...).
The binders then live inside the proposition rather than in front of it, which
is what "closed" is supposed to mean; nothing below accepts construction data
from a caller.
-/

#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptUniversalMFQuotient
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptMFIffRadicalTrivial
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptSemanticClosure
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptSoundSaturation
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptCompressionCollapse
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptExplicitSeed
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremA
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremB
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremC
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptTheoremD
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyExactRadicals
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilySameVisibleQuotient
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyNoncommensurable
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptMFRadicalPaperSuite

-- The two implementation-level endpoints the new exact-radical half rests on,
-- audited at their own statements so the paper rows above are not the only
-- place the closure is checked.
#audit_axioms GroupApproximation.PerfectLampRadical.actualCoronaMFResidual_eq_lampRange
#audit_axioms GroupApproximation.PerfectLampRadical.lampRange_le_actualCoronaMFResidual
#audit_axioms GroupApproximation.AlternatingLampFamily.alternatingFamilyPackage
#audit_axioms GroupApproximation.AlternatingLampFamily.four_radicals_eq_lampRange

-- The Bohr column, added 2026-08-23.  The closed row is audited as a closed
-- statement, so a leading hypothesis anywhere under it -- a Peter--Weyl
-- binder in particular -- fails the gate rather than passing quietly.
#audit_closed_axioms GroupApproximation.Manuscript.MFRadicals.manuscriptAlternatingFamilyBohrColumn
#audit_axioms GroupApproximation.AlternatingLampFamily.alternatingFamilyRadicalPackage
#audit_axioms GroupApproximation.AlternatingLampFamily.bohrResidual_le_lampRange
#audit_axioms GroupApproximation.AlternatingLampFamily.lampRange_le_ker_of_profinite
