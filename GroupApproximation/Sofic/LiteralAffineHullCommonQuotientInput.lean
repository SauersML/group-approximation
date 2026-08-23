import GroupApproximation.Sofic.LiteralAffineFreeProductSource
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner

/-!
# Concrete source for the first Hull common-quotient stage

The first stage uses the free product of the amplified compression source with
the certified torsion-free Kazhdan partner.  This file records the first
substantive algebraic input to that construction: the whole source from which
finite-order elements must lift is torsion-free.
-/

namespace GroupApproximation.LiteralAffineHullCommonQuotientInput

open LiteralAffineFreeProductSource

/-- The whole torsion-free source used in the first common-quotient stage. -/
abbrev Source : Type :=
  Monoid.Coprod Ambient CongruenceSubgroup.gamma3Partner.B

/-- Both factors of the first-stage source are torsion-free, hence so is their
free product. -/
theorem source_isPowerTorsionFree : IsPowerTorsionFree Source :=
  Higman.isPowerTorsionFree_coprod ambient_isPowerTorsionFree
    CongruenceSubgroup.gamma3Partner.torsionFree

end GroupApproximation.LiteralAffineHullCommonQuotientInput
