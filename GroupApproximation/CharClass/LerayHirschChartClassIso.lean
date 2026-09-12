import GroupApproximation.CharClass.LerayHirschChartClassGen
import GroupApproximation.CharClass.LerayHirschChartHomeo

/-!
# The class identification, at an arbitrary isomorphism of situations

`pull_chartProdIsoOf_cpGen` states the class identification for the isomorphism built
from a bundle isomorphism.  Its proof never uses where that isomorphism came from,
only that it is one, so the hypothesis is again stronger than the use — the third
time in this lane, and the same cure.

Stated at an arbitrary isomorphism it serves both chart steps, the one built from a
bundle isomorphism and the one built from a homeomorphism over the base, which is
the form `cc-bundle`'s `projTrivStdOn` supplies.

## Main declarations

* `pull_prodIso_cpGen` — **the class identification**, at any isomorphism of
  situations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The class identification, at any isomorphism of situations.**  Under an
isomorphism of the part over `U` with a product, compatible with the projection to
`ℂP^r` and with the tautological lines, the tautological class restricts to the
pulled-back generator. -/
theorem pull_prodIso_cpGen (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (hr : 1 ≤ r)
    (E : opSpace (opensComap (projMapOf p) U)
      ≅ TopCat.of (↥((U : Opens (TopCat.of X)) : Set X) × CP r))
    (chartCP : C(↥(opSpace (opensComap (projMapOf p) U)), CP r))
    (hchart : cmap chartCP = E.hom ≫ KnCP.cpSnd _ r)
    (chartIncl : C(↥(opSpace (opensComap (projMapOf p) U)), Proj p))
    (hincl : LH.opIncl (opensComap (projMapOf p) U) = cmap chartIncl)
    (hrc : r ≤ tautCardOf ι)
    (etaut : BundleIso (comap chartIncl (tautLine p)) (comap chartCP (cpTaut r))) :
    pull E.hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = lhClass (projMapOf p) (tautEulerOf p) U := by
  have hL : pull E.hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = eulerOfBundle hr (comap chartCP (cpTaut r))
          (fun w => trace_cpTaut r (chartCP w)) := by
    rw [eulerOfBundle_comap, ← eulerOfBundle_cpTaut r hr, hchart, pull_comp]
  have hR : lhClass (projMapOf p) (tautEulerOf p) U
      = eulerOfBundle (show 1 ≤ 1 + tautCardOf ι by omega)
          (pushforward (tautEmbOf ι) (tautEmbOf_injective ι)
            (comap chartIncl (tautLine p)))
          (fun w => trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι)
            (tautLine p) (trace_tautLine p) (chartIncl w)) := by
    rw [lhClass, hincl, tautEulerOf, ← eulerOfBundle_comap]
    rfl
  rw [hL, hR]
  exact (eulerOfBundle_pushforward_eq_of_bundleIso' r (1 + tautCardOf ι - r)
    (1 + tautCardOf ι) (by omega) hr
    (comap chartIncl (tautLine p)) (comap chartCP (cpTaut r)) etaut
    (fun w => trace_cpTaut r (chartCP w)) (tautEmbOf_injective ι) _).symm

end

end LH
end CharClass
end GroupApproximation
