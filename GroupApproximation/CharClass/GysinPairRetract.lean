import GroupApproximation.CharClass.GysinRetract
import GroupApproximation.CharClass.GysinPairTaut
import GroupApproximation.CharClass.MayerVietorisPullAmbient

/-!
# The pair condition, in the form the Gysin datum states it

`GysinPairTaut` proves the pair of Mayer–Vietoris restrictions bijective in the
Gysin range.  The datum states its pair condition about the two *readings*, each a
restriction followed by a retraction onto the base.  The two differ by those
retractions, which are isomorphisms on cohomology because they come from homotopy
equivalences, so the conditions are the same statement.

That is all this file does, and it is worth having separately only because the
identification of a Mayer–Vietoris restriction with a pullback along the inclusion
is stated once here in general rather than per-cover.

## Main declarations

* `resU_eq_pull_opIncl`, `resV_eq_pull_opIncl` — the restrictions are pullbacks.
* `bijective_pair_cpTaut` — **the pair condition for the two readings**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

/-- The Mayer–Vietoris restriction to the first open is a pullback along its
inclusion. -/
theorem resU_eq_pull_opIncl {X : TopCat.{0}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (n : ℕ) (a : Hmod2 X n) :
    (mvSequence U V hUV).resU n a = pull (LH.opIncl U) n a := by
  show (mvResU U V hUV n).hom a = _
  rw [mvResU_eq_pull]
  rfl

/-- And so is the restriction to the second. -/
theorem resV_eq_pull_opIncl {X : TopCat.{0}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (n : ℕ) (a : Hmod2 X n) :
    (mvSequence U V hUV).resV n a = pull (LH.opIncl V) n a := by
  show (mvResV U V hUV n).hom a = _
  rw [mvResV_eq_pull]
  rfl

/-- **The pair condition, for the two readings of the Gysin datum.**  The readings
differ from the Mayer–Vietoris restrictions by the retractions onto the base, which
are isomorphisms on cohomology. -/
theorem bijective_pair_cpTaut (d m : ℕ) (hm : m < d) :
    Function.Bijective
      (fun z : Hmod2 (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        (rChart (cpTaut d) (2 * m + 2) z,
          rNotZero (cpTaut d) (trace_cpTaut d) (2 * m + 2) z)) := by
  have hf : Function.Bijective
      (pull (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2)) :=
    (pullEquivOfHomotopyEquiv (chartEquivBase (cpTaut d)) (2 * m + 2)).symm.bijective
  have hg : Function.Bijective
      (pull (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun) (2 * m + 2)) :=
    (pullEquivOfHomotopyEquiv (notZeroEquivBase (cpTaut d) (trace_cpTaut d))
      (2 * m + 2)).symm.bijective
  have hcomp : ∀ z : Hmod2 (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2),
      (rChart (cpTaut d) (2 * m + 2) z,
          rNotZero (cpTaut d) (trace_cpTaut d) (2 * m + 2) z)
        = Prod.map (pull (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2))
            (pull (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun) (2 * m + 2))
            ((mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
                (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
              (mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
                (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z) := by
    intro z
    rw [resU_eq_pull_opIncl, resV_eq_pull_opIncl]
    rfl
  have heq : (fun z : Hmod2 (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        (rChart (cpTaut d) (2 * m + 2) z,
          rNotZero (cpTaut d) (trace_cpTaut d) (2 * m + 2) z))
      = Prod.map (pull (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2))
          (pull (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun) (2 * m + 2))
        ∘ (fun z => ((mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
              (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
            (mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
              (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z)) :=
    funext hcomp
  rw [heq]
  exact (hf.prodMap hg).comp (bijective_resPair_cpTaut d m hm)

end

end Gysin
end CharClass
end GroupApproximation
