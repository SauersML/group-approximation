import GroupApproximation.CharClass.GysinPairRetract
import GroupApproximation.CharClass.GysinPairTautOf
import GroupApproximation.CharClass.GysinRetractOf
import GroupApproximation.CharClass.MayerVietorisPullOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Gysin pair condition for the two readings, over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`GysinPairRetract.lean` shows, at `F₂`, that the two readings `rChart`, `rNotZero` of the
Gysin datum are jointly bijective in the Gysin range: they differ from the Mayer–Vietoris
restrictions by the retractions onto the base, which are isomorphisms on cohomology.  Over a
field `K` the restrictions are pullbacks by `lix-lh`'s `mvResUOf_eq_pull` /
`mvResVOf_eq_pull`, the retractions are isomorphisms by `pullEquivOfHomotopyEquivOf K`, and
the restrictions are jointly bijective by `bijective_resPair_cpTautOf`.

## Main declarations

* `resU_eq_pull_opInclOf`, `resV_eq_pull_opInclOf` — the restrictions of `mvSequenceOf K` are
  pullbacks along the inclusions.
* `bijective_pair_cpTautOf` — **the pair condition over a field**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

/-- The Mayer–Vietoris restriction to the first open, over a field, is a pullback along its
inclusion. -/
theorem resU_eq_pull_opInclOf (K : Type) [Field K] {X : TopCat.{0}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (a : Hmod K X n) :
    (mvSequenceOf K U V hUV).resU n a = pull (LH.opIncl U) n a := by
  show (mvResUOf K U V hUV n).hom a = _
  rw [mvResUOf_eq_pull]
  rfl

/-- And so is the restriction to the second. -/
theorem resV_eq_pull_opInclOf (K : Type) [Field K] {X : TopCat.{0}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (a : Hmod K X n) :
    (mvSequenceOf K U V hUV).resV n a = pull (LH.opIncl V) n a := by
  show (mvResVOf K U V hUV n).hom a = _
  rw [mvResVOf_eq_pull]
  rfl

/-- **The pair condition for the two readings of the Gysin datum, over a field.** -/
theorem bijective_pair_cpTautOf (K : Type) [Field K] (d m : ℕ) (hm : m < d) :
    Function.Bijective
      (fun z : Hmod K (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        (rChartOf K (cpTaut d) (2 * m + 2) z,
          rNotZeroOf K (cpTaut d) (trace_cpTaut d) (2 * m + 2) z)) := by
  have hf : Function.Bijective
      (pull (K := K) (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2)) :=
    (pullEquivOfHomotopyEquivOf K (chartEquivBase (cpTaut d)) (2 * m + 2)).symm.bijective
  have hg : Function.Bijective
      (pull (K := K) (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun)
        (2 * m + 2)) :=
    (pullEquivOfHomotopyEquivOf K (notZeroEquivBase (cpTaut d) (trace_cpTaut d))
      (2 * m + 2)).symm.bijective
  have hcomp : ∀ z : Hmod K (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2),
      (rChartOf K (cpTaut d) (2 * m + 2) z,
          rNotZeroOf K (cpTaut d) (trace_cpTaut d) (2 * m + 2) z)
        = Prod.map (pull (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2))
            (pull (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun) (2 * m + 2))
            ((mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
                (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
              (mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
                (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z) := by
    intro z
    rw [resU_eq_pull_opInclOf, resV_eq_pull_opInclOf]
    rfl
  have heq : (fun z : Hmod K (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        (rChartOf K (cpTaut d) (2 * m + 2) z,
          rNotZeroOf K (cpTaut d) (trace_cpTaut d) (2 * m + 2) z))
      = Prod.map (pull (cmap (chartEquivBase (cpTaut d)).invFun) (2 * m + 2))
          (pull (cmap (notZeroEquivBase (cpTaut d) (trace_cpTaut d)).invFun) (2 * m + 2))
        ∘ (fun z => ((mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
              (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
            (mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
              (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z)) :=
    funext hcomp
  rw [heq]
  exact (hf.prodMap hg).comp (bijective_resPair_cpTautOf K d m hm)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms bijective_pair_cpTautOf

end

end Gysin
end CharClass
end GroupApproximation
