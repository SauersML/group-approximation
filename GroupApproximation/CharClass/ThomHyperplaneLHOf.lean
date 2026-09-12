import GroupApproximation.CharClass.ThomHyperplaneLH
import GroupApproximation.CharClass.ThomBridgeTotalOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Leray–Hirsch on the hyperplane, and the Thom data over one class restriction, over `K`

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomHyperplaneLH` presents the hyperplane at infinity of `P(p ⊕ 1)` as `P(p)` over the base,
transports Leray–Hirsch across that identification, and reduces the degreewise Thom data of
the vector-bundle pair to one named input: the tautological class of `P(p ⊕ 1)` restricts to
that of `P(p)`.  The transport (`lerayHirschGraded_of_iso`) is already over any ring and the
identification is topology, so over `K` only the Leray–Hirsch instances change.  Here they are
arguments: over `F₂` they come from `lerayHirschGraded_compact`, and over `K` they come from its
`K`-form (`lix-lh`).

## Main declarations

* `hyperLHOf` — Leray–Hirsch on the hyperplane over `K`, from Leray–Hirsch on `P(p)`.
* `thomData_total_of_tautOf` — the degreewise Thom data of the vector-bundle pair over a
  field, over the class restriction `htaut`.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Leray–Hirsch on the hyperplane over `K`**, presented as a subset of `P(p ⊕ 1)`, from a
Leray–Hirsch instance on `P(p)`.  The class is defined as the transport. -/
theorem hyperLHOf {K : Type} [CommRing K] [CompactSpace X] [T2Space X] (p : Bundle X ι)
    {r : ℕ} {ξ : Hmod K (TopCat.of (Bundle.Proj p)) 2}
    (L : LerayHirschGraded (projMapOf p) ξ r) :
    LerayHirschGraded (hyperProj p) (pull (hyperIso p).hom 2 ξ) r :=
  lerayHirschGraded_of_iso (hyperIso p) (projMapOf p) (hyperProj p)
    (hyperIso_hom_comp p) ξ _ rfl L

/-- **The degreewise Thom data of the vector-bundle pair over a field, over one class
restriction.**  `htaut` says the Leray–Hirsch class of `P(p ⊕ 1)` restricts to the transported
class of `P(p)`. -/
theorem thomData_total_of_tautOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) {r : ℕ} (hr : 1 ≤ r)
    {ξPlus : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    {ξ : Hmod K (TopCat.of (Bundle.Proj p)) 2}
    (htaut : pull (sInclusion (Set.range (Bundle.projIncl p))) 2 ξPlus
      = pull (hyperIso p).hom 2 ξ)
    (LPlus : LerayHirschGraded (projMapOf p.plusOne) ξPlus (r + 1))
    (L : LerayHirschGraded (projMapOf p) ξ r) :
    ∃ (jm : ↥(relCohomology K (TopCat.of (Bundle.Total p))
          ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
          (2 * r))
        →ₗ[K] ((i : Fin (r + 1)) → Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := K)
        (M := fun i : Fin (r + 1) => Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMulOf (hyperLHOf p L) i)) :=
  thomData_total_of_lerayHirschOf K p (hyperProj p) rfl ξPlus
    (pull (hyperIso p).hom 2 ξ) htaut hr LPlus (hyperLHOf p L)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms thomData_total_of_tautOf

end ThomChernDeg

end

end GroupApproximation.CharClass
