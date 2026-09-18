import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.StableKTwo
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.Steinberg.KervaireSteinberg
import GroupApproximation.Leavitt.BinaryLeavittAllRanksUnits
import GroupApproximation.Sofic.CentralCoverInheritance
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import GroupApproximation.Meta.AxiomGuard

/-!
# Superperfect `L^×` from `K₂(5, L) = ⊥` (lane sk-leavitt-17, part 2)

Let `L = L_{𝔽₂}(1,2)`.  The carto `sk-leavitt` (§2, equivalence warning) observes that the
rank-five gap `LeavittFP.BinaryLeavittSteinbergInjectiveStatement` (`K₂(Fin 5, L) = ⊥`) gives back
the superperfectness of `Lˣ`, `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`: every
central extension `E ↠ Lˣ` with `E` perfect is injective.  This module proves that implication.

## Route

1. `centralExtension_projection_injective_of_section` (formal splitting, any groups).  Let
   `π : E ↠ G` be a central extension with a homomorphic section `s`, and let `E` be perfect.
   Put `ψ(x) = x · s(π x)⁻¹`.  It lies in `ker π ≤ Z(E)`, and centrality makes `ψ` a
   homomorphism with commuting values.  So `ψ` kills every commutator, hence all of
   `E = [E, E]`.  Thus `x = s(π x)` for every `x`, and `π` is injective.
2. `superperfect_of_binaryLeavittSteinbergInjective`.  `K₂(5, L) = ⊥` makes
   `St_5(L) ≃* E_5(L)` (`BooneHigman.SteinbergBasic.equivOfK2EqBot`).  `E_5(L) = GL_5(L) ≅ Lˣ`
   (`UniversalLeavitt.nonempty_unitsMulEquiv_elementaryGroup`, from
   `BinaryLeavitt.elementaryGroup_eq_top` and the prefix-code self-similarity).  Transport the
   central extension `E ↠ Lˣ` to `E ↠ St_5(L)` (`CentralExtension.postcompEquiv`).  It splits by
   Kervaire–Steinberg (`KervaireSteinberg.every_centralExtension_splits`, rank `5 ≥ 5`).  Step 1
   gives injectivity.

## Truth check

Every statement here is an implication between true statements (Khanh, arXiv:2609.08428,
Thm 2.2 and Thm 5.4).  Step 1 is elementary and holds for all groups.
`binaryLeavittUnitsSuperperfect_of_stable` composes with part 1: stable `K₂(L) = 0` together with
injective stability from rank five gives superperfectness.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement

/-- **Formal splitting.**  A perfect central extension with a homomorphic section is injective:
`E = [E, E] ⊆ s(G)`. -/
theorem centralExtension_projection_injective_of_section
    {E G : Type*} [Group E] [Group G] (P : GroupApproximation.CentralExtension E G)
    (s : G →* E) (hs : P.projection.comp s = MonoidHom.id G) (hE : _root_.commutator E = ⊤) :
    Function.Injective P.projection := by
  have hsg : ∀ g : G, P.projection (s g) = g := fun g => by
    simpa using DFunLike.congr_fun hs g
  have hcen : ∀ x : E, x * (s (P.projection x))⁻¹ ∈ Subgroup.center E := fun x => by
    apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, mul_inv_cancel]
  let ψ : E →* E := MonoidHom.mk' (fun x => x * (s (P.projection x))⁻¹) fun x y => by
    have hx : x * (y * (s (P.projection y))⁻¹) = y * (s (P.projection y))⁻¹ * x :=
      Subgroup.mem_center_iff.mp (hcen y) x
    have hx' : x * (s (P.projection x))⁻¹ * (y * (s (P.projection y))⁻¹) =
        y * (s (P.projection y))⁻¹ * (x * (s (P.projection x))⁻¹) :=
      Subgroup.mem_center_iff.mp (hcen y) (x * (s (P.projection x))⁻¹)
    simp only [map_mul, mul_inv_rev]
    calc x * y * ((s (P.projection y))⁻¹ * (s (P.projection x))⁻¹)
        = x * (y * (s (P.projection y))⁻¹) * (s (P.projection x))⁻¹ := by
          simp only [mul_assoc]
      _ = y * (s (P.projection y))⁻¹ * x * (s (P.projection x))⁻¹ := by rw [hx]
      _ = y * (s (P.projection y))⁻¹ * (x * (s (P.projection x))⁻¹) := mul_assoc _ _ _
      _ = x * (s (P.projection x))⁻¹ * (y * (s (P.projection y))⁻¹) := hx'.symm
  have hle : _root_.commutator E ≤ ψ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have h₂ : ψ g₂ ∈ Subgroup.center E := hcen g₂
    exact Subgroup.mem_center_iff.mp h₂ (ψ g₁)
  have hfix : ∀ x : E, x = s (P.projection x) := fun x => by
    have hmem : x ∈ _root_.commutator E := by
      rw [hE]
      exact Subgroup.mem_top x
    have h₁ : x * (s (P.projection x))⁻¹ = 1 := MonoidHom.mem_ker.mp (hle hmem)
    exact mul_inv_eq_one.mp h₁
  intro x y hxy
  calc x = s (P.projection x) := hfix x
    _ = s (P.projection y) := by rw [hxy]
    _ = y := (hfix y).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.centralExtension_projection_injective_of_section

/-- **Superperfect `Lˣ` from `K₂(5, L) = ⊥`.**  `St_5(L) ≅ E_5(L) = GL_5(L) ≅ Lˣ`, and every
central extension of `St_5(L)` splits (Kervaire–Steinberg), so a perfect central extension of
`Lˣ` is injective. -/
theorem superperfect_of_binaryLeavittSteinbergInjective
    (h : GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement := by
  intro E _ P hE
  have h' : GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ := h
  obtain ⟨e⟩ :=
    GroupApproximation.UniversalLeavitt.nonempty_unitsMulEquiv_elementaryGroup (n := 5) (by norm_num)
  let f : GroupApproximation.SteinbergGroup (Fin 5)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≃*
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
    (GroupApproximation.BooneHigman.SteinbergBasic.equivOfK2EqBot h').trans e.symm
  let Q := P.postcompEquiv f.symm
  obtain ⟨s, hs⟩ :=
    GroupApproximation.KervaireSteinberg.every_centralExtension_splits (n := 5) le_rfl Q
  have hQ : Function.Injective Q.projection :=
    centralExtension_projection_injective_of_section Q s hs hE
  intro x y hxy
  apply hQ
  exact congrArg f.symm.toMonoidHom hxy

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.superperfect_of_binaryLeavittSteinbergInjective

/-- **Superperfect `Lˣ` from the two stable ingredients** (stable `K₂(L) = 0` and injective
stability from rank five), through `K₂(5, L) = ⊥`. -/
theorem binaryLeavittUnitsSuperperfect_of_stable
    (hS : BinaryLeavittStableK2TrivialStatement)
    (hT : BinaryLeavittK2FiveStabilityStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  superperfect_of_binaryLeavittSteinbergInjective (binaryLeavittSteinbergInjective_of_stable hS hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittUnitsSuperperfect_of_stable

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
