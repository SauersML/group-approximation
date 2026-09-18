import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPIntPres
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStChar
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# A finite presentation `P m` mapping onto `St_4(ℤ[1/m])` (bh-met-91m)

Generators: `Y α` and `T s` for off-diagonal pairs `α, s` of `Fin 4`.  Relators:

* the relators of `czSLFourFP_IntGroup (Fin 4)` in the letters `Y α`;
* `T s Y α T s⁻¹ = Y α ^ (m ^ χ_s(α))` whenever `χ_s(α) ≥ 0` (`czStFourFP_chi`);
* `(T α T s)⁻¹ (T s T α)` commutes with every generator.

In `St_4(ℤ[1/m])`, `Y α ↦ x_α(1)` and `T s ↦ H_s(m)`.  This file sets up `P m` and its basic
relations; the section `R → P m` of each root subgroup is built in `ElemFPCharZeroStFourFPPTorus`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

/-- Conjugations by `a` and `b` commute when `a b = b a z` with `z` central. -/
theorem czStFourFP_conj_swap {G : Type*} [Group G] {a b z : G} (habz : a * b = b * a * z)
    (hz : ∀ g, g * z = z * g) (h : G) :
    a * (b * h * b⁻¹) * a⁻¹ = b * (a * h * a⁻¹) * b⁻¹ := by
  calc a * (b * h * b⁻¹) * a⁻¹ = a * b * h * (a * b)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
    _ = b * a * z * h * (b * a * z)⁻¹ := by rw [habz]
    _ = b * a * (z * h * z⁻¹) * (b * a)⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    _ = b * a * h * (b * a)⁻¹ := by rw [← hz h, mul_inv_cancel_right]
    _ = b * (a * h * a⁻¹) * b⁻¹ := by simp only [mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_swap

/-- Off-diagonal pairs of `Fin 4`. -/
abbrev czStFourFP_Root : Type := czSLFourFP_Root (Fin 4)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Root

/-- Generators: `Y α` (left) and `T s` (right). -/
abbrev czStFourFP_Gen : Type := czStFourFP_Root ⊕ czStFourFP_Root

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Gen

/-- The letters `Y α` inside the free group on all generators. -/
def czStFourFP_inl : FreeGroup czStFourFP_Root →* FreeGroup czStFourFP_Gen :=
  FreeGroup.map Sum.inl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_inl

/-- The scaling relator `T s Y α T s⁻¹ (Y α ^ m ^ χ)⁻¹` (trivial if `χ < 0`). -/
def czStFourFP_scaleRel (m : ℕ) (s α : czStFourFP_Root) : FreeGroup czStFourFP_Gen :=
  if 0 ≤ czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2 then
    FreeGroup.of (Sum.inr s) * FreeGroup.of (Sum.inl α) * (FreeGroup.of (Sum.inr s))⁻¹ *
      (FreeGroup.of (Sum.inl α) ^ ((m : ℤ) ^ (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat))⁻¹
  else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_scaleRel

/-- The centrality relator `⁅(T α T s)⁻¹ (T s T α), g⁆`. -/
def czStFourFP_centRel (s α : czStFourFP_Root) (g : czStFourFP_Gen) :
    FreeGroup czStFourFP_Gen :=
  ⁅(FreeGroup.of (Sum.inr α) * FreeGroup.of (Sum.inr s))⁻¹ *
      (FreeGroup.of (Sum.inr s) * FreeGroup.of (Sum.inr α)), FreeGroup.of g⁆

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_centRel

/-- The relator set of `P m`. -/
def czStFourFP_rels (m : ℕ) : Set (FreeGroup czStFourFP_Gen) :=
  (czStFourFP_inl '' czSLFourFP_intRels (Fin 4) ∪
      Set.range (fun p : czStFourFP_Root × czStFourFP_Root => czStFourFP_scaleRel m p.1 p.2)) ∪
    Set.range (fun p : czStFourFP_Root × czStFourFP_Root × czStFourFP_Gen =>
      czStFourFP_centRel p.1 p.2.1 p.2.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_rels

instance czStFourFP_rels_finite (m : ℕ) : Finite ↥(czStFourFP_rels m) :=
  ((((Set.toFinite (czSLFourFP_intRels (Fin 4))).image czStFourFP_inl).union
    (Set.finite_range _)).union (Set.finite_range _)).to_subtype

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_rels_finite

/-- The finitely presented group `P m`. -/
abbrev czStFourFP_P (m : ℕ) : Type := PresentedGroup (czStFourFP_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_P

/-- The generator `Y α`. -/
def czStFourFP_Y (m : ℕ) (α : czStFourFP_Root) : czStFourFP_P m :=
  PresentedGroup.of (Sum.inl α)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Y

/-- The generator `T s`. -/
def czStFourFP_T (m : ℕ) (s : czStFourFP_Root) : czStFourFP_P m :=
  PresentedGroup.of (Sum.inr s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_T

theorem czStFourFP_lift_Y (m : ℕ) :
    FreeGroup.lift (czStFourFP_Y m) =
      (PresentedGroup.mk (czStFourFP_rels m)).comp czStFourFP_inl :=
  FreeGroup.ext_hom _ _ fun α => by
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, czStFourFP_inl, FreeGroup.map.of]
    rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_lift_Y

theorem czStFourFP_iota_rels (m : ℕ) : ∀ r ∈ czSLFourFP_intRels (Fin 4),
    FreeGroup.lift (czStFourFP_Y m) r = 1 := by
  intro r hr
  rw [czStFourFP_lift_Y, MonoidHom.comp_apply]
  exact PresentedGroup.one_of_mem
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_image_of_mem czStFourFP_inl hr)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_iota_rels

/-- `y_α ↦ Y α` from the presentation of `St_4(ℤ)`. -/
def czStFourFP_iota (m : ℕ) : czSLFourFP_IntGroup (Fin 4) →* czStFourFP_P m :=
  PresentedGroup.toGroup (czStFourFP_iota_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_iota

theorem czStFourFP_iota_y (m : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    czStFourFP_iota m (czSLFourFP_y (Fin 4) i j hij) = czStFourFP_Y m ⟨(i, j), hij⟩ :=
  PresentedGroup.toGroup.of (czStFourFP_iota_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_iota_y

/-- Commutation relation among the `Y`. -/
theorem czStFourFP_Y_commute (m : ℕ) (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) :
    Commute (czStFourFP_Y m ⟨(i, j), hij⟩) (czStFourFP_Y m ⟨(k, l), hkl⟩) := by
  have h := (czSLFourFP_y_commute (Fin 4) i j k l hij hkl hjk hli).map (czStFourFP_iota m)
  rw [czStFourFP_iota_y m i j hij, czStFourFP_iota_y m k l hkl] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Y_commute

/-- Adjacent relation among the `Y`. -/
theorem czStFourFP_Y_commutator (m : ℕ) (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ⁅czStFourFP_Y m ⟨(i, j), hij⟩, czStFourFP_Y m ⟨(j, k), hjk⟩⁆ =
      czStFourFP_Y m ⟨(i, k), hik⟩ := by
  have h := congrArg (czStFourFP_iota m) (czSLFourFP_y_commutator (Fin 4) i j k hij hjk hik)
  rw [map_commutatorElement, czStFourFP_iota_y m i j hij, czStFourFP_iota_y m j k hjk,
    czStFourFP_iota_y m i k hik] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Y_commutator

/-- The scaling relation `T s Y α T s⁻¹ = Y α ^ m ^ χ` for `χ = χ_s(α) ≥ 0`. -/
theorem czStFourFP_T_conj_Y (m : ℕ) (s α : czStFourFP_Root)
    (h : 0 ≤ czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2) :
    czStFourFP_T m s * czStFourFP_Y m α * (czStFourFP_T m s)⁻¹ =
      czStFourFP_Y m α ^ ((m : ℤ) ^ (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat) := by
  have hmem : czStFourFP_scaleRel m s α ∈ czStFourFP_rels m :=
    Set.mem_union_left _ (Set.mem_union_right _ ⟨(s, α), rfl⟩)
  have h1 := PresentedGroup.one_of_mem hmem
  rw [czStFourFP_scaleRel, if_pos h] at h1
  simp only [map_mul, map_inv, map_zpow] at h1
  exact mul_inv_eq_one.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_T_conj_Y

/-- The centrality relation: `(T α T s)⁻¹ (T s T α)` is central in `P m`. -/
theorem czStFourFP_T_central (m : ℕ) (s α : czStFourFP_Root) (g : czStFourFP_P m) :
    g * ((czStFourFP_T m α * czStFourFP_T m s)⁻¹ * (czStFourFP_T m s * czStFourFP_T m α)) =
      (czStFourFP_T m α * czStFourFP_T m s)⁻¹ * (czStFourFP_T m s * czStFourFP_T m α) * g := by
  refine czStFourFP_commute_of_commute_of (fun a => ?_) g
  have hmem : czStFourFP_centRel s α a ∈ czStFourFP_rels m :=
    Set.mem_union_right _ ⟨(s, α, a), rfl⟩
  have h1 := PresentedGroup.one_of_mem hmem
  simp only [czStFourFP_centRel, map_commutatorElement, map_mul, map_inv] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_T_central

/-- Conjugation by `T s` commutes with conjugation by `T α`. -/
theorem czStFourFP_T_conj_swap (m : ℕ) (s α : czStFourFP_Root) (h : czStFourFP_P m) :
    czStFourFP_T m s * (czStFourFP_T m α * h * (czStFourFP_T m α)⁻¹) * (czStFourFP_T m s)⁻¹ =
      czStFourFP_T m α * (czStFourFP_T m s * h * (czStFourFP_T m s)⁻¹) *
        (czStFourFP_T m α)⁻¹ :=
  czStFourFP_conj_swap (a := czStFourFP_T m s) (b := czStFourFP_T m α)
    (mul_inv_cancel_left _ _).symm (czStFourFP_T_central m s α) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_T_conj_swap

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
