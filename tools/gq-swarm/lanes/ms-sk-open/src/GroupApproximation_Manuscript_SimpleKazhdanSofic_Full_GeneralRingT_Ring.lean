import GroupApproximation.Dynamics.ClopenGroupCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The ring `R = LC(C,F_2) ⋊ Λ` and the word balls `B_m`

`simple_kazhdan_sofic_group.tex`, Section `sec:proof`, "The ring and property (T)":

> Write `e_U` for the indicator of a clopen set `U ⊆ C`.  The ring `R = ⊕_{ξ∈Λ} LC(C,F_2) u_ξ` has
> the multiplication `(f u_ξ)(f' u_η) = f (f'∘ξ⁻¹) u_{ξη}`, so `u_ξ e_U u_ξ⁻¹ = e_{ξU}`.  Fix a
> finite symmetric generating set of `Λ`, let `|ξ|` be the word length, and put
> `B_m = {ξ ∈ Λ : |ξ| ≤ m}`.

The ring is `ClopenGroupCrossedProduct Λ C (ZMod 2)` (`GroupApproximation.Dynamics`), the skew
group ring of `LC(C,F_2)` with `ξ • f = f ∘ ξ⁻¹`.

* `printedGeneralRing`: the direct sum decomposition (existence and uniqueness of the expansion),
  the multiplication rule and the covariance `u_ξ e_U u_ξ⁻¹ = e_{ξU}`, for every group acting by
  homeomorphisms on every space, as a closed statement.
* `wordBall T m`: the elements that are products of at most `m` letters of `T`, i.e. `B_m`.
* `exists_mem_wordBall`: when `T` is symmetric and generates `Λ`, every `ξ` lies in some `B_m`.
-/

namespace GroupApproximation.Full.SK03

/-! ## The ring -/

/-- **The ring** (`sec:proof`, "The ring and property (T)"), with `k = F_2 = ZMod 2`:
1. every `r ∈ R` is a finite sum `∑_{ξ ∈ S} f_ξ u_ξ` with `f_ξ ∈ LC(C,F_2)`;
2. the coefficients of such an expansion over `S` are unique, so `R = ⊕_{ξ∈Λ} LC(C,F_2) u_ξ`;
3. `(f u_ξ)(f' u_η) = f (f'∘ξ⁻¹) u_{ξη}`;
4. `u_ξ e_U u_ξ⁻¹ = e_{ξU}` for every clopen `U`. -/
def PrintedGeneralRing : Prop :=
  ∀ (Λ : Type) [Group Λ] (C : Type) [TopologicalSpace C] [MulAction Λ C]
    [ContinuousConstSMul Λ C],
    (∀ r : ClopenGroupCrossedProduct Λ C (ZMod 2),
      ∃ (S : Finset Λ) (f : Λ → LocallyConstant C (ZMod 2)),
        r = ∑ ξ ∈ S, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (f ξ) *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
            ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
    (∀ (S : Finset Λ) (f g : Λ → LocallyConstant C (ZMod 2)),
      ∑ ξ ∈ S, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (f ξ) *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
            ClopenGroupCrossedProduct Λ C (ZMod 2)) =
        ∑ ξ ∈ S, ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (g ξ) *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ : ClopenGroupCrossedProduct Λ C (ZMod 2)) →
      ∀ ξ ∈ S, f ξ = g ξ) ∧
    (∀ (ξ η : Λ) (f f' : LocallyConstant C (ZMod 2)),
      (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ :
            ClopenGroupCrossedProduct Λ C (ZMod 2))) *
        (ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) f' *
          (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) η : ClopenGroupCrossedProduct Λ C (ZMod 2))) =
      ClopenGroupCrossedProduct.coeff Λ C (ZMod 2)
          (f * LocallyConstant.comap (ClopenGroupCoeff.smulMap Λ C ξ⁻¹) f') *
        (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) (ξ * η) :
          ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
    (∀ (ξ : Λ) (U : Set C) (hU : IsClopen U),
      (ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ : ClopenGroupCrossedProduct Λ C (ZMod 2)) *
          ClopenGroupCrossedProduct.coeff Λ C (ZMod 2) (LocallyConstant.charFn (ZMod 2) hU) *
          ((ClopenGroupCrossedProduct.unit Λ C (ZMod 2) ξ)⁻¹ :
            (ClopenGroupCrossedProduct Λ C (ZMod 2))ˣ) =
        ClopenGroupCrossedProduct.coeff Λ C (ZMod 2)
          (LocallyConstant.charFn (ZMod 2) (ClopenGroupCrossedProduct.isClopen_smul_set Λ C ξ hU)))

theorem printedGeneralRing : PrintedGeneralRing := by
  intro Λ _ C _ _ _
  refine ⟨ClopenGroupCrossedProduct.exists_sum_coeff_mul_unit Λ C (ZMod 2),
    ClopenGroupCrossedProduct.eq_of_sum_coeff_mul_unit_eq Λ C (ZMod 2),
    ClopenGroupCrossedProduct.coeff_mul_unit_mul_coeff_mul_unit Λ C (ZMod 2), ?_⟩
  intro ξ _ hU
  exact ClopenGroupCrossedProduct.unit_mul_charFn_mul_inv Λ C (ZMod 2) ξ hU

#audit_closed_axioms GroupApproximation.Full.SK03.printedGeneralRing

/-! ## The word balls `B_m` -/

section WordBall

variable {Λ : Type*} [Group Λ]

/-- **`B_m`** (`sec:proof`): the elements of word length at most `m` in the letters `T`, i.e. the
products of lists of at most `m` elements of `T`. -/
def wordBall (T : Set Λ) (m : ℕ) : Set Λ :=
  {ξ | ∃ l : List Λ, l.length ≤ m ∧ (∀ x ∈ l, x ∈ T) ∧ l.prod = ξ}

theorem one_mem_wordBall (T : Set Λ) (m : ℕ) : (1 : Λ) ∈ wordBall T m :=
  ⟨[], Nat.zero_le m, fun _ hx => absurd hx List.not_mem_nil, List.prod_nil⟩

theorem mem_wordBall_one {T : Set Λ} {x : Λ} (hx : x ∈ T) : x ∈ wordBall T 1 := by
  refine ⟨[x], Nat.le_refl 1, fun y hy => ?_, List.prod_singleton⟩
  rw [List.mem_singleton.1 hy]
  exact hx

/-- `B_m B_{m'} ⊆ B_{m+m'}`. -/
theorem mul_mem_wordBall {T : Set Λ} {m m' : ℕ} {ξ η : Λ} (hξ : ξ ∈ wordBall T m)
    (hη : η ∈ wordBall T m') : ξ * η ∈ wordBall T (m + m') := by
  obtain ⟨l, hl, hlT, rfl⟩ := hξ
  obtain ⟨l', hl', hlT', rfl⟩ := hη
  refine ⟨l ++ l', ?_, fun x hx => ?_, List.prod_append⟩
  · rw [List.length_append]
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · exact hlT x hx
    · exact hlT' x hx

/-- For a symmetric `T`, `B_m⁻¹ = B_m`. -/
theorem inv_mem_wordBall {T : Set Λ} (hT : ∀ x ∈ T, x⁻¹ ∈ T) {m : ℕ} {ξ : Λ}
    (hξ : ξ ∈ wordBall T m) : ξ⁻¹ ∈ wordBall T m := by
  obtain ⟨l, hl, hlT, rfl⟩ := hξ
  refine ⟨(l.map fun x => x⁻¹).reverse, ?_, fun x hx => ?_, (List.prod_inv_reverse l).symm⟩
  · rw [List.length_reverse, List.length_map]
    exact hl
  · rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hT y (hlT y hy)

/-- The union of the balls `B_m` of a symmetric set, as a subgroup. -/
def wordBallSubgroup (T : Set Λ) (hT : ∀ x ∈ T, x⁻¹ ∈ T) : Subgroup Λ where
  carrier := {ξ | ∃ m : ℕ, ξ ∈ wordBall T m}
  mul_mem' := by
    rintro a b ⟨m, hm⟩ ⟨m', hm'⟩
    exact ⟨m + m', mul_mem_wordBall hm hm'⟩
  one_mem' := ⟨0, one_mem_wordBall T 0⟩
  inv_mem' := by
    rintro a ⟨m, hm⟩
    exact ⟨m, inv_mem_wordBall hT hm⟩

/-- **Word length is finite** for a finite symmetric generating set: every `ξ ∈ Λ` lies in some
ball `B_m` (`sec:proof`). -/
theorem exists_mem_wordBall {T : Set Λ} (hT : ∀ x ∈ T, x⁻¹ ∈ T)
    (hgen : Subgroup.closure T = ⊤) (ξ : Λ) : ∃ m : ℕ, ξ ∈ wordBall T m := by
  have hle : Subgroup.closure T ≤ wordBallSubgroup T hT :=
    (Subgroup.closure_le _).mpr fun x hx => ⟨1, mem_wordBall_one hx⟩
  rw [hgen] at hle
  exact hle (Subgroup.mem_top ξ)

end WordBall

end GroupApproximation.Full.SK03

#audit_axioms GroupApproximation.Full.SK03.mul_mem_wordBall
#audit_axioms GroupApproximation.Full.SK03.inv_mem_wordBall
#audit_axioms GroupApproximation.Full.SK03.exists_mem_wordBall
