import GroupApproximation.Kazhdan.FoxRelationSequence
import Mathlib.GroupTheory.Abelianization.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The relation module embeds in `ℤG^X`

Let `N` be the normal closure of the relators of a signed-word presentation of `G = F/N`.
An element `n ∈ N` whose Fox derivative vanishes in `ℤG^X` lies in the commutator subgroup
of `N` (`mem_commutator_of_mapG_foxFree_eq_zero`): the relation module `N/[N,N]` embeds in
`ℤG^X`.

The proof is a Schreier potential.  Fix a section `σ : G → F` with `σ 1 = 1` (`secP`).  For
`g ∈ G` and `w ∈ F` the element `σ(g) · w · σ(g w̄)⁻¹` lies in `N` (`potential`), and its
class in the abelianization of `N` is a crossed function of `w` (`apot_mul`).  The additive
map `λ (x, g) = [σ(g) · x · σ(g x̄)⁻¹]` (`lam`) turns the translated Fox derivative
`g · ∂w` into the same crossed function (`flow_eq_apot`), because both agree on generators.
At `g = 1` and `w = n ∈ N` the potential is `n` itself.
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe v w

variable {X : Type v} {ρ : Type w} (rel : ρ → SignedWord X)

open Classical in
/-- A section of the quotient map with `σ 1 = 1`. -/
noncomputable def secP (g : Presented rel) : FreeGroup X :=
  if g = 1 then 1 else sectionP rel g

theorem secP_one : secP rel 1 = 1 := by
  unfold secP
  rw [if_pos rfl]

theorem mk_secP (g : Presented rel) : PresentedGroup.mk (relSet rel) (secP rel g) = g := by
  unfold secP
  split_ifs with h
  · rw [map_one, h]
  · exact mk_sectionP rel g

theorem potential_mem (g : Presented rel) (w : FreeGroup X) :
    secP rel g * w * (secP rel (g * PresentedGroup.mk (relSet rel) w))⁻¹ ∈
      Subgroup.normalClosure (relSet rel) :=
  mem_normalClosure_of_mk_eq_one rel (by
    rw [map_mul, map_mul, map_inv, mk_secP, mk_secP, mul_inv_cancel])

/-- The Schreier potential `σ(g) · w · σ(g w̄)⁻¹ ∈ N`. -/
def potential (g : Presented rel) (w : FreeGroup X) : Subgroup.normalClosure (relSet rel) :=
  ⟨_, potential_mem rel g w⟩

theorem potential_one (g : Presented rel) : potential rel g 1 = 1 := by
  apply Subtype.ext
  show secP rel g * 1 * (secP rel (g * PresentedGroup.mk (relSet rel) 1))⁻¹ = 1
  rw [map_one, mul_one, mul_one, mul_inv_cancel]

theorem potential_mul (g : Presented rel) (w₁ w₂ : FreeGroup X) :
    potential rel g (w₁ * w₂) =
      potential rel g w₁ * potential rel (g * PresentedGroup.mk (relSet rel) w₁) w₂ := by
  apply Subtype.ext
  show secP rel g * (w₁ * w₂) *
      (secP rel (g * PresentedGroup.mk (relSet rel) (w₁ * w₂)))⁻¹ =
    secP rel g * w₁ * (secP rel (g * PresentedGroup.mk (relSet rel) w₁))⁻¹ *
      (secP rel (g * PresentedGroup.mk (relSet rel) w₁) * w₂ *
        (secP rel (g * PresentedGroup.mk (relSet rel) w₁ *
          PresentedGroup.mk (relSet rel) w₂))⁻¹)
  rw [map_mul, ← mul_assoc g]
  group

/-- The class of the potential in the abelianization of `N`, written additively. -/
noncomputable def apot (g : Presented rel) (w : FreeGroup X) :
    Additive (Abelianization (Subgroup.normalClosure (relSet rel))) :=
  Additive.ofMul (Abelianization.of (potential rel g w))

theorem apot_one (g : Presented rel) : apot rel g 1 = 0 := by
  unfold apot
  rw [potential_one, map_one]
  rfl

theorem apot_mul (g : Presented rel) (w₁ w₂ : FreeGroup X) :
    apot rel g (w₁ * w₂) = apot rel g w₁ + apot rel (g * PresentedGroup.mk (relSet rel) w₁) w₂ := by
  unfold apot
  rw [potential_mul, map_mul]
  rfl

/-- The additive map `λ (x, g) = [σ(g) · x · σ(g x̄)⁻¹]`. -/
noncomputable def lam :
    FreeZG (Presented rel) X →+ Additive (Abelianization (Subgroup.normalClosure (relSet rel))) :=
  Finsupp.liftAddHom fun q ↦ zmultiplesHom _ (apot rel q.2 (FreeGroup.of q.1))

theorem lam_single (x : X) (g : Presented rel) (c : ℤ) :
    lam rel (Finsupp.single (x, g) c) = c • apot rel g (FreeGroup.of x) := by
  simp only [lam, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

/-- The potential of the translated, pushed-forward Fox derivative. -/
noncomputable def flow (g : Presented rel) (w : FreeGroup X) :
    Additive (Abelianization (Subgroup.normalClosure (relSet rel))) :=
  lam rel (act g (mapG (PresentedGroup.mk (relSet rel)) (foxFree 1 w)))

theorem flow_one (g : Presented rel) : flow rel g 1 = 0 := by
  unfold flow
  rw [foxFree_one, map_zero, map_zero, map_zero]

theorem flow_mul (g : Presented rel) (w₁ w₂ : FreeGroup X) :
    flow rel g (w₁ * w₂) = flow rel g w₁ + flow rel (g * PresentedGroup.mk (relSet rel) w₁) w₂ := by
  unfold flow
  rw [foxFree_mul, map_add, mapG_act, map_add, act_act, map_add]

theorem flow_of (g : Presented rel) (x : X) : flow rel g (FreeGroup.of x) = apot rel g (FreeGroup.of x) := by
  unfold flow
  have h := foxFree_mul_of (1 : FreeGroup X) 1 x
  rw [one_mul, foxFree_one, zero_add, one_mul] at h
  rw [h, mapG_single, map_one, act_single, mul_one, lam_single, one_zsmul]

theorem flow_eq_apot_mk (L : SignedWord X) (g : Presented rel) :
    flow rel g (FreeGroup.mk L) = apot rel g (FreeGroup.mk L) := by
  induction L generalizing g with
  | nil => rw [← FreeGroup.one_eq_mk, flow_one, apot_one]
  | cons letter rest ih =>
      have hsplit : (FreeGroup.mk (letter :: rest) : FreeGroup X) =
          FreeGroup.mk [letter] * FreeGroup.mk rest := by
        rw [FreeGroup.mul_mk]
        rfl
      rw [hsplit, flow_mul, apot_mul, ih]
      congr 1
      rcases letter with ⟨x, _ | _⟩
      · have hinv : (FreeGroup.mk [(x, false)] : FreeGroup X) = (FreeGroup.of x)⁻¹ := by
          show FreeGroup.mk [(x, false)] = (FreeGroup.mk [(x, true)])⁻¹
          rw [FreeGroup.inv_mk]
          rfl
        rw [hinv]
        have h1 := flow_mul rel g (FreeGroup.of x)⁻¹ (FreeGroup.of x)
        have h2 := apot_mul rel g (FreeGroup.of x)⁻¹ (FreeGroup.of x)
        rw [inv_mul_cancel, flow_one, flow_of] at h1
        rw [inv_mul_cancel, apot_one] at h2
        exact add_right_cancel (h1.symm.trans h2)
      · exact flow_of rel g x

/-- **The potential identity**: `λ (g · ∂w) = [σ(g) · w · σ(g w̄)⁻¹]`. -/
theorem flow_eq_apot (g : Presented rel) (w : FreeGroup X) : flow rel g w = apot rel g w := by
  induction w using Quot.ind with
  | mk L => exact flow_eq_apot_mk rel L g

/-- **The relation module embeds in `ℤG^X`**: a normal-closure element with vanishing Fox
derivative in `ℤG^X` lies in the commutator subgroup of the normal closure. -/
theorem mem_commutator_of_mapG_foxFree_eq_zero {n : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure (relSet rel))
    (h0 : mapG (PresentedGroup.mk (relSet rel)) (foxFree 1 n) = 0) :
    (⟨n, hn⟩ : Subgroup.normalClosure (relSet rel)) ∈
      commutator (Subgroup.normalClosure (relSet rel)) := by
  have hflow : flow rel 1 n = 0 := by
    unfold flow
    rw [h0, map_zero, map_zero]
  have hmk : PresentedGroup.mk (relSet rel) n = 1 :=
    (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure (relSet rel)) n).mpr hn
  have hpot : potential rel 1 n = ⟨n, hn⟩ := by
    apply Subtype.ext
    show secP rel 1 * n * (secP rel (1 * PresentedGroup.mk (relSet rel) n))⁻¹ = n
    rw [hmk, mul_one, secP_one, one_mul, inv_one, mul_one]
  have hz : apot rel 1 n = 0 := by rw [← flow_eq_apot, hflow]
  unfold apot at hz
  rw [hpot] at hz
  have hof : Abelianization.of (⟨n, hn⟩ : Subgroup.normalClosure (relSet rel)) = 1 := hz
  rw [← Abelianization.ker_of]
  exact MonoidHom.mem_ker.mpr hof

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.mk_secP
#audit_axioms GroupApproximation.FoxComplex.potential_mul
#audit_axioms GroupApproximation.FoxComplex.flow_mul
#audit_axioms GroupApproximation.FoxComplex.flow_of
#audit_axioms GroupApproximation.FoxComplex.flow_eq_apot
#audit_axioms GroupApproximation.FoxComplex.mem_commutator_of_mapG_foxFree_eq_zero
