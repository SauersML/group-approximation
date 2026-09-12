import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group
import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Recognizing ascending HNN extensions

Hyde–Lodha, Lemma 2.3 (GMSW, Lemma 3.1): "Let `G` be a group that satisfies the following.  There
exist subgroups `H₁ < H₂ < G` and an element `f ∈ G` such that `f⁻¹H₂f = H₁`, no nontrivial power of
`f` lies in `H₂`, and `⟨H₂, f⟩ = G`.  Then `G` admits the structure of an ascending HNN extension
with base group `H₂`."

* `hnnEquiv`: for `H ≤ G` and `g ∈ G` with `g^n ∈ H ⇒ n = 0` and `⟨H, g⟩ = G`, and any
  `φ : ⊤ ≃* B` with `φ h = g⁻¹ h g`, the map `HNNExtension H ⊤ B φ → G`, `h ↦ h`, `t ↦ g⁻¹`, is an
  isomorphism.  Every element of the extension is `t⁻ᵃ h tᵇ` (`exists_nf`), and such an element maps
  to `1` only if `a = b` and `h = 1`.  (Mathlib's relation is `t a t⁻¹ = φ a`; with `t ↦ g⁻¹` it is
  the printed `f⁻¹ h f = φ(h)`.)
* `ascendingHNN_recognition`: the printed statement ("no nontrivial power" read as `f^n ∈ H₂ ⇒ n = 0`).
* `isFinitelyPresented_of_ascending`: with `H` finitely presented, `G` is finitely presented (through
  `HNNFinitePresentation.isFinitelyPresented_hnnExtension`).
-/

namespace GroupApproximation
namespace AscendingHNNRecognition

section Core

variable {G : Type*} [Group G] (H : Subgroup G) (g : G) {B : Subgroup H}
  (φ : (⊤ : Subgroup H) ≃* B)

/-- The evaluation `h ↦ h`, `t ↦ g⁻¹`. -/
def eval (hφ : ∀ a : (⊤ : Subgroup H), (((φ a : H) : G)) = g⁻¹ * ((a : H) : G) * g) :
    HNNExtension H ⊤ B φ →* G :=
  HNNExtension.lift H.subtype g⁻¹ (fun a => by
    show g⁻¹ * ((a : H) : G) = ((φ a : H) : G) * g⁻¹
    rw [hφ a]
    group)

variable {H g φ}

/-- The normal forms `t⁻ᵃ h tᵇ`. -/
def NF (x : HNNExtension H ⊤ B φ) : Prop :=
  ∃ a b : ℕ, ∃ h : H, x = HNNExtension.t⁻¹ ^ a * HNNExtension.of h * HNNExtension.t ^ b

/-- `φ` as an endomorphism of `H`. -/
def phiEnd (x : H) : H := φ ⟨x, Subgroup.mem_top x⟩

theorem of_mul_inv_t_pow (k : H) (a : ℕ) :
    ∃ k' : H, (HNNExtension.of k : HNNExtension H ⊤ B φ) * HNNExtension.t⁻¹ ^ a =
      HNNExtension.t⁻¹ ^ a * HNNExtension.of k' := by
  induction a generalizing k with
  | zero => exact ⟨k, by simp⟩
  | succ a ih =>
    have h1 : (HNNExtension.of k : HNNExtension H ⊤ B φ) * HNNExtension.t⁻¹ =
        HNNExtension.t⁻¹ * HNNExtension.of (phiEnd (φ := φ) k) :=
      HNNExtension.of_mul_inv_t (A := ⊤) (B := B) (φ := φ) ⟨k, Subgroup.mem_top k⟩
    obtain ⟨k', hk'⟩ := ih (phiEnd (φ := φ) k)
    refine ⟨k', ?_⟩
    calc (HNNExtension.of k : HNNExtension H ⊤ B φ) * HNNExtension.t⁻¹ ^ (a + 1)
        = ((HNNExtension.of k : HNNExtension H ⊤ B φ) * HNNExtension.t⁻¹) *
            HNNExtension.t⁻¹ ^ a := by
          rw [pow_succ', mul_assoc]
      _ = HNNExtension.t⁻¹ * (HNNExtension.of (phiEnd (φ := φ) k) * HNNExtension.t⁻¹ ^ a) := by
          rw [h1, mul_assoc]
      _ = HNNExtension.t⁻¹ ^ (a + 1) * HNNExtension.of k' := by
          rw [hk', pow_succ', mul_assoc]

theorem nf_of_mul {x : HNNExtension H ⊤ B φ} (hx : NF x) (k : H) :
    NF (HNNExtension.of k * x) := by
  obtain ⟨a, b, h, rfl⟩ := hx
  obtain ⟨k', hk'⟩ := of_mul_inv_t_pow (φ := φ) k a
  refine ⟨a, b, k' * h, ?_⟩
  calc (HNNExtension.of k : HNNExtension H ⊤ B φ) *
        (HNNExtension.t⁻¹ ^ a * HNNExtension.of h * HNNExtension.t ^ b)
      = ((HNNExtension.of k : HNNExtension H ⊤ B φ) * HNNExtension.t⁻¹ ^ a) *
          HNNExtension.of h * HNNExtension.t ^ b := by
        simp only [mul_assoc]
    _ = HNNExtension.t⁻¹ ^ a * HNNExtension.of (k' * h) * HNNExtension.t ^ b := by
        rw [hk', map_mul]
        simp only [mul_assoc]

theorem nf_t_mul {x : HNNExtension H ⊤ B φ} (hx : NF x) : NF (HNNExtension.t * x) := by
  obtain ⟨a, b, h, rfl⟩ := hx
  rcases a with _ | a
  · refine ⟨0, b + 1, phiEnd (φ := φ) h, ?_⟩
    have h1 : (HNNExtension.t : HNNExtension H ⊤ B φ) * HNNExtension.of h =
        HNNExtension.of (phiEnd (φ := φ) h) * HNNExtension.t :=
      HNNExtension.t_mul_of (A := ⊤) (B := B) (φ := φ) ⟨h, Subgroup.mem_top h⟩
    simp only [pow_zero, one_mul]
    rw [← mul_assoc, h1, mul_assoc, pow_succ']
  · refine ⟨a, b, h, ?_⟩
    simp only [pow_succ', mul_assoc, mul_inv_cancel_left]

theorem nf_inv_t_mul {x : HNNExtension H ⊤ B φ} (hx : NF x) : NF (HNNExtension.t⁻¹ * x) := by
  obtain ⟨a, b, h, rfl⟩ := hx
  exact ⟨a + 1, b, h, by simp only [pow_succ', mul_assoc]⟩

/-- **Normal form.** -/
theorem exists_nf (x : HNNExtension H ⊤ B φ) : NF x := by
  have key : ∀ y : HNNExtension H ⊤ B φ, ∀ p, NF p → NF (y * p) ∧ NF (y⁻¹ * p) := by
    intro y
    induction y using HNNExtension.induction_on with
    | of k =>
      intro p hp
      refine ⟨nf_of_mul hp k, ?_⟩
      rw [← map_inv]
      exact nf_of_mul hp k⁻¹
    | t => exact fun p hp => ⟨nf_t_mul hp, nf_inv_t_mul hp⟩
    | mul y z hy hz =>
      intro p hp
      refine ⟨?_, ?_⟩
      · rw [mul_assoc]
        exact (hy _ (hz p hp).1).1
      · rw [mul_inv_rev, mul_assoc]
        exact (hz _ (hy p hp).2).2
    | inv y hy =>
      intro p hp
      rw [inv_inv]
      exact ⟨(hy p hp).2, (hy p hp).1⟩
  have h1 : NF (1 : HNNExtension H ⊤ B φ) := ⟨0, 0, 1, by simp⟩
  simpa using (key x 1 h1).1

variable (hφ : ∀ a : (⊤ : Subgroup H), (((φ a : H) : G)) = g⁻¹ * ((a : H) : G) * g)

theorem eval_of (h : H) : eval H g φ hφ (HNNExtension.of h) = (h : G) :=
  HNNExtension.lift_of _ _ _ h

theorem eval_t : eval H g φ hφ HNNExtension.t = g⁻¹ :=
  HNNExtension.lift_t _ _ _

variable (hpow : ∀ n : ℤ, g ^ n ∈ H → n = 0)

include hpow in
theorem eval_injective : Function.Injective (eval H g φ hφ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, b, h, rfl⟩ := exists_nf x
  have hG : g ^ a * (h : G) * g⁻¹ ^ b = 1 := by
    have e := hx
    rw [map_mul, map_mul, map_pow, map_pow, map_inv, eval_t hφ, eval_of hφ, inv_inv] at e
    exact e
  have e1 : g ^ a * (h : G) = (g⁻¹ ^ b)⁻¹ := eq_inv_of_mul_eq_one_left hG
  have e2 : (h : G) = (g ^ a)⁻¹ * (g⁻¹ ^ b)⁻¹ := eq_inv_mul_of_mul_eq e1
  have hh : (h : G) = g ^ ((b : ℤ) - a) := by
    rw [e2, inv_pow, inv_inv, sub_eq_add_neg, zpow_add, zpow_neg, zpow_natCast, zpow_natCast]
    exact Commute.inv_left ((Commute.refl g).pow_pow a b) |>.eq
  have hmem : g ^ ((b : ℤ) - a) ∈ H := by
    rw [← hh]
    exact h.2
  have hab : (b : ℤ) - a = 0 := hpow _ hmem
  have hba : b = a := by omega
  have h1 : h = 1 := by
    apply Subtype.ext
    rw [hh, hab, zpow_zero]
    rfl
  rw [h1, hba, map_one, mul_one, inv_pow, inv_mul_cancel]

variable (hgen : Subgroup.closure ((H : Set G) ∪ {g}) = ⊤)

include hgen in
theorem eval_surjective : Function.Surjective (eval H g φ hφ) := by
  intro x
  have hle : Subgroup.closure ((H : Set G) ∪ {g}) ≤ (eval H g φ hφ).range := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · exact ⟨HNNExtension.of ⟨y, hy⟩, eval_of hφ _⟩
    · rw [Set.mem_singleton_iff.mp hy]
      exact ⟨HNNExtension.t⁻¹, by rw [map_inv, eval_t hφ, inv_inv]⟩
  exact hle (by rw [hgen]; exact Subgroup.mem_top x)

/-- **The ascending HNN extension is `G`.** -/
noncomputable def hnnEquiv : HNNExtension H ⊤ B φ ≃* G :=
  MulEquiv.ofBijective (eval H g φ hφ) ⟨eval_injective hφ hpow, eval_surjective hφ hgen⟩

end Core

/-- **Hyde–Lodha, Lemma 2.3 (GMSW, Lemma 3.1).** -/
theorem ascendingHNN_recognition {G : Type*} [Group G] (H₁ H₂ : Subgroup G) (h₁₂ : H₁ < H₂)
    (_h₂ : H₂ < ⊤) (f : G) (hconj : ∀ x : G, x ∈ H₁ ↔ f * x * f⁻¹ ∈ H₂)
    (hpow : ∀ n : ℤ, f ^ n ∈ H₂ → n = 0) (hgen : Subgroup.closure ((H₂ : Set G) ∪ {f}) = ⊤) :
    ∃ φ : (⊤ : Subgroup H₂) ≃* H₁.subgroupOf H₂,
      (∀ a : (⊤ : Subgroup H₂), (((φ a : H₂) : G)) = f⁻¹ * ((a : H₂) : G) * f) ∧
      Nonempty (HNNExtension H₂ ⊤ (H₁.subgroupOf H₂) φ ≃* G) := by
  have hmem₁ : ∀ a : H₂, f⁻¹ * (a : G) * f ∈ H₁ := by
    intro a
    rw [hconj]
    have e : f * (f⁻¹ * (a : G) * f) * f⁻¹ = (a : G) := by group
    rw [e]
    exact a.2
  let ψ : (⊤ : Subgroup H₂) →* H₁.subgroupOf H₂ :=
    { toFun := fun a => ⟨⟨f⁻¹ * ((a : H₂) : G) * f, h₁₂.le (hmem₁ a)⟩,
        Subgroup.mem_subgroupOf.mpr (hmem₁ a)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show f⁻¹ * (((1 : (⊤ : Subgroup H₂)) : H₂) : G) * f = 1
        simp
      map_mul' := fun a c => by
        apply Subtype.ext
        apply Subtype.ext
        show f⁻¹ * (((a * c : (⊤ : Subgroup H₂)) : H₂) : G) * f =
          (f⁻¹ * ((a : H₂) : G) * f) * (f⁻¹ * ((c : H₂) : G) * f)
        simp only [Subgroup.coe_mul]
        group }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h : f⁻¹ * ((a : H₂) : G) * f = 1 :=
      congrArg (fun x : H₁.subgroupOf H₂ => ((x : H₂) : G)) ha
    apply Subtype.ext
    apply Subtype.ext
    calc ((a : H₂) : G) = f * (f⁻¹ * ((a : H₂) : G) * f) * f⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨⟨x, hx₂⟩, hx₁⟩
    have hx₁' : x ∈ H₁ := Subgroup.mem_subgroupOf.mp hx₁
    refine ⟨⟨⟨f * x * f⁻¹, (hconj x).mp hx₁'⟩, Subgroup.mem_top _⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show f⁻¹ * (f * x * f⁻¹) * f = x
    group
  let φ := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hφ : ∀ a : (⊤ : Subgroup H₂), (((φ a : H₂) : G)) = f⁻¹ * ((a : H₂) : G) * f := fun _ => rfl
  exact ⟨φ, hφ, ⟨hnnEquiv hφ hpow hgen⟩⟩

/-- **Ascending HNN extensions of finitely presented groups are finitely presented.** -/
theorem isFinitelyPresented_of_ascending {G : Type} [Group G] (H : Subgroup G)
    [Group.IsFinitelyPresented H] (g : G) (hconj : ∀ h ∈ H, g⁻¹ * h * g ∈ H)
    (hpow : ∀ n : ℤ, g ^ n ∈ H → n = 0) (hgen : Subgroup.closure ((H : Set G) ∪ {g}) = ⊤) :
    Group.IsFinitelyPresented G := by
  let ψ : H →* H :=
    { toFun := fun h => ⟨g⁻¹ * (h : G) * g, hconj h h.2⟩
      map_one' := by
        apply Subtype.ext
        show g⁻¹ * ((1 : H) : G) * g = 1
        simp
      map_mul' := fun a c => by
        apply Subtype.ext
        show g⁻¹ * ((a * c : H) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (c : G) * g)
        rw [Subgroup.coe_mul]
        group }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h : g⁻¹ * (a : G) * g = 1 := congrArg (fun x : H => (x : G)) ha
    apply Subtype.ext
    calc (a : G) = g * (g⁻¹ * (a : G) * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  let φ : (⊤ : Subgroup H) ≃* ψ.range := Subgroup.topEquiv.trans (MonoidHom.ofInjective hψinj)
  have hφ : ∀ a : (⊤ : Subgroup H), (((φ a : H) : G)) = g⁻¹ * ((a : H) : G) * g := fun _ => rfl
  haveI : Group.FG H := ProductFinitePresentation.fg_of_isFinitelyPresented H
  haveI : Group.FG (⊤ : Subgroup H) :=
    (Group.fg_iff_subgroup_fg (⊤ : Subgroup H)).mpr (Group.fg_def.mp inferInstance)
  haveI : Group.IsFinitelyPresented (HNNExtension H ⊤ ψ.range φ) :=
    HNNFinitePresentation.isFinitelyPresented_hnnExtension φ
  exact Group.IsFinitelyPresented.equiv (hnnEquiv hφ hpow hgen)

#audit_axioms GroupApproximation.AscendingHNNRecognition.ascendingHNN_recognition
#audit_axioms GroupApproximation.AscendingHNNRecognition.isFinitelyPresented_of_ascending

end AscendingHNNRecognition
end GroupApproximation
