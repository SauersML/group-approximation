import GroupApproximation.Sofic.FreeLampReduction
import GroupApproximation.Sofic.PushoutEmbedding
import GroupApproximation.Sofic.WeakMFTransfer

/-!
# A free-lamp amalgam embeds in a symmetric product double

For a subgroup `Γ ≤ G` and a group `K`, this file constructs the canonical
homomorphism

`G *_Γ (Γ × K) ⟶ (G × K) *_Γ (G × K)`

and proves it injective by the Bass--Serre normal-form criterion in
`PushoutEmbedding`.  This is the elementary embedding used to transfer
Shulman's weak-MF permanence theorem to the Kun--Thom free-lamp group.
-/

namespace GroupApproximation

open Monoid

variable (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]

/-- Both vertex groups in the product double are `G × K`. -/
abbrev ProductDoubleFactor : Bool → Type := fun _ ↦ G × K

instance productDoubleFactorGroup : ∀ b, Group (ProductDoubleFactor G K b) :=
  fun _ ↦ inferInstanceAs (Group (G × K))

/-- The edge map `γ ↦ (γ,1)` into either vertex group. -/
def productDoubleMap : ∀ b, ↥Γ →* ProductDoubleFactor G K b :=
  fun _ ↦
    { toFun := fun γ ↦ ((γ : G), (1 : K))
      map_one' := by simp
      map_mul' := fun _ _ ↦ by simp }

@[simp]
theorem productDoubleMap_apply (b : Bool) (γ : ↥Γ) :
    productDoubleMap G Γ K b γ = ((γ : G), (1 : K)) := rfl

theorem productDoubleMap_injective :
    ∀ b, Function.Injective (productDoubleMap G Γ K b) := by
  intro b x y h
  exact Subtype.ext (congrArg Prod.fst h)

/-- The symmetric double of `G × K` along the copy `Γ × {1}`. -/
abbrev ProductDouble : Type := PushoutI (productDoubleMap G Γ K)

/-- The factor maps defining the free-lamp inclusion into the product double.
On the ambient factor this is `g ↦ (g,1)`; on the lamp factor it is the
coordinatewise inclusion `Γ × K ↪ G × K`. -/
def freeLampProductFactorMap :
    ∀ b, LampFactor G Γ K b →* ProductDoubleFactor G K b
  | true =>
      { toFun := fun g ↦ (g, (1 : K))
        map_one' := rfl
        map_mul' := fun _ _ ↦ by
          apply Prod.ext
          · rfl
          · simp }
  | false =>
      { toFun := fun p ↦ ((p.1 : G), p.2)
        map_one' := by
          apply Prod.ext
          · rfl
          · rfl
        map_mul' := fun _ _ ↦ by
          apply Prod.ext
          · rfl
          · rfl }

@[simp]
theorem freeLampProductFactorMap_true_apply (g : G) :
    freeLampProductFactorMap G Γ K true g = (g, (1 : K)) := rfl

@[simp]
theorem freeLampProductFactorMap_false_apply (p : ↥Γ × K) :
    freeLampProductFactorMap G Γ K false p = ((p.1 : G), p.2) := rfl

theorem freeLampProductFactorMap_injective :
    ∀ b, Function.Injective (freeLampProductFactorMap G Γ K b)
  | true => fun _ _ h ↦ by
      dsimp [freeLampProductFactorMap] at h
      exact congrArg (fun p : G × K ↦ p.1) h
  | false => fun x y h ↦ by
      dsimp [freeLampProductFactorMap] at h
      exact Prod.ext
        (Subtype.ext (congrArg (fun p : G × K ↦ p.1) h))
        (congrArg (fun p : G × K ↦ p.2) h)

theorem freeLampProductFactorMap_commutes : ∀ b,
    (freeLampProductFactorMap G Γ K b).comp (lampMap G Γ K b) =
      productDoubleMap G Γ K b := by
  intro b
  cases b with
  | false =>
      apply MonoidHom.ext
      intro γ
      rw [MonoidHom.comp_apply, lampMap_false_apply,
        freeLampProductFactorMap_false_apply, productDoubleMap_apply]
  | true =>
      apply MonoidHom.ext
      intro γ
      rw [MonoidHom.comp_apply, lampMap_true_apply,
        freeLampProductFactorMap_true_apply, productDoubleMap_apply]

/-- The canonical map from the free-lamp amalgam to the product double. -/
def freeLampToProductDouble :
    FreeLamp G Γ K →* ProductDouble G Γ K :=
  PushoutEmbedding.map (lampMap G Γ K) (productDoubleMap G Γ K)
    (freeLampProductFactorMap G Γ K)
    (freeLampProductFactorMap_commutes G Γ K)

@[simp]
theorem freeLampToProductDouble_inAmbient (g : G) :
    freeLampToProductDouble G Γ K (inAmbient G Γ K g) =
      PushoutI.of (φ := productDoubleMap G Γ K) true (g, 1) := by
  change PushoutEmbedding.map (lampMap G Γ K) (productDoubleMap G Γ K)
      (freeLampProductFactorMap G Γ K) (freeLampProductFactorMap_commutes G Γ K)
      (PushoutI.of (φ := lampMap G Γ K) true g) = _
  have h := PushoutEmbedding.map_of (lampMap G Γ K) (productDoubleMap G Γ K)
    (freeLampProductFactorMap G Γ K) (freeLampProductFactorMap_commutes G Γ K) true g
  rw [freeLampProductFactorMap_true_apply] at h
  exact h

@[simp]
theorem freeLampToProductDouble_inLamp (k : K) :
    freeLampToProductDouble G Γ K (inLamp G Γ K k) =
      PushoutI.of (φ := productDoubleMap G Γ K) false ((1 : G), k) := by
  change freeLampToProductDouble G Γ K
      (PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k)) = _
  change PushoutEmbedding.map (lampMap G Γ K) (productDoubleMap G Γ K)
      (freeLampProductFactorMap G Γ K) (freeLampProductFactorMap_commutes G Γ K)
      (PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k)) = _
  have h := PushoutEmbedding.map_of (lampMap G Γ K) (productDoubleMap G Γ K)
    (freeLampProductFactorMap G Γ K) (freeLampProductFactorMap_commutes G Γ K)
    false ((1 : ↥Γ), k)
  rw [freeLampProductFactorMap_false_apply] at h
  exact h

theorem freeLampProductFactorMap_reflects_range : ∀ b g,
    freeLampProductFactorMap G Γ K b g ∈
        (productDoubleMap G Γ K b).range →
      g ∈ (lampMap G Γ K b).range := by
  intro b
  cases b with
  | false =>
      intro g hg
      obtain ⟨γ, hγ⟩ := hg
      dsimp [productDoubleMap, freeLampProductFactorMap] at hγ
      refine ⟨γ, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun p : G × K ↦ p.1) hγ
      · exact congrArg (fun p : G × K ↦ p.2) hγ
  | true =>
      intro g hg
      obtain ⟨γ, hγ⟩ := hg
      dsimp [productDoubleMap, freeLampProductFactorMap] at hγ
      refine ⟨γ, ?_⟩
      exact congrArg (fun p : G × K ↦ p.1) hγ

/-- **Free-lamp/product-double embedding.**  The canonical map
`G *_Γ (Γ × K) → (G × K) *_Γ (G × K)` is injective. -/
theorem freeLampToProductDouble_injective :
    Function.Injective (freeLampToProductDouble G Γ K) :=
  PushoutEmbedding.map_injective_of_reflects_range
    (lampMap G Γ K) (productDoubleMap G Γ K)
    (freeLampProductFactorMap G Γ K)
    (lampMap_injective G Γ K)
    (productDoubleMap_injective G Γ K)
    (freeLampProductFactorMap_injective G Γ K)
    (freeLampProductFactorMap_commutes G Γ K)
    (freeLampProductFactorMap_reflects_range G Γ K)

/-- Once weak MF of the product double has been established, the free-lamp
subgroup inherits it through the proved embedding.  This is a transfer lemma,
not a permanence premise: the analytic proof of weak MF for the double remains
an explicit upstream obligation. -/
theorem isWeakMF_freeLamp_of_productDouble
    (hD : IsWeakMF (ProductDouble G Γ K)) :
    IsWeakMF (FreeLamp G Γ K) :=
  isWeakMF_of_injective (freeLampToProductDouble G Γ K)
    (freeLampToProductDouble_injective G Γ K) hD

end GroupApproximation
