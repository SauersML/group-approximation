import GroupApproximation.Algebra.RabinVariantTower
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
# The presentation of the variant construction

`Algebra.RabinVariantTower` builds the tower and proves both halves of the
biconditional for it.  The Adian--Rabin reduction, however, is a statement about
a *presentation*: the map it needs is `w ↦ P(w)` with `P(w)` a finite
presentation.  This file writes that presentation down and maps it into the
tower.

The generators are the source generators `xᵢ`, the free letter `s`, one letter
`tᵢ` for each `sᵢ`, and the four cascade letters `u`, `b`, `c`, `k`.  The
relators are the source relators together with

    `u tᵢ u⁻¹ (tᵢ sᵢ)⁻¹`,   `b u b⁻¹ u⁻²`,   `c b c⁻¹ b⁻²`,   `k z k⁻¹ c⁻¹`,

where `sᵢ` is `s` for `i = 0` and `s xᵢ₋₁` otherwise, and `z = ⁅w, s⁆`.

`toTower` is the homomorphism into the tower, and it exists because every one of
those relators holds there --- which is exactly what
`RabinVariantTower.conj_t_eq_ts`, `casc1_conj`, `casc2_conj` and `full_conj`
say.  Composing with it turns the tower's `full_base_injective` into the
statement the reduction needs: the source group embeds in the *presented*
group.
-/

namespace GroupApproximation
namespace RabinVariantPresentation

open RabinVariantTower

/-- The letters adjoined to the source generators. -/
inductive Extra (m : ℕ) : Type
  | s : Extra m
  | t : Fin (m + 1) → Extra m
  | u : Extra m
  | b : Extra m
  | c : Extra m
  | k : Extra m
  deriving DecidableEq

/-- The generators of the presentation. -/
abbrev Gen (m : ℕ) : Type := Fin m ⊕ Extra m

variable {m : ℕ}

/-- A source generator, as a word. -/
def X (i : Fin m) : FreeGroup (Gen m) := FreeGroup.of (Sum.inl i)

/-- The free letter, as a word. -/
def S : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.s)

/-- The `i`th stable letter of the killing layer, as a word. -/
def T (i : Fin (m + 1)) : FreeGroup (Gen m) := FreeGroup.of (Sum.inr (Extra.t i))

/-- The cascade letters, as words. -/
def U : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.u)
/-- The second cascade letter. -/
def B : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.b)
/-- The third cascade letter. -/
def C : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.c)
/-- The last cascade letter. -/
def K : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.k)

/-- `sᵢ`: the letter `s` at `i = 0`, and `s xᵢ₋₁` afterwards.  The change of
generators, at the level of words. -/
def sWord (i : Fin (m + 1)) : FreeGroup (Gen m) :=
  if h : (i : ℕ) = 0 then S
  else S * X ⟨(i : ℕ) - 1, by omega⟩

/-- The source generators, embedded in the larger free group. -/
def emb : FreeGroup (Fin m) →* FreeGroup (Gen m) := FreeGroup.map Sum.inl

/-- The witness word `z = ⁅w, s⁆`. -/
def Z (w : FreeGroup (Fin m)) : FreeGroup (Gen m) :=
  emb w * S * (emb w)⁻¹ * S⁻¹

/-- **The relators.**  The source relators, the killing relations, and the
cascade. -/
def relators (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    Set (FreeGroup (Gen m)) :=
  (fun r => emb r) '' R
    ∪ Set.range (fun i : Fin (m + 1) => U * T i * U⁻¹ * (T i * sWord i)⁻¹)
    ∪ {B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹, C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹,
        K * Z w * K⁻¹ * C⁻¹}

/-- **The presented group of the construction.** -/
abbrev Pres (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) : Type :=
  PresentedGroup (relators R w)

/-! ## Mapping the presentation into the tower

Every relator holds in the tower, so the presentation maps into it.  The four
families of relators are discharged by the four conjugation lemmas of
`RabinVariantTower`, and the source relators by the fact that the source group
sits inside. -/

variable {Γ : Type} [Group Γ] (x : Fin (m + 1) → Γ) (xs : Fin m → Γ)

/-- The witness `z = ⁅w, s⁆`, as an element of the tower. -/
noncomputable def zElt (w : FreeGroup (Fin m)) : Casc2 x :=
  casc2OfMid x (midOfBase
    (Monoid.Coprod.inl (FreeGroup.lift xs w) * RabinVariantTower.s *
      (Monoid.Coprod.inl (FreeGroup.lift xs w))⁻¹ * (RabinVariantTower.s)⁻¹))

variable {w : FreeGroup (Fin m)}
  {hz : ∀ p : ℤ, p ≠ 0 → (zElt x xs w) ^ p ≠ 1}

/-- Where the generators go in the tower. -/
noncomputable def towerGen : Gen m → Full x hz
  | Sum.inl i => fullOf x hz (casc2OfBase x (xs i))
  | Sum.inr Extra.s =>
      fullOf x hz (casc2OfMid x (midOfBase (RabinVariantTower.s)))
  | Sum.inr (Extra.t i) => fullOf x hz (casc2OfMid x (RabinVariantTower.t i))
  | Sum.inr Extra.u => fullOf x hz (casc2Of x (casc1Of x HNNExtension.t))
  | Sum.inr Extra.b => fullOf x hz (casc2Of x (bLetter x))
  | Sum.inr Extra.c => fullOf x hz (cLetter x)
  | Sum.inr Extra.k => kLetter x hz

/-- The homomorphism the generator map induces on the free group. -/
noncomputable def towerLift : FreeGroup (Gen m) →* Full x hz :=
  FreeGroup.lift (towerGen x xs (hz := hz))

@[simp] theorem towerLift_X (i : Fin m) :
    towerLift x xs (hz := hz) (X i) = fullOf x hz (casc2OfBase x (xs i)) := by
  simp [towerLift, X, towerGen]

@[simp] theorem towerLift_S :
    towerLift x xs (hz := hz) S
      = fullOf x hz (casc2OfMid x (midOfBase (RabinVariantTower.s))) := by
  simp [towerLift, S, towerGen]

@[simp] theorem towerLift_T (i : Fin (m + 1)) :
    towerLift x xs (hz := hz) (T i)
      = fullOf x hz (casc2OfMid x (RabinVariantTower.t i)) := by
  simp [towerLift, T, towerGen]

@[simp] theorem towerLift_U :
    towerLift x xs (hz := hz) U
      = fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) := by
  simp [towerLift, U, towerGen]

@[simp] theorem towerLift_B :
    towerLift x xs (hz := hz) B = fullOf x hz (casc2Of x (bLetter x)) := by
  simp [towerLift, B, towerGen]

@[simp] theorem towerLift_C :
    towerLift x xs (hz := hz) C = fullOf x hz (cLetter x) := by
  simp [towerLift, C, towerGen]

@[simp] theorem towerLift_K :
    towerLift x xs (hz := hz) K = kLetter x hz := by
  simp [towerLift, K, towerGen]

/-- The source generators, mapped through. -/
theorem towerLift_emb (r : FreeGroup (Fin m)) :
    towerLift x xs (hz := hz) (emb r)
      = (fullOf x hz).comp (casc2OfBase x) (FreeGroup.lift xs r) := by
  have h : (towerLift x xs (hz := hz)).comp (emb : FreeGroup (Fin m) →* _)
      = ((fullOf x hz).comp (casc2OfBase x)).comp (FreeGroup.lift xs) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [emb, towerLift, towerGen]
  exact DFunLike.congr_fun h r

/-! ## The relators hold in the tower

Each family is one of the tower's conjugation lemmas, pushed up the cascade one
layer at a time. -/

theorem casc2OfBase_eq (g : Γ) :
    casc2OfBase x g = casc2OfMid x (midOfBase (Monoid.Coprod.inl g)) := rfl

/-- The killing relation, pushed to the top. -/
theorem conj_ts_top (i : Fin (m + 1)) :
    fullOf x hz (casc2OfMid x (ts x i))
      = fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) *
        fullOf x hz (casc2OfMid x (t i)) *
        (fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)))⁻¹ := by
  have h0 := conj_t_eq_ts x i
  have h1 := congrArg (casc1Of x) h0
  rw [map_mul, map_mul, map_inv] at h1
  have h2 := congrArg (casc2Of x) h1
  rw [map_mul, map_mul, map_inv] at h2
  have h3 := congrArg (fullOf x hz) h2
  rw [map_mul, map_mul, map_inv] at h3
  exact h3

/-- The first cascade relation, pushed to the top. -/
theorem casc1_top :
    fullOf x hz (casc2Of x (casc1Of x ((HNNExtension.t : Top Γ x) ^ (2 : ℤ))))
      = fullOf x hz (casc2Of x (bLetter x)) *
        fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) *
        (fullOf x hz (casc2Of x (bLetter x)))⁻¹ := by
  have h1 := congrArg (casc2Of x) (casc1_conj x)
  rw [map_mul, map_mul, map_inv] at h1
  have h2 := congrArg (fullOf x hz) h1
  rw [map_mul, map_mul, map_inv] at h2
  exact h2

/-- The second cascade relation, pushed to the top. -/
theorem casc2_top :
    fullOf x hz (casc2Of x ((bLetter x) ^ (2 : ℤ)))
      = fullOf x hz (cLetter x) * fullOf x hz (casc2Of x (bLetter x)) *
        (fullOf x hz (cLetter x))⁻¹ := by
  have h1 := congrArg (fullOf x hz) (casc2_conj x)
  rw [map_mul, map_mul, map_inv] at h1
  exact h1

/-! ## Each relator dies -/

/-- The `b`-relator holds. -/
theorem relator_B_dies :
    towerLift x xs (hz := hz) (B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹) = 1 := by
  have h := casc1_top x xs (hz := hz)
  have hpow : fullOf x hz (casc2Of x (casc1Of x
      ((HNNExtension.t : Top Γ x) ^ (2 : ℤ))))
      = (fullOf x hz (casc2Of x (casc1Of x HNNExtension.t))) ^ (2 : ℕ) := by
    rw [map_zpow, map_zpow, map_zpow, ← zpow_natCast]
    norm_cast
  rw [hpow] at h
  simp only [map_mul, map_inv, map_pow, towerLift_B, towerLift_U]
  rw [← h]
  group

/-- The `c`-relator holds. -/
theorem relator_C_dies :
    towerLift x xs (hz := hz) (C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹) = 1 := by
  have h := casc2_top x xs (hz := hz)
  have hpow : fullOf x hz (casc2Of x ((bLetter x) ^ (2 : ℤ)))
      = (fullOf x hz (casc2Of x (bLetter x))) ^ (2 : ℕ) := by
    rw [map_zpow, map_zpow, ← zpow_natCast]
    norm_cast
  rw [hpow] at h
  simp only [map_mul, map_inv, map_pow, towerLift_B, towerLift_C]
  rw [← h]
  group

/-- The witness element, expanded.  Proved in `Casc2`, where nothing depends on
the infinite-order hypothesis: the tower's type mentions that hypothesis, which
mentions `zElt`, so `zElt` cannot be rewritten inside a goal of tower type. -/
theorem zElt_eq :
    zElt x xs w
      = casc2OfBase x (FreeGroup.lift xs w) *
        casc2OfMid x (midOfBase RabinVariantTower.s) *
        (casc2OfBase x (FreeGroup.lift xs w))⁻¹ *
        (casc2OfMid x (midOfBase RabinVariantTower.s))⁻¹ := by
  unfold zElt
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, casc2OfBase_eq]
  simp [mul_assoc]

/-- The witness word maps to the witness element.  The last step is `congrArg`
rather than `rw`, for the reason above. -/
theorem towerLift_Z :
    towerLift x xs (hz := hz) (Z w) = fullOf x hz (zElt x xs w) := by
  have hL : towerLift x xs (hz := hz) (Z w)
      = fullOf x hz (casc2OfBase x (FreeGroup.lift xs w) *
          casc2OfMid x (midOfBase RabinVariantTower.s) *
          (casc2OfBase x (FreeGroup.lift xs w))⁻¹ *
          (casc2OfMid x (midOfBase RabinVariantTower.s))⁻¹) := by
    rw [Z, map_mul, map_mul, map_mul, map_inv, map_inv, towerLift_emb,
      towerLift_S, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp [MonoidHom.comp_apply, mul_assoc]
  rw [hL]
  exact congrArg (fullOf x hz) (zElt_eq x xs).symm

/-- The `k`-relator holds: this is where the witness enters. -/
theorem relator_K_dies :
    towerLift x xs (hz := hz) (K * Z w * K⁻¹ * C⁻¹) = 1 := by
  have h := full_conj x hz
  simp only [map_mul, map_inv, towerLift_K, towerLift_Z, towerLift_C]
  rw [← h]
  group

end RabinVariantPresentation
end GroupApproximation