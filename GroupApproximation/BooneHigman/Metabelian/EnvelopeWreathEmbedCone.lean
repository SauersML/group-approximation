import GroupApproximation.BooneHigman.V.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Permuting separated cones and acting inside them

This module supplies the cone calculus behind Zaremsky's Proposition 2.5 (`EnvelopeWreathEmbed`).
A family `c : ι → List X` is *separated* (`ConesSeparated c`) when the cone of `c j` meets the
cone of `c i` only for `j = i`; injective families of words of one length are separated
(`conesSeparated_of_length`).

For a permutation `σ` of `ι` and `g : ι → Perm (Cantor X)`, `coneMap hsep σ g` sends
`c i · z ↦ c (σ i) · g i z` and fixes every point outside the cones.

* `coneMap_prepend`: the defining formula on the cone of `c i`;
* `coneMap_mul`: `coneMap σ g * coneMap τ h = coneMap (σ * τ) (i ↦ g (τ i) * h i)`, the
  multiplication of `(ι → Perm) ⋊ Perm ι`;
* `coneMap_eq_one`: `coneMap σ g = 1` forces `σ = 1` and `g = 1` (for `X` nonempty).

Route: `coneMapFun` chooses the cone containing the point (unique by separation); the product
formula is checked on each cone and off the cones, and the inverse is the product formula for
`σ⁻¹` and `i ↦ (g (σ⁻¹ i))⁻¹`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

noncomputable section

variable {X : Type*} {ι : Type*} {c : ι → List X}

/-- The cones of the words `c i` are pairwise disjoint. -/
def ConesSeparated (c : ι → List X) : Prop :=
  ∀ (i j : ι) (z : Cantor X), IsStreamPrefix (c j) (prepend (c i) z) → j = i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.ConesSeparated

theorem conesSeparated_of_length {N : ℕ} (hc : Function.Injective c)
    (hlen : ∀ i, (c i).length = N) : ConesSeparated c := by
  intro i j z h
  have e : (c j).length = (c i).length := (hlen j).trans (hlen i).symm
  exact hc ((prefix_of_isStreamPrefix_of_length_le h (isStreamPrefix_prepend (c i) z)
    e.le).eq_of_length e)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.conesSeparated_of_length

open Classical in
/-- `c i · z ↦ c (σ i) · g i z` on the cones, the identity elsewhere. -/
def coneMapFun (c : ι → List X) (σ : Equiv.Perm ι) (g : ι → Equiv.Perm (Cantor X))
    (x : Cantor X) : Cantor X :=
  if h : ∃ i, IsStreamPrefix (c i) x then
    prepend (c (σ h.choose)) (g h.choose (dropN (c h.choose).length x))
  else x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun

theorem coneMapFun_of_exists (σ : Equiv.Perm ι) (g : ι → Equiv.Perm (Cantor X)) {x : Cantor X}
    (h : ∃ i, IsStreamPrefix (c i) x) :
    coneMapFun c σ g x = prepend (c (σ h.choose)) (g h.choose (dropN (c h.choose).length x)) := by
  rw [coneMapFun, dif_pos h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun_of_exists

theorem coneMapFun_of_not (σ : Equiv.Perm ι) (g : ι → Equiv.Perm (Cantor X)) {x : Cantor X}
    (h : ¬ ∃ i, IsStreamPrefix (c i) x) : coneMapFun c σ g x = x := by
  rw [coneMapFun, dif_neg h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun_of_not

theorem coneMapFun_prepend (hsep : ConesSeparated c) (σ : Equiv.Perm ι)
    (g : ι → Equiv.Perm (Cantor X)) (i : ι) (z : Cantor X) :
    coneMapFun c σ g (prepend (c i) z) = prepend (c (σ i)) (g i z) := by
  have h : ∃ j, IsStreamPrefix (c j) (prepend (c i) z) := ⟨i, isStreamPrefix_prepend _ _⟩
  rw [coneMapFun_of_exists σ g h, hsep i h.choose z h.choose_spec, dropN_prepend]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun_prepend

theorem coneMapFun_comp (hsep : ConesSeparated c) (σ τ : Equiv.Perm ι)
    (g h : ι → Equiv.Perm (Cantor X)) (x : Cantor X) :
    coneMapFun c σ g (coneMapFun c τ h x) =
      coneMapFun c (σ * τ) (fun i => g (τ i) * h i) x := by
  by_cases hx : ∃ i, IsStreamPrefix (c i) x
  · obtain ⟨i, hi⟩ := hx
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hi
    simp only [coneMapFun_prepend hsep, Equiv.Perm.mul_apply]
  · rw [coneMapFun_of_not τ h hx, coneMapFun_of_not σ g hx, coneMapFun_of_not _ _ hx]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun_comp

theorem coneMapFun_one (hsep : ConesSeparated c) (x : Cantor X) :
    coneMapFun c 1 (fun _ => 1) x = x := by
  by_cases hx : ∃ i, IsStreamPrefix (c i) x
  · obtain ⟨i, hi⟩ := hx
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hi
    simp only [coneMapFun_prepend hsep, Equiv.Perm.one_apply]
  · exact coneMapFun_of_not _ _ hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMapFun_one

/-- `coneMapFun` as a permutation of the Cantor set. -/
def coneMap (hsep : ConesSeparated c) (σ : Equiv.Perm ι) (g : ι → Equiv.Perm (Cantor X)) :
    Equiv.Perm (Cantor X) where
  toFun := coneMapFun c σ g
  invFun := coneMapFun c σ⁻¹ fun i => (g (σ⁻¹ i))⁻¹
  left_inv x := by
    refine (coneMapFun_comp hsep σ⁻¹ σ (fun i => (g (σ⁻¹ i))⁻¹) g x).trans ?_
    refine (congrArg₂
      (fun (τ : Equiv.Perm ι) (G : ι → Equiv.Perm (Cantor X)) => coneMapFun c τ G x)
      (inv_mul_cancel σ) (funext fun i => ?_)).trans (coneMapFun_one hsep x)
    exact (congrArg (fun k => (g k)⁻¹ * g i) (Equiv.symm_apply_apply σ i)).trans
      (inv_mul_cancel (g i))
  right_inv x := by
    refine (coneMapFun_comp hsep σ σ⁻¹ g (fun i => (g (σ⁻¹ i))⁻¹) x).trans ?_
    refine (congrArg₂
      (fun (τ : Equiv.Perm ι) (G : ι → Equiv.Perm (Cantor X)) => coneMapFun c τ G x)
      (mul_inv_cancel σ) (funext fun i => ?_)).trans (coneMapFun_one hsep x)
    exact mul_inv_cancel (g (σ⁻¹ i))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap

theorem coneMap_prepend (hsep : ConesSeparated c) (σ : Equiv.Perm ι)
    (g : ι → Equiv.Perm (Cantor X)) (i : ι) (z : Cantor X) :
    coneMap hsep σ g (prepend (c i) z) = prepend (c (σ i)) (g i z) :=
  coneMapFun_prepend hsep σ g i z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_prepend

theorem coneMap_of_not (hsep : ConesSeparated c) (σ : Equiv.Perm ι)
    (g : ι → Equiv.Perm (Cantor X)) {x : Cantor X} (h : ¬ ∃ i, IsStreamPrefix (c i) x) :
    coneMap hsep σ g x = x :=
  coneMapFun_of_not σ g h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_of_not

theorem coneMap_mul (hsep : ConesSeparated c) (σ τ : Equiv.Perm ι)
    (g h : ι → Equiv.Perm (Cantor X)) :
    coneMap hsep σ g * coneMap hsep τ h = coneMap hsep (σ * τ) (fun i => g (τ i) * h i) :=
  Equiv.ext fun x => coneMapFun_comp hsep σ τ g h x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_mul

theorem coneMap_eq_one [Nonempty X] (hsep : ConesSeparated c) {σ : Equiv.Perm ι}
    {g : ι → Equiv.Perm (Cantor X)} (h : coneMap hsep σ g = 1) (i : ι) :
    σ i = i ∧ g i = 1 := by
  have e : ∀ z, prepend (c (σ i)) (g i z) = prepend (c i) z := fun z =>
    (coneMap_prepend hsep σ g i z).symm.trans
      (congrArg (fun k : Equiv.Perm (Cantor X) => k (prepend (c i) z)) h)
  have hp := isStreamPrefix_prepend (c (σ i)) (g i fun _ => Classical.arbitrary X)
  rw [e] at hp
  have hσ : σ i = i := hsep i (σ i) _ hp
  refine ⟨hσ, Equiv.ext fun z => ?_⟩
  have e' := e z
  rw [hσ] at e'
  exact prepend_injective (c i) e'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_eq_one

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
