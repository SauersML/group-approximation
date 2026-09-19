import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.Algebra.Colimit.DirectLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg groups commute with directed colimits of rings (k2-poly, piece F.5)

This is Tulenbaev (Math. USSR Sb. 45 (1983)), Lemma 2.2: `lim St_r(B_i) ≅ St_r(lim B_i)`. Here it
is in the two forms that the local–global argument consumes. Let `(R_i, φ_ij)` be a directed
system of rings over a nonempty directed preorder. Let `ψ_i : R_i → S` be a compatible cocone that
is a colimit, in the elementwise sense:
* every `s ∈ S` is some `ψ_i r`;
* `ψ_i a = ψ_i b` forces `φ_ij a = φ_ij b` for some `j ≥ i`.
Then:
* `exists_ringMap_eq`: every element of `St_I(S)` comes from some `St_I(R_i)`;
* `exists_ringMap_eq_one`: if `u ∈ St_I(R_i)` dies in `St_I(S)`, it already dies in some
  `St_I(R_j)`, `j ≥ i`.

The second is the substantial one. It goes through Mathlib's `DirectLimit` of the groups
`St_I(R_i)`. A homomorphism `St_I(S) → lim St_I(R_i)` is built on the Steinberg presentation,
by lifting coefficients, and it is shown to split the canonical maps. Then
`DirectLimit.exists_eq_one` finishes.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section Colimit

variable {ι : Type*} [Preorder ι]
variable (I : Type*) [Fintype I] [DecidableEq I]
variable {R : ι → Type*} [∀ i, Ring (R i)] (φ : ∀ i j, i ≤ j → R i →+* R j)

/-- A directed system of rings induces one of Steinberg groups. -/
instance stDirectedSystem [DirectedSystem R (fun i j h => φ i j h)] :
    DirectedSystem (fun i => SteinbergGroup I (R i)) (fun i j h => ringMap (I := I) (φ i j h)) where
  map_self i u := by
    have h : ringMap (I := I) (φ i i le_rfl) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      rintro ⟨k, l, hkl, a⟩
      change ringMap (φ i i le_rfl) (x k l hkl a) = x k l hkl a
      rw [ringMap_x, DirectedSystem.map_self' φ a]
    exact DFunLike.congr_fun h u
  map_map k j i hij hjk u := by
    have h : (ringMap (I := I) (φ j k hjk)).comp (ringMap (φ i j hij)) =
        ringMap (φ i k (hij.trans hjk)) := by
      apply PresentedGroup.ext
      rintro ⟨a, b, hab, r⟩
      change ringMap (φ j k hjk) (ringMap (φ i j hij) (x a b hab r)) =
        ringMap (φ i k (hij.trans hjk)) (x a b hab r)
      rw [ringMap_x, ringMap_x, ringMap_x, DirectedSystem.map_map' φ hij hjk r]
    exact DFunLike.congr_fun h u

variable [DirectedSystem R (fun i j h => φ i j h)] [IsDirectedOrder ι] [Nonempty ι]

/-- The direct limit of the Steinberg groups `St_I(R_i)`. -/
abbrev StLim : Type _ :=
  DirectLimit (fun i => SteinbergGroup I (R i)) (fun i j h => ringMap (I := I) (φ i j h))

/-- The canonical map `St_I(R_i) → lim St_I(R_j)`. -/
noncomputable def stOf (i : ι) : SteinbergGroup I (R i) →* StLim I φ where
  toFun u := ⟦⟨i, u⟩⟧
  map_one' := (DirectLimit.one_def (G := fun i => SteinbergGroup I (R i))
    (f := fun i j h => ringMap (I := I) (φ i j h)) i).symm
  map_mul' u v := (DirectLimit.mul_def (G := fun i => SteinbergGroup I (R i))
    (f := fun i j h => ringMap (I := I) (φ i j h)) i u v).symm

variable {I φ}

theorem stOf_le {i j : ι} (h : i ≤ j) (u : SteinbergGroup I (R i)) :
    stOf I φ i u = stOf I φ j (ringMap (φ i j h) u) :=
  DirectLimit.eq_of_le (F := fun i => SteinbergGroup I (R i))
    (f := fun i j h => ringMap (I := I) (φ i j h)) ⟨i, u⟩ j h

#audit_axioms stOf_le

theorem stOf_eq_one_iff (i : ι) (u : SteinbergGroup I (R i)) :
    stOf I φ i u = 1 ↔ ∃ j, ∃ h : i ≤ j, ringMap (φ i j h) u = 1 :=
  DirectLimit.exists_eq_one (G := fun i => SteinbergGroup I (R i))
    (f := fun i j h => ringMap (I := I) (φ i j h)) ⟨i, u⟩

#audit_axioms stOf_eq_one_iff

variable {S : Type*} [Ring S] (ψ : ∀ i, R i →+* S)
  (hψ : ∀ i j (h : i ≤ j) (a : R i), ψ j (φ i j h a) = ψ i a)
  (hinj : ∀ i (a b : R i), ψ i a = ψ i b → ∃ j, ∃ h : i ≤ j, φ i j h a = φ i j h b)

include hψ hinj in
/-- Root elements whose coefficients have the same image in `S` agree in the limit. -/
theorem stOf_x_eq {i j : ι} {a : R i} {b : R j} (hab : ψ i a = ψ j b) (k l : I) (hkl : k ≠ l) :
    stOf I φ i (x k l hkl a) = stOf I φ j (x k l hkl b) := by
  obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
  have hm : ψ m (φ i m him a) = ψ m (φ j m hjm b) := by rw [hψ, hψ, hab]
  obtain ⟨n, hmn, hn⟩ := hinj m _ _ hm
  rw [stOf_le him, stOf_le hjm, ringMap_x, ringMap_x, stOf_le hmn, stOf_le hmn, ringMap_x,
    ringMap_x, hn]

#audit_axioms stOf_x_eq

variable (hsurj : ∀ s : S, ∃ i, ∃ r : R i, ψ i r = s)

/-- The limit homomorphism on generators, lifting each coefficient to some `R_i`. -/
noncomputable def limGen (g : SteinbergGenerator I S) : StLim I φ :=
  stOf I φ (hsurj g.coefficient).choose
    (x g.row g.column g.row_ne_column (hsurj g.coefficient).choose_spec.choose)

include hψ hinj in
/-- Any lift of the coefficient computes the limit generator. -/
theorem limGen_eq (k l : I) (hkl : k ≠ l) {i : ι} {r : R i} {s : S} (h : ψ i r = s) :
    limGen (φ := φ) ψ hsurj ⟨k, l, hkl, s⟩ = stOf I φ i (x k l hkl r) :=
  stOf_x_eq ψ hψ hinj ((hsurj s).choose_spec.choose_spec.trans h.symm) k l hkl

#audit_axioms limGen_eq

include hψ hinj in
theorem limGen_kills (w : FreeGroup (SteinbergGenerator I S))
    (hw : w ∈ relations (I := I) (R := S)) : FreeGroup.lift (limGen (φ := φ) ψ hsurj) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add k l hkl a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      obtain ⟨i₁, r₁, h₁⟩ := hsurj a
      obtain ⟨i₂, r₂, h₂⟩ := hsurj b
      obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge i₁ i₂
      have ha : ψ m (φ i₁ m hm₁ r₁) = a := (hψ _ _ _ _).trans h₁
      have hb : ψ m (φ i₂ m hm₂ r₂) = b := (hψ _ _ _ _).trans h₂
      have hab : ψ m (φ i₁ m hm₁ r₁ + φ i₂ m hm₂ r₂) = a + b := by rw [map_add, ha, hb]
      change limGen (φ := φ) ψ hsurj ⟨k, l, hkl, a⟩ * limGen (φ := φ) ψ hsurj ⟨k, l, hkl, b⟩ *
          (limGen (φ := φ) ψ hsurj ⟨k, l, hkl, a + b⟩)⁻¹ = 1
      rw [limGen_eq ψ hψ hinj hsurj k l hkl ha, limGen_eq ψ hψ hinj hsurj k l hkl hb,
        limGen_eq ψ hψ hinj hsurj k l hkl hab, ← map_mul, x_mul, mul_inv_cancel]
  | commute k l k' l' hkl hkl' hlk' hl'k a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      obtain ⟨i₁, r₁, h₁⟩ := hsurj a
      obtain ⟨i₂, r₂, h₂⟩ := hsurj b
      obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge i₁ i₂
      have ha : ψ m (φ i₁ m hm₁ r₁) = a := (hψ _ _ _ _).trans h₁
      have hb : ψ m (φ i₂ m hm₂ r₂) = b := (hψ _ _ _ _).trans h₂
      change ⁅limGen (φ := φ) ψ hsurj ⟨k, l, hkl, a⟩, limGen (φ := φ) ψ hsurj ⟨k', l', hkl', b⟩⁆ = 1
      rw [limGen_eq ψ hψ hinj hsurj k l hkl ha, limGen_eq ψ hψ hinj hsurj k' l' hkl' hb,
        ← map_commutatorElement,
        (x_commute_of_ne k l k' l' hkl hkl' hlk' hl'k _ _).commutator_eq, map_one]
  | adjacent k l n hkl hln hkn a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      obtain ⟨i₁, r₁, h₁⟩ := hsurj a
      obtain ⟨i₂, r₂, h₂⟩ := hsurj b
      obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge i₁ i₂
      have ha : ψ m (φ i₁ m hm₁ r₁) = a := (hψ _ _ _ _).trans h₁
      have hb : ψ m (φ i₂ m hm₂ r₂) = b := (hψ _ _ _ _).trans h₂
      have hab : ψ m (φ i₁ m hm₁ r₁ * φ i₂ m hm₂ r₂) = a * b := by rw [map_mul, ha, hb]
      change ⁅limGen (φ := φ) ψ hsurj ⟨k, l, hkl, a⟩, limGen (φ := φ) ψ hsurj ⟨l, n, hln, b⟩⁆ *
          (limGen (φ := φ) ψ hsurj ⟨k, n, hkn, a * b⟩)⁻¹ = 1
      rw [limGen_eq ψ hψ hinj hsurj k l hkl ha, limGen_eq ψ hψ hinj hsurj l n hln hb,
        limGen_eq ψ hψ hinj hsurj k n hkn hab, ← map_commutatorElement,
        x_commutator k l n hkl hln hkn, mul_inv_cancel]

#audit_axioms limGen_kills

/-- The homomorphism `St_I(S) → lim St_I(R_i)`. -/
noncomputable def limHom : SteinbergGroup I S →* StLim I φ :=
  PresentedGroup.toGroup (f := limGen (φ := φ) ψ hsurj) (limGen_kills ψ hψ hinj hsurj)

theorem limHom_x (k l : I) (hkl : k ≠ l) (s : S) :
    limHom ψ hψ hinj hsurj (x k l hkl s) = limGen (φ := φ) ψ hsurj ⟨k, l, hkl, s⟩ :=
  PresentedGroup.toGroup.of _

/-- `limHom` splits the canonical maps: `limHom ∘ ringMap ψ_i = stOf i`. -/
theorem limHom_ringMap (i : ι) (u : SteinbergGroup I (R i)) :
    limHom ψ hψ hinj hsurj (ringMap (ψ i) u) = stOf I φ i u := by
  have h : (limHom ψ hψ hinj hsurj).comp (ringMap (ψ i)) = stOf I φ i := by
    apply PresentedGroup.ext
    rintro ⟨k, l, hkl, a⟩
    change limHom ψ hψ hinj hsurj (ringMap (ψ i) (x k l hkl a)) = stOf I φ i (x k l hkl a)
    rw [ringMap_x, limHom_x]
    exact limGen_eq ψ hψ hinj hsurj k l hkl (i := i) (r := a) rfl
  exact DFunLike.congr_fun h u

#audit_axioms limHom_ringMap

include hψ hinj hsurj in
/-- **Steinberg groups commute with directed colimits, injectivity form** (Tulenbaev Lemma 2.2).
An element of `St_I(R_i)` that dies in `St_I(S)` already dies in some `St_I(R_j)`, `j ≥ i`. -/
theorem exists_ringMap_eq_one {i : ι} {u : SteinbergGroup I (R i)}
    (hu : ringMap (ψ i) u = 1) : ∃ j, ∃ h : i ≤ j, ringMap (φ i j h) u = 1 := by
  exact (stOf_eq_one_iff i u).mp (by rw [← limHom_ringMap ψ hψ hinj hsurj, hu, map_one])

#audit_axioms exists_ringMap_eq_one

end Colimit

section ColimitSurj

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R : ι → Type*} [∀ i, Ring (R i)] {φ : ∀ i j, i ≤ j → R i →+* R j}
variable {S : Type*} [Ring S] (ψ : ∀ i, R i →+* S)
  (hψ : ∀ i j (h : i ≤ j) (a : R i), ψ j (φ i j h a) = ψ i a)
  (hsurj : ∀ s : S, ∃ i, ∃ r : R i, ψ i r = s)

include hψ hsurj in
/-- **Steinberg groups commute with directed colimits, surjectivity form.** Every element of
`St_I(S)` comes from some `St_I(R_i)`. -/
theorem exists_ringMap_eq (v : SteinbergGroup I S) :
    ∃ i, ∃ u : SteinbergGroup I (R i), ringMap (ψ i) u = v := by
  have hcomp : ∀ i j (h : i ≤ j), (ψ j).comp (φ i j h) = ψ i := fun i j h =>
    RingHom.ext (hψ i j h)
  let U : Subgroup (SteinbergGroup I S) :=
    { carrier := {v | ∃ i, ∃ u : SteinbergGroup I (R i), ringMap (ψ i) u = v}
      mul_mem' := by
        rintro _ _ ⟨i₁, u₁, rfl⟩ ⟨i₂, u₂, rfl⟩
        obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge i₁ i₂
        refine ⟨m, ringMap (φ i₁ m hm₁) u₁ * ringMap (φ i₂ m hm₂) u₂, ?_⟩
        rw [map_mul, BooneHigman.SteinbergBasic.ringMap_ringMap,
          BooneHigman.SteinbergBasic.ringMap_ringMap, hcomp, hcomp]
      one_mem' := by
        obtain ⟨i⟩ := ‹Nonempty ι›
        exact ⟨i, 1, map_one _⟩
      inv_mem' := by
        rintro _ ⟨i, u, rfl⟩
        exact ⟨i, u⁻¹, map_inv _ u⟩ }
  refine PresentedGroup.generated_by _ U ?_ v
  rintro ⟨k, l, hkl, s⟩
  obtain ⟨i, r, hr⟩ := hsurj s
  exact ⟨i, x k l hkl r, (ringMap_x (ψ i) k l hkl r).trans (congrArg (x k l hkl) hr)⟩

#audit_axioms exists_ringMap_eq

end ColimitSurj

end K2Found
end BooneHigmanLinear
end GroupApproximation
