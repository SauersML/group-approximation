import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Polynomial.Eval.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative Steinberg groups: kernel form and retraction splitting (k2-poly, piece F.2–F.3)

Tulenbaev (*The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), §1) works with
the relative group `St_r(A, 𝔄)` of an ideal `𝔄 ⊆ A`, and with the splitting
`St_r(A) ≅ St_r(B) ⋉ St_r(A, 𝔄)` along a retraction `A → B` with kernel `𝔄` (Prop. 1.6). This
file gives both in kernel form, for any finite index type `I`.

* `relSt f`: for a ring homomorphism `f : A →+* B`, the kernel of
  `ringMap f : St_I(A) → St_I(B)`.
* `relSt_eq_normalClosure` (F.2): for surjective `f`, `relSt f` is the normal closure of the
  relative roots `x_ij(a)` with `f a = 0`. The proof builds the inverse of
  `St_I(A)/⟨⟨x_ij(ker f)⟩⟩ → St_I(B)` on the Steinberg presentation of `St_I(B)`, through any
  set-theoretic section of `f`.
* `splitEquiv` (F.3): for a retraction, `ρ ∘ ι = id` with `ι : B →+* A`, multiplication
  `(n, g) ↦ n · ι(g)` is an isomorphism `relSt ρ ⋊ St_I(B) ≃* St_I(A)`. The action is conjugation
  through `ringMap ι`.
* The polynomial instance: `polyRelSt A = relSt (evalRingHom 0)` on `St_I(A[X])`, split by the
  constants `C`. Its normal generation is `polyRelSt_eq_normalClosure`.

Everything is formal: the Steinberg presentation, `ringMap` functoriality, and Mathlib's
semidirect products.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section Kernel

variable (I : Type*) {A B : Type*} [Fintype I] [DecidableEq I] [Ring A] [Ring B]

/-- **The relative Steinberg group, kernel form.** `St_I(A, f) = ker (ringMap f)`. -/
def relSt (f : A →+* B) : Subgroup (SteinbergGroup I A) :=
  (ringMap f).ker

instance relSt_normal (f : A →+* B) : (relSt I f).Normal :=
  MonoidHom.normal_ker _

variable {I}

theorem mem_relSt {f : A →+* B} {u : SteinbergGroup I A} : u ∈ relSt I f ↔ ringMap f u = 1 :=
  MonoidHom.mem_ker

variable (I)

/-- The relative roots: `x_ij(a)` with `f a = 0`. -/
def relRoots (f : A →+* B) : Set (SteinbergGroup I A) :=
  {u | ∃ (i j : I) (hij : i ≠ j) (a : A), f a = 0 ∧ x i j hij a = u}

/-- The normal closure of the relative roots. -/
abbrev relNC (f : A →+* B) : Subgroup (SteinbergGroup I A) :=
  Subgroup.normalClosure (relRoots I f)

/-- The quotient map `St_I(A) → St_I(A)/⟨⟨x_ij(ker f)⟩⟩`. -/
abbrev relQ (f : A →+* B) : SteinbergGroup I A →* SteinbergGroup I A ⧸ relNC I f :=
  QuotientGroup.mk' (relNC I f)

variable {I}

theorem relRoots_subset (f : A →+* B) : relRoots I f ⊆ relSt I f := by
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  rw [SetLike.mem_coe, mem_relSt, ringMap_x, ha, x_zero]

#audit_axioms relRoots_subset

theorem relNC_le (f : A →+* B) : relNC I f ≤ relSt I f :=
  Subgroup.normalClosure_le_normal (relRoots_subset f)

#audit_axioms relNC_le

/-- Root elements whose coefficients agree modulo `ker f` agree modulo the relative roots. -/
theorem relQ_x_eq {f : A →+* B} {i j : I} (hij : i ≠ j) {a a' : A} (h : f a = f a') :
    relQ I f (x i j hij a) = relQ I f (x i j hij a') := by
  have hd : x i j hij (a - a') ∈ relNC I f :=
    Subgroup.subset_normalClosure ⟨i, j, hij, a - a', by rw [map_sub, h, sub_self], rfl⟩
  have h1 : relQ I f (x i j hij (a - a')) = 1 := (QuotientGroup.eq_one_iff _).mpr hd
  have hx : x i j hij a = x i j hij (a - a') * x i j hij a' := by
    rw [x_mul, sub_add_cancel]
  rw [hx, map_mul, h1, one_mul]

#audit_axioms relQ_x_eq

section Surjective

variable (f : A →+* B) (hf : Function.Surjective f)

/-- The inverse on generators, through the section `Function.surjInv hf`. -/
noncomputable def invGen (g : SteinbergGenerator I B) : SteinbergGroup I A ⧸ relNC I f :=
  relQ I f (x g.row g.column g.row_ne_column (Function.surjInv hf g.coefficient))

theorem invGen_kills (w : FreeGroup (SteinbergGenerator I B))
    (hw : w ∈ relations (I := I) (R := B)) : FreeGroup.lift (invGen f hf) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, invGen]
      change relQ I f (x i j hij (Function.surjInv hf a)) *
          relQ I f (x i j hij (Function.surjInv hf b)) *
          (relQ I f (x i j hij (Function.surjInv hf (a + b))))⁻¹ = 1
      rw [← map_mul, x_mul,
        relQ_x_eq hij (show f (Function.surjInv hf a + Function.surjInv hf b) =
          f (Function.surjInv hf (a + b)) by
            rw [map_add, Function.surjInv_eq hf a, Function.surjInv_eq hf b,
              Function.surjInv_eq hf (a + b)]),
        mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, invGen]
      change ⁅relQ I f (x i j hij (Function.surjInv hf a)),
          relQ I f (x k l hkl (Function.surjInv hf b))⁆ = 1
      rw [← map_commutatorElement,
        (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq, map_one]
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of, invGen]
      change ⁅relQ I f (x i j hij (Function.surjInv hf a)),
          relQ I f (x j k hjk (Function.surjInv hf b))⁆ *
          (relQ I f (x i k hik (Function.surjInv hf (a * b))))⁻¹ = 1
      rw [← map_commutatorElement, x_commutator i j k hij hjk hik,
        relQ_x_eq hik (show f (Function.surjInv hf a * Function.surjInv hf b) =
          f (Function.surjInv hf (a * b)) by
            rw [map_mul, Function.surjInv_eq hf a, Function.surjInv_eq hf b,
              Function.surjInv_eq hf (a * b)]),
        mul_inv_cancel]

#audit_axioms invGen_kills

/-- The inverse homomorphism `St_I(B) → St_I(A)/⟨⟨x_ij(ker f)⟩⟩`. -/
noncomputable def invHom : SteinbergGroup I B →* SteinbergGroup I A ⧸ relNC I f :=
  PresentedGroup.toGroup (f := invGen f hf) (invGen_kills f hf)

theorem invHom_x (i j : I) (hij : i ≠ j) (b : B) :
    invHom f hf (x i j hij b) = relQ I f (x i j hij (Function.surjInv hf b)) :=
  PresentedGroup.toGroup.of _

theorem invHom_ringMap (u : SteinbergGroup I A) : invHom f hf (ringMap f u) = relQ I f u := by
  have h : (invHom f hf).comp (ringMap f) = relQ I f := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change invHom f hf (ringMap f (x i j hij a)) = relQ I f (x i j hij a)
    rw [ringMap_x, invHom_x]
    exact relQ_x_eq hij (Function.surjInv_eq hf (f a))
  exact DFunLike.congr_fun h u

#audit_axioms invHom_ringMap

include hf in
/-- **The relative group is normally generated by the relative roots** (F.2). For a surjective
ring homomorphism `f : A →+* B`, `ker (St_I(A) → St_I(B))` is the normal closure of the
`x_ij(a)` with `f a = 0`. -/
theorem relSt_eq_normalClosure : relSt I f = relNC I f := by
  refine le_antisymm (fun u hu => ?_) (relNC_le f)
  have h := invHom_ringMap f hf u
  rw [mem_relSt.mp hu, map_one] at h
  exact (QuotientGroup.eq_one_iff u).mp h.symm

#audit_axioms relSt_eq_normalClosure

end Surjective

end Kernel

section Retraction

variable {I A B : Type*} [Fintype I] [DecidableEq I] [Ring A] [Ring B]
  (ι : B →+* A) (ρ : A →+* B) (hρι : Function.LeftInverse ρ ι)

include hρι in
theorem ringMap_leftInverse (u : SteinbergGroup I B) : ringMap ρ (ringMap ι u) = u := by
  have h : (ringMap (I := I) ρ).comp (ringMap ι) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change ringMap ρ (ringMap ι (x i j hij a)) = x i j hij a
    rw [ringMap_x, ringMap_x, hρι a]
  exact DFunLike.congr_fun h u

#audit_axioms ringMap_leftInverse

/-- `St_I(B)` acts on the relative group `relSt ρ` by conjugation through `ringMap ι`. -/
noncomputable def relAct : SteinbergGroup I B →* MulAut (relSt I ρ) :=
  (MulAut.conjNormal (H := relSt I ρ)).comp (ringMap ι)

/-- Multiplication `relSt ρ ⋊ St_I(B) → St_I(A)`, `(n, g) ↦ n · ι(g)`. -/
noncomputable def splitHom : relSt I ρ ⋊[relAct ι ρ] SteinbergGroup I B →* SteinbergGroup I A :=
  SemidirectProduct.lift (relSt I ρ).subtype (ringMap ι) fun g => by
    ext n
    change ((MulAut.conjNormal (ringMap ι g) n : relSt I ρ) : SteinbergGroup I A) =
      ringMap ι g * n * (ringMap ι g)⁻¹
    exact MulAut.conjNormal_apply _ _

theorem splitHom_mk (n : relSt I ρ) (g : SteinbergGroup I B) :
    splitHom ι ρ ⟨n, g⟩ = n * ringMap ι g :=
  rfl

include hρι in
theorem splitHom_injective : Function.Injective (splitHom (I := I) ι ρ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨n, g⟩ h
  have h' : (n : SteinbergGroup I A) * ringMap ι g = 1 := h
  have hn : ringMap ρ (n : SteinbergGroup I A) = 1 := mem_relSt.mp n.2
  have hg : g = 1 := by
    have h2 := congrArg (ringMap (I := I) ρ) h'
    rwa [map_mul, hn, one_mul, ringMap_leftInverse ι ρ hρι, map_one] at h2
  subst hg
  rw [map_one, mul_one] at h'
  have hn1 : n = 1 := Subtype.ext h'
  subst hn1
  rfl

#audit_axioms splitHom_injective

include hρι in
theorem splitHom_surjective : Function.Surjective (splitHom (I := I) ι ρ) := by
  intro a
  refine ⟨⟨⟨a * (ringMap ι (ringMap ρ a))⁻¹, ?_⟩, ringMap ρ a⟩, ?_⟩
  · rw [mem_relSt, map_mul, map_inv, ringMap_leftInverse ι ρ hρι, mul_inv_cancel]
  · change a * (ringMap ι (ringMap ρ a))⁻¹ * ringMap ι (ringMap ρ a) = a
    exact inv_mul_cancel_right a _

#audit_axioms splitHom_surjective

include hρι in
/-- **Retraction splitting** (Tulenbaev Prop. 1.6, kernel form; F.3). For ring homomorphisms
`ι : B → A`, `ρ : A → B` with `ρ ∘ ι = id`, `St_I(A) ≅ relSt ρ ⋊ St_I(B)`. -/
noncomputable def splitEquiv :
    relSt I ρ ⋊[relAct ι ρ] SteinbergGroup I B ≃* SteinbergGroup I A :=
  MulEquiv.ofBijective (splitHom ι ρ) ⟨splitHom_injective ι ρ hρι, splitHom_surjective ι ρ hρι⟩

include hρι in
/-- For a retraction, the relative group is the normal closure of its relative roots. -/
theorem relSt_eq_normalClosure_of_leftInverse : relSt I ρ = relNC I ρ :=
  relSt_eq_normalClosure ρ hρι.surjective

#audit_axioms relSt_eq_normalClosure_of_leftInverse

end Retraction

section Polynomial

variable (I : Type*) [Fintype I] [DecidableEq I] (A : Type*) [CommRing A]

/-- **The polynomial relative group** `𝔑_I(A[X]) = ker (ev₀ : St_I(A[X]) → St_I(A))`. -/
noncomputable abbrev polyRelSt : Subgroup (SteinbergGroup I (Polynomial A)) :=
  relSt I (Polynomial.evalRingHom (0 : A))

theorem evalRingHom_zero_leftInverse_C :
    Function.LeftInverse (Polynomial.evalRingHom (0 : A)) (Polynomial.C : A →+* Polynomial A) :=
  fun a => by simp

set_option maxHeartbeats 800000 in
/-- `St_I(A[X]) ≅ 𝔑_I(A[X]) ⋊ St_I(A)`, split by the constants. -/
noncomputable def polySplitEquiv :
    relSt I (Polynomial.evalRingHom (0 : A)) ⋊[relAct (Polynomial.C : A →+* Polynomial A)
      (Polynomial.evalRingHom (0 : A))] SteinbergGroup I A ≃* SteinbergGroup I (Polynomial A) :=
  splitEquiv (Polynomial.C : A →+* Polynomial A) (Polynomial.evalRingHom (0 : A))
    (evalRingHom_zero_leftInverse_C A)

set_option maxHeartbeats 800000 in
/-- `𝔑_I(A[X])` is the normal closure of the `x_ij(p)` with `p(0) = 0`. -/
theorem polyRelSt_eq_normalClosure :
    polyRelSt I A = relNC I (Polynomial.evalRingHom (0 : A)) :=
  relSt_eq_normalClosure_of_leftInverse (Polynomial.C : A →+* Polynomial A)
    (Polynomial.evalRingHom (0 : A)) (evalRingHom_zero_leftInverse_C A)

#audit_axioms polyRelSt_eq_normalClosure

end Polynomial

end K2Found
end BooneHigmanLinear
end GroupApproximation
