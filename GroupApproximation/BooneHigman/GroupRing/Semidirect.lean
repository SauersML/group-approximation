import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Prod

/-!
# The split metabelian group of a group-ring module

Let `Q` be a group, `R` a commutative ring, and `M` a module over the group ring `R[Q]`. Then `Q`
acts on the additive group of `M` by `q · m = q • m`, and the semidirect product
`Affine R Q M = M ⋊ Q` has multiplication `(m, q) (m', q') = (m + q • m', q q')`.

Every finitely generated metabelian group embeds in a group of this shape with `R = ℤ` and `Q`
its abelianization (the Magnus embedding, lane `mb-magnus`). The pieces of a primary decomposition
of `M` then give the factors of the product embedding (lane `mb-primary`). This file supplies the
shared API.

* `affineAction`: `Q →* MulAut (Multiplicative M)`, `q ↦ (m ↦ q • m)`.
* `Affine R Q M`: the semidirect product `Multiplicative M ⋊[affineAction R Q M] Q`.
* `inr_mul_inl_mul_inr_inv`: conjugation by `q` is the module action.
* `affineMap`, `affineMap_injective`: an `R[Q]`-linear map induces a homomorphism, injective
  when the linear map is.
* `affinePi`, `affinePi_injective`: a jointly injective family of linear maps gives an injective
  homomorphism into the product of the affine groups.
* `affineAddRegular_injective`, `eq_one_of_smul_regular`: adding the regular summand `R[Q]`
  embeds `Affine R Q M` into an affine group on which `Q` acts faithfully.
* `derivedSeries_two_eq_bot`: for commutative `Q`, `Affine R Q M` is metabelian.
-/

namespace GroupApproximation
namespace BooneHigman
namespace GroupRing

open SemidirectProduct

noncomputable section

section Action

variable (R : Type*) [CommRing R] (Q : Type*) [Group Q]
variable (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra R Q) M]

/-- Multiplication by a group element, as an additive automorphism of an `R[Q]`-module. -/
def groupRingAddEquiv (q : Q) : M ≃+ M where
  toFun m := MonoidAlgebra.of R Q q • m
  invFun m := MonoidAlgebra.of R Q q⁻¹ • m
  left_inv m := by
    dsimp only
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  right_inv m := by
    dsimp only
    rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  map_add' := smul_add _

@[simp] theorem groupRingAddEquiv_apply (q : Q) (m : M) :
    groupRingAddEquiv R Q M q m = MonoidAlgebra.of R Q q • m := rfl

/-- The action of `Q` on `Multiplicative M` through the group ring. -/
def affineAction : Q →* MulAut (Multiplicative M) where
  toFun q := AddEquiv.toMultiplicative (groupRingAddEquiv R Q M q)
  map_one' := by
    ext m
    show Multiplicative.ofAdd (MonoidAlgebra.of R Q 1 • Multiplicative.toAdd m) = m
    rw [map_one, one_smul, ofAdd_toAdd]
  map_mul' q q' := by
    ext m
    show Multiplicative.ofAdd (MonoidAlgebra.of R Q (q * q') • Multiplicative.toAdd m) =
      Multiplicative.ofAdd (MonoidAlgebra.of R Q q • Multiplicative.toAdd
        (Multiplicative.ofAdd (MonoidAlgebra.of R Q q' • Multiplicative.toAdd m)))
    rw [map_mul, mul_smul, toAdd_ofAdd]

@[simp] theorem affineAction_apply (q : Q) (m : Multiplicative M) :
    affineAction R Q M q m =
      Multiplicative.ofAdd (MonoidAlgebra.of R Q q • Multiplicative.toAdd m) := rfl

/-- The split metabelian group `M ⋊ Q` of an `R[Q]`-module `M`. -/
abbrev Affine := Multiplicative M ⋊[affineAction R Q M] Q

variable {R Q M}

@[simp] theorem toAdd_mul_left (a b : Affine R Q M) :
    Multiplicative.toAdd (a * b).left =
      Multiplicative.toAdd a.left + MonoidAlgebra.of R Q a.right • Multiplicative.toAdd b.left :=
  rfl

/-- Conjugating a translation by `q` applies the module action of `q`. -/
theorem inr_mul_inl_mul_inr_inv (q : Q) (m : M) :
    (inr q * inl (Multiplicative.ofAdd m) * inr q⁻¹ : Affine R Q M) =
      inl (Multiplicative.ofAdd (MonoidAlgebra.of R Q q • m)) := by
  rw [← inl_aut]
  rfl

end Action

section Map

variable {R : Type*} [CommRing R] {Q : Type*} [Group Q]
variable {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra R Q) M]
variable {N : Type*} [AddCommGroup N] [Module (MonoidAlgebra R Q) N]

/-- An `R[Q]`-linear map induces a homomorphism of affine groups. -/
def affineMap (f : M →ₗ[MonoidAlgebra R Q] N) : Affine R Q M →* Affine R Q N :=
  SemidirectProduct.map (AddMonoidHom.toMultiplicative f.toAddMonoidHom) (MonoidHom.id Q)
    (fun q => by
      ext m
      show Multiplicative.ofAdd (f (MonoidAlgebra.of R Q q • Multiplicative.toAdd m)) =
        Multiplicative.ofAdd (MonoidAlgebra.of R Q q • f (Multiplicative.toAdd m))
      rw [map_smul])

@[simp] theorem affineMap_left (f : M →ₗ[MonoidAlgebra R Q] N) (x : Affine R Q M) :
    (affineMap f x).left = Multiplicative.ofAdd (f (Multiplicative.toAdd x.left)) := rfl

@[simp] theorem affineMap_right (f : M →ₗ[MonoidAlgebra R Q] N) (x : Affine R Q M) :
    (affineMap f x).right = x.right := rfl

/-- An injective linear map induces an injective homomorphism of affine groups. -/
theorem affineMap_injective {f : M →ₗ[MonoidAlgebra R Q] N} (hf : Function.Injective f) :
    Function.Injective (affineMap f) := by
  intro x y hxy
  have hl := congrArg SemidirectProduct.left hxy
  have hr := congrArg SemidirectProduct.right hxy
  simp only [affineMap_left, affineMap_right] at hl hr
  ext
  · exact Multiplicative.toAdd.injective (hf (Multiplicative.ofAdd.injective hl))
  · exact hr

end Map

section Pi

variable {R : Type*} [CommRing R] {Q : Type*} [Group Q]
variable {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra R Q) M]
variable {ι : Type*} {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module (MonoidAlgebra R Q) (N i)]

/-- A family of `R[Q]`-linear maps induces a homomorphism into the product of affine groups. -/
def affinePi (f : ∀ i, M →ₗ[MonoidAlgebra R Q] N i) : Affine R Q M →* ∀ i, Affine R Q (N i) :=
  MonoidHom.pi fun i => affineMap (f i)

@[simp] theorem affinePi_apply (f : ∀ i, M →ₗ[MonoidAlgebra R Q] N i) (x : Affine R Q M)
    (i : ι) : affinePi f x i = affineMap (f i) x := rfl

/-- **Product embedding.** If the linear maps `f i` are jointly injective and there is at least one
of them, the induced homomorphism into the product of affine groups is injective. -/
theorem affinePi_injective [Nonempty ι] {f : ∀ i, M →ₗ[MonoidAlgebra R Q] N i}
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0) : Function.Injective (affinePi f) := by
  intro x y hxy
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hr : x.right = y.right := by
    have h := congrArg (fun z => (z i₀).right) hxy
    simp only [affinePi_apply, affineMap_right] at h
    exact h
  have hl : ∀ i, f i (Multiplicative.toAdd x.left) = f i (Multiplicative.toAdd y.left) := by
    intro i
    have h := congrArg (fun z => (z i).left) hxy
    simp only [affinePi_apply, affineMap_left] at h
    exact Multiplicative.ofAdd.injective h
  have hsub : Multiplicative.toAdd x.left - Multiplicative.toAdd y.left = 0 :=
    hf _ fun i => by rw [map_sub, hl i, sub_self]
  ext
  · exact Multiplicative.toAdd.injective (sub_eq_zero.mp hsub)
  · exact hr

end Pi

section Regular

variable (R : Type*) [CommRing R] (Q : Type*) [Group Q]
variable (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra R Q) M]

/-- Adding the regular summand `R[Q]`. -/
def affineAddRegular : Affine R Q M →* Affine R Q (M × MonoidAlgebra R Q) :=
  affineMap (LinearMap.inl (MonoidAlgebra R Q) M (MonoidAlgebra R Q))

theorem affineAddRegular_injective : Function.Injective (affineAddRegular R Q M) :=
  affineMap_injective LinearMap.inl_injective

variable {R Q M}

/-- `Q` acts faithfully on `M × R[Q]`: an element acting trivially is the identity. -/
theorem eq_one_of_smul_regular [Nontrivial R] {q : Q}
    (hq : ∀ x : M × MonoidAlgebra R Q, MonoidAlgebra.of R Q q • x = x) : q = 1 := by
  have h : (MonoidAlgebra.of R Q q • ((0 : M), (1 : MonoidAlgebra R Q))).2 = 1 :=
    congrArg Prod.snd (hq (0, 1))
  rw [Prod.smul_snd, smul_eq_mul, mul_one] at h
  exact MonoidAlgebra.of_injective (h.trans (map_one (MonoidAlgebra.of R Q)).symm)

end Regular

section Metabelian

variable (R : Type*) [CommRing R] (Q : Type*) [CommGroup Q]
variable (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra R Q) M]

/-- For commutative `Q`, every commutator of `Affine R Q M` is a translation. -/
theorem commutator_le_range_inl :
    commutator (Affine R Q M) ≤ (inl : Multiplicative M →* Affine R Q M).range := by
  rw [range_inl_eq_ker_rightHom]
  show ⁅(⊤ : Subgroup (Affine R Q M)), ⊤⁆ ≤ _
  rw [Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

/-- **`Affine R Q M` is metabelian** when `Q` is commutative. -/
theorem derivedSeries_two_eq_bot : derivedSeries (Affine R Q M) 2 = ⊥ := by
  show derivedSeries (Affine R Q M) (1 + 1) = ⊥
  rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff]
  refine (Subgroup.commutator_mono (commutator_le_range_inl R Q M)
    (commutator_le_range_inl R Q M)).trans ?_
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [MonoidHom.mem_range] at hg₁ hg₂
  obtain ⟨a, rfl⟩ := hg₁
  obtain ⟨b, rfl⟩ := hg₂
  have hc : (inl a : Affine R Q M) * inl b = inl b * inl a := by
    rw [← map_mul, ← map_mul, mul_comm a b]
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact Subgroup.one_mem _

end Metabelian

end

end GroupRing
end BooneHigman
end GroupApproximation
