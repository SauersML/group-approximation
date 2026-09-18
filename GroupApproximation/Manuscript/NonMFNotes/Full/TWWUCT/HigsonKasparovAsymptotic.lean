import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Asymptotic morphisms (Higson–Kasparov 2001, §2)

This file sets up the basic language of asymptotic morphisms between C⋆-algebras, as used in
the proof of the Baum–Connes conjecture for a-T-menable groups by Higson and Kasparov
(Invent. Math. 144 (2001), §2; after Connes–Higson 1990 and Guentner–Higson–Trout 2000).
This is part of the UCT input for `thm:fixed-radical-membership` in `non_mf_group_notes.tex`.

An asymptotic morphism `φ : A ⇝ B` is a family `φ t : A → B`, `t ∈ ℝ`, continuous in `t` for
fixed `a`, whose defects from being a `*`-homomorphism tend to zero as `t → ∞`.

## Main definitions

* `AsymptoticMorphism A B`: asymptotic morphisms, parametrised by `t ∈ ℝ` (limits at `atTop`).
* `AsymptoticMorphism.ofHom`: a `*`-homomorphism as a constant asymptotic morphism.
* `AsymptoticMorphism.postcomp`, `AsymptoticMorphism.precomp`: composition with
  `*`-homomorphisms on either side.
* `AsymptoticMorphism.reparam`: reparametrisation along a proper continuous map `ℝ → ℝ`.
* `AsymptoticMorphism.AsymptoticallyEquivalent`: asymptotic equivalence, an equivalence relation.
* `AsymptoticMorphism.IsAsymptoticallyEquivariant`: equivariance up to asymptotically vanishing
  error for actions of a discrete group (HK 2001, Definition 2.? / §2 "equivariant asymptotic
  morphisms").
-/

noncomputable section

open Filter Topology
open scoped CStarAlgebra

namespace GroupApproximation.Full.TWWUCT.HigsonKasparov

universe u₁ u₂ u₃ u₄

/-- An asymptotic morphism from `A` to `B` (Higson–Kasparov 2001, §2; Connes–Higson 1990):
a family of maps `toFun t : A → B`, continuous in `t`, which is asymptotically additive,
`ℂ`-homogeneous, multiplicative and `*`-preserving as `t → ∞`. -/
structure AsymptoticMorphism (A : Type u₁) (B : Type u₂) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] where
  /-- The underlying family of maps. -/
  toFun : ℝ → A → B
  continuous_toFun : ∀ a, Continuous fun t => toFun t a
  tendsto_add : ∀ a b,
    Tendsto (fun t => toFun t (a + b) - (toFun t a + toFun t b)) atTop (𝓝 0)
  tendsto_smul : ∀ (z : ℂ) (a : A),
    Tendsto (fun t => toFun t (z • a) - z • toFun t a) atTop (𝓝 0)
  tendsto_mul : ∀ a b,
    Tendsto (fun t => toFun t (a * b) - toFun t a * toFun t b) atTop (𝓝 0)
  tendsto_star : ∀ a,
    Tendsto (fun t => toFun t (star a) - star (toFun t a)) atTop (𝓝 0)

namespace AsymptoticMorphism

variable {A : Type u₁} {B : Type u₂} {D : Type u₃} {E : Type u₄}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
variable [NonUnitalCStarAlgebra E]

/-- A function that vanishes identically tends to zero. -/
theorem tendsto_zero_of_forall_eq_zero {X : Type*} [TopologicalSpace X] [Zero X]
    {f : ℝ → X} (h : ∀ t, f t = 0) : Tendsto f atTop (𝓝 0) :=
  (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : X)) atTop (𝓝 0)).congr fun t => (h t).symm

/-- A `*`-homomorphism of C⋆-algebras preserves convergence to zero (it is continuous,
being contractive). -/
theorem tendsto_map_zero (ψ : B →⋆ₙₐ[ℂ] D) {f : ℝ → B} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun t => ψ (f t)) atTop (𝓝 0) := by
  have h := ((map_continuous ψ).tendsto 0).comp hf
  rw [map_zero] at h
  exact h

/-! ### `*`-homomorphisms and composition -/

/-- A `*`-homomorphism, viewed as a constant asymptotic morphism. -/
def ofHom (π : A →⋆ₙₐ[ℂ] B) : AsymptoticMorphism A B where
  toFun _ a := π a
  continuous_toFun a := show Continuous fun _ : ℝ => π a from continuous_const
  tendsto_add a b := tendsto_zero_of_forall_eq_zero fun _ =>
    show π (a + b) - (π a + π b) = 0 from sub_eq_zero.mpr (map_add π a b)
  tendsto_smul z a := tendsto_zero_of_forall_eq_zero fun _ =>
    show π (z • a) - z • π a = 0 from sub_eq_zero.mpr (map_smul π z a)
  tendsto_mul a b := tendsto_zero_of_forall_eq_zero fun _ =>
    show π (a * b) - π a * π b = 0 from sub_eq_zero.mpr (map_mul π a b)
  tendsto_star a := tendsto_zero_of_forall_eq_zero fun _ =>
    show π (star a) - star (π a) = 0 from sub_eq_zero.mpr (map_star π a)

theorem ofHom_toFun (π : A →⋆ₙₐ[ℂ] B) (t : ℝ) (a : A) : (ofHom π).toFun t a = π a := rfl

/-- Post-composition of an asymptotic morphism with a `*`-homomorphism. -/
def postcomp (ψ : B →⋆ₙₐ[ℂ] D) (φ : AsymptoticMorphism A B) : AsymptoticMorphism A D where
  toFun t a := ψ (φ.toFun t a)
  continuous_toFun a := show Continuous fun t => ψ (φ.toFun t a) from
    (map_continuous ψ).comp (φ.continuous_toFun a)
  tendsto_add a b := (tendsto_map_zero ψ (φ.tendsto_add a b)).congr fun _ => by
    simp only [map_sub, map_add]
  tendsto_smul z a := (tendsto_map_zero ψ (φ.tendsto_smul z a)).congr fun _ => by
    simp only [map_sub, map_smul]
  tendsto_mul a b := (tendsto_map_zero ψ (φ.tendsto_mul a b)).congr fun _ => by
    simp only [map_sub, map_mul]
  tendsto_star a := (tendsto_map_zero ψ (φ.tendsto_star a)).congr fun _ => by
    simp only [map_sub, map_star]

theorem postcomp_toFun (ψ : B →⋆ₙₐ[ℂ] D) (φ : AsymptoticMorphism A B) (t : ℝ) (a : A) :
    (φ.postcomp ψ).toFun t a = ψ (φ.toFun t a) := rfl

/-- Pre-composition of an asymptotic morphism with a `*`-homomorphism. -/
def precomp (φ : AsymptoticMorphism B D) (π : A →⋆ₙₐ[ℂ] B) : AsymptoticMorphism A D where
  toFun t a := φ.toFun t (π a)
  continuous_toFun a := φ.continuous_toFun (π a)
  tendsto_add a b := by
    show Tendsto (fun t => φ.toFun t (π (a + b)) - (φ.toFun t (π a) + φ.toFun t (π b)))
      atTop (𝓝 0)
    rw [map_add π]
    exact φ.tendsto_add (π a) (π b)
  tendsto_smul z a := by
    show Tendsto (fun t => φ.toFun t (π (z • a)) - z • φ.toFun t (π a)) atTop (𝓝 0)
    rw [map_smul π]
    exact φ.tendsto_smul z (π a)
  tendsto_mul a b := by
    show Tendsto (fun t => φ.toFun t (π (a * b)) - φ.toFun t (π a) * φ.toFun t (π b))
      atTop (𝓝 0)
    rw [map_mul π]
    exact φ.tendsto_mul (π a) (π b)
  tendsto_star a := by
    show Tendsto (fun t => φ.toFun t (π (star a)) - star (φ.toFun t (π a))) atTop (𝓝 0)
    rw [map_star π]
    exact φ.tendsto_star (π a)

theorem precomp_toFun (φ : AsymptoticMorphism B D) (π : A →⋆ₙₐ[ℂ] B) (t : ℝ) (a : A) :
    (φ.precomp π).toFun t a = φ.toFun t (π a) := rfl

theorem postcomp_ofHom (ψ : B →⋆ₙₐ[ℂ] D) (π : A →⋆ₙₐ[ℂ] B) :
    (ofHom π).postcomp ψ = ofHom (ψ.comp π) := rfl

theorem precomp_ofHom (ψ : B →⋆ₙₐ[ℂ] D) (π : A →⋆ₙₐ[ℂ] B) :
    (ofHom ψ).precomp π = ofHom (ψ.comp π) := rfl

/-- Reparametrisation of an asymptotic morphism along a continuous map `r : ℝ → ℝ` with
`r t → ∞` (HK 2001, §2: asymptotic morphisms are only relevant up to such changes). -/
def reparam (φ : AsymptoticMorphism A B) (r : ℝ → ℝ) (hr : Continuous r)
    (hr' : Tendsto r atTop atTop) : AsymptoticMorphism A B where
  toFun t := φ.toFun (r t)
  continuous_toFun a := (φ.continuous_toFun a).comp hr
  tendsto_add a b := (φ.tendsto_add a b).comp hr'
  tendsto_smul z a := (φ.tendsto_smul z a).comp hr'
  tendsto_mul a b := (φ.tendsto_mul a b).comp hr'
  tendsto_star a := (φ.tendsto_star a).comp hr'

theorem reparam_toFun (φ : AsymptoticMorphism A B) (r : ℝ → ℝ) (hr : Continuous r)
    (hr' : Tendsto r atTop atTop) (t : ℝ) (a : A) :
    (φ.reparam r hr hr').toFun t a = φ.toFun (r t) a := rfl

/-! ### Asymptotic equivalence -/

/-- Two asymptotic morphisms are asymptotically equivalent if their difference tends to zero
pointwise (HK 2001, §2). -/
def AsymptoticallyEquivalent (φ ψ : AsymptoticMorphism A B) : Prop :=
  ∀ a, Tendsto (fun t => φ.toFun t a - ψ.toFun t a) atTop (𝓝 0)

namespace AsymptoticallyEquivalent

theorem refl (φ : AsymptoticMorphism A B) : AsymptoticallyEquivalent φ φ := fun a =>
  tendsto_zero_of_forall_eq_zero fun t => sub_self (φ.toFun t a)

theorem symm {φ ψ : AsymptoticMorphism A B} (h : AsymptoticallyEquivalent φ ψ) :
    AsymptoticallyEquivalent ψ φ := by
  intro a
  have h' := (h a).neg
  rw [neg_zero] at h'
  exact h'.congr fun t => neg_sub (φ.toFun t a) (ψ.toFun t a)

theorem trans {φ ψ χ : AsymptoticMorphism A B} (h₁ : AsymptoticallyEquivalent φ ψ)
    (h₂ : AsymptoticallyEquivalent ψ χ) : AsymptoticallyEquivalent φ χ := by
  intro a
  have h := (h₁ a).add (h₂ a)
  rw [add_zero] at h
  exact h.congr fun t => sub_add_sub_cancel (φ.toFun t a) (ψ.toFun t a) (χ.toFun t a)

theorem postcomp (ψ : B →⋆ₙₐ[ℂ] D) {φ φ' : AsymptoticMorphism A B}
    (h : AsymptoticallyEquivalent φ φ') :
    AsymptoticallyEquivalent (φ.postcomp ψ) (φ'.postcomp ψ) := by
  intro a
  exact (tendsto_map_zero ψ (h a)).congr fun t => map_sub ψ (φ.toFun t a) (φ'.toFun t a)

theorem precomp (π : A →⋆ₙₐ[ℂ] B) {φ φ' : AsymptoticMorphism B D}
    (h : AsymptoticallyEquivalent φ φ') :
    AsymptoticallyEquivalent (φ.precomp π) (φ'.precomp π) := fun a => h (π a)

end AsymptoticallyEquivalent

/-- Asymptotic equivalence as a setoid on asymptotic morphisms. -/
def asymptoticSetoid (A : Type u₁) (B : Type u₂) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] : Setoid (AsymptoticMorphism A B) where
  r := AsymptoticallyEquivalent
  iseqv := ⟨AsymptoticallyEquivalent.refl, AsymptoticallyEquivalent.symm,
    AsymptoticallyEquivalent.trans⟩

/-! ### Equivariance for discrete groups -/

section Equivariant

variable {G : Type*} [Group G]

/-- An asymptotic morphism is asymptotically equivariant for actions `α` of `G` on `A` and `β`
on `B` if `φ t (α g a) - β g (φ t a) → 0` for every `g` and `a` (HK 2001, §2, equivariant
asymptotic morphisms for a discrete group `G`). -/
def IsAsymptoticallyEquivariant (α : G →* (A ≃⋆ₐ[ℂ] A)) (β : G →* (B ≃⋆ₐ[ℂ] B))
    (φ : AsymptoticMorphism A B) : Prop :=
  ∀ g a, Tendsto (fun t => φ.toFun t (α g a) - β g (φ.toFun t a)) atTop (𝓝 0)

/-- An intertwining `*`-homomorphism is an equivariant asymptotic morphism. -/
theorem isAsymptoticallyEquivariant_ofHom (α : G →* (A ≃⋆ₐ[ℂ] A)) (β : G →* (B ≃⋆ₐ[ℂ] B))
    (π : A →⋆ₙₐ[ℂ] B) (hπ : ∀ g a, π (α g a) = β g (π a)) :
    IsAsymptoticallyEquivariant α β (ofHom π) := fun g a =>
  tendsto_zero_of_forall_eq_zero fun _ =>
    show π (α g a) - β g (π a) = 0 from sub_eq_zero.mpr (hπ g a)

/-- Post-composing an equivariant asymptotic morphism with an intertwining `*`-homomorphism
gives an equivariant asymptotic morphism. -/
theorem IsAsymptoticallyEquivariant.postcomp {α : G →* (A ≃⋆ₐ[ℂ] A)}
    {β : G →* (B ≃⋆ₐ[ℂ] B)} {γ : G →* (D ≃⋆ₐ[ℂ] D)} {φ : AsymptoticMorphism A B}
    (hφ : IsAsymptoticallyEquivariant α β φ) (ψ : B →⋆ₙₐ[ℂ] D)
    (hψ : ∀ g b, ψ (β g b) = γ g (ψ b)) :
    IsAsymptoticallyEquivariant α γ (φ.postcomp ψ) := by
  intro g a
  show Tendsto (fun t => ψ (φ.toFun t (α g a)) - γ g (ψ (φ.toFun t a))) atTop (𝓝 0)
  refine (tendsto_map_zero ψ (hφ g a)).congr fun t => ?_
  show ψ (φ.toFun t (α g a) - β g (φ.toFun t a)) = ψ (φ.toFun t (α g a)) - γ g (ψ (φ.toFun t a))
  rw [map_sub ψ, hψ g]

/-- Pre-composing an equivariant asymptotic morphism with an intertwining `*`-homomorphism
gives an equivariant asymptotic morphism. -/
theorem IsAsymptoticallyEquivariant.precomp {α' : G →* (A ≃⋆ₐ[ℂ] A)}
    {α : G →* (B ≃⋆ₐ[ℂ] B)} {β : G →* (D ≃⋆ₐ[ℂ] D)} {φ : AsymptoticMorphism B D}
    (hφ : IsAsymptoticallyEquivariant α β φ) (π : A →⋆ₙₐ[ℂ] B)
    (hπ : ∀ g a, π (α' g a) = α g (π a)) :
    IsAsymptoticallyEquivariant α' β (φ.precomp π) := by
  intro g a
  show Tendsto (fun t => φ.toFun t (π (α' g a)) - β g (φ.toFun t (π a))) atTop (𝓝 0)
  rw [hπ g a]
  exact hφ g (π a)

/-- Asymptotically equivalent asymptotic morphisms are simultaneously asymptotically
equivariant, provided the target action is by contractions (automatic for `*`-automorphisms of
a C⋆-algebra). -/
theorem IsAsymptoticallyEquivariant.of_equivalent {α : G →* (A ≃⋆ₐ[ℂ] A)}
    {β : G →* (B ≃⋆ₐ[ℂ] B)} {φ ψ : AsymptoticMorphism A B}
    (hφ : IsAsymptoticallyEquivariant α β φ) (h : AsymptoticallyEquivalent φ ψ) :
    IsAsymptoticallyEquivariant α β ψ := by
  intro g a
  have h₁ := (h (α g a)).neg
  have h₂ := tendsto_map_zero (β g : B →⋆ₙₐ[ℂ] B) (h a)
  have h₃ := (h₁.add (hφ g a)).add h₂
  rw [neg_zero, zero_add, add_zero] at h₃
  refine h₃.congr fun t => ?_
  show -(φ.toFun t (α g a) - ψ.toFun t (α g a)) + (φ.toFun t (α g a) - β g (φ.toFun t a)) +
      (β g : B →⋆ₙₐ[ℂ] B) (φ.toFun t a - ψ.toFun t a) = ψ.toFun t (α g a) - β g (ψ.toFun t a)
  rw [map_sub]
  show -(φ.toFun t (α g a) - ψ.toFun t (α g a)) + (φ.toFun t (α g a) - β g (φ.toFun t a)) +
      (β g (φ.toFun t a) - β g (ψ.toFun t a)) = ψ.toFun t (α g a) - β g (ψ.toFun t a)
  abel

end Equivariant

end AsymptoticMorphism

end GroupApproximation.Full.TWWUCT.HigsonKasparov
