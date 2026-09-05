import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The two pieces of algebra that Leray–Hirsch runs on

The Leray–Hirsch theorem for a projective bundle `P(E) → X` is proved by
induction over a finite trivializing cover of the base.  Stripped of all
topology, the induction step and its conclusion are two statements about
modules, and this file proves both once.

## The induction step: a five lemma in element form

Write `Φ_U : ⨁_{i<r} H^{*-2i}(U) → H^*(P(E)|_U)`, `(a_i) ↦ ∑ π^*a_i ⌣ ξ^i`.
Restriction along `U ∩ V ⊆ U ⊆ U ∪ V` makes `Φ` a map from the (direct sum of
shifted) Mayer–Vietoris sequences of the base to the Mayer–Vietoris sequence of
the total space; the squares commute because restriction is a ring map and
because the connecting map is linear over classes pulled back from the base.
Knowing `Φ` on `U`, `V` and `U ∩ V` therefore gives `Φ` on `U ∪ V` by the five
lemma.  Mathlib (pin `81a5d257`) has no five lemma, so `bijective_of_ladder`
below is a self-contained element-level diagram chase for additive groups.

## The conclusion: a `PowerBasis`

Leray–Hirsch says that `1, ξ, …, ξ^{r-1}` is a basis, i.e. that
`c ↦ ∑ c i • ξ^i` is bijective.  `powerBasisOfBijective` repackages exactly that
hypothesis as a `Mathlib` `PowerBasis`, which is the input of
`CharClass/ChernRelation.lean`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

section FiveLemma

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}
variable [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄]
variable [AddCommGroup A₅] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
variable [AddCommGroup B₄] [AddCommGroup B₅]

/-- **The five lemma, in element form.**

Two exact rows, a commuting ladder of additive maps, the outer four vertical maps
respectively surjective, bijective, bijective, injective: then the middle one is
bijective.  Exactness of a row at a spot is stated as
`g x = 0 ↔ x ∈ range f`, which is the form the Mayer–Vietoris sequence delivers. -/
theorem bijective_of_ladder
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄) (g₄ : B₄ →+ B₅)
    (φ₁ : A₁ →+ B₁) (φ₂ : A₂ →+ B₂) (φ₃ : A₃ →+ B₃) (φ₄ : A₄ →+ B₄) (φ₅ : A₅ →+ B₅)
    (sq₁ : ∀ a, φ₂ (f₁ a) = g₁ (φ₁ a))
    (sq₂ : ∀ a, φ₃ (f₂ a) = g₂ (φ₂ a))
    (sq₃ : ∀ a, φ₄ (f₃ a) = g₃ (φ₃ a))
    (sq₄ : ∀ a, φ₅ (f₄ a) = g₄ (φ₄ a))
    (exA₂ : ∀ x, f₂ x = 0 ↔ ∃ y, f₁ y = x)
    (exA₃ : ∀ x, f₃ x = 0 ↔ ∃ y, f₂ y = x)
    (exA₄ : ∀ x, f₄ x = 0 ↔ ∃ y, f₃ y = x)
    (exB₂ : ∀ x, g₂ x = 0 ↔ ∃ y, g₁ y = x)
    (exB₃ : ∀ x, g₃ x = 0 ↔ ∃ y, g₂ y = x)
    (exB₄ : ∀ x, g₄ x = 0 ↔ ∃ y, g₃ y = x)
    (h₁ : Function.Surjective φ₁) (h₂ : Function.Bijective φ₂)
    (h₄ : Function.Bijective φ₄) (h₅ : Function.Injective φ₅) :
    Function.Bijective φ₃ := by
  constructor
  · have key : ∀ x : A₃, φ₃ x = 0 → x = 0 := by
      intro x hx
      have hfx : f₃ x = 0 := by
        refine h₄.1 ?_
        rw [sq₃, hx]
        simp
      obtain ⟨a₂, ha₂⟩ := (exA₃ x).mp hfx
      have hker : g₂ (φ₂ a₂) = 0 := by rw [← sq₂, ha₂, hx]
      obtain ⟨b₁, hb₁⟩ := (exB₂ (φ₂ a₂)).mp hker
      obtain ⟨a₁, rfl⟩ := h₁ b₁
      have ha₁ : f₁ a₁ = a₂ := h₂.1 (by rw [sq₁, hb₁])
      rw [← ha₂, ← ha₁]
      exact (exA₂ (f₁ a₁)).mpr ⟨a₁, rfl⟩
    intro a a' haa
    have := key (a - a') (by rw [map_sub, haa, sub_self])
    exact sub_eq_zero.mp this
  · intro b₃
    obtain ⟨a₄, ha₄⟩ := h₄.2 (g₃ b₃)
    have hz : g₄ (g₃ b₃) = 0 := (exB₄ (g₃ b₃)).mpr ⟨b₃, rfl⟩
    have h5 : f₄ a₄ = 0 := by
      refine h₅ ?_
      rw [sq₄, ha₄, hz]
      simp
    obtain ⟨a₃, ha₃⟩ := (exA₄ a₄).mp h5
    have hdiff : g₃ (b₃ - φ₃ a₃) = 0 := by
      rw [map_sub, ← sq₃, ha₃, ha₄, sub_self]
    obtain ⟨b₂, hb₂⟩ := (exB₃ (b₃ - φ₃ a₃)).mp hdiff
    obtain ⟨a₂, rfl⟩ := h₂.2 b₂
    refine ⟨a₃ + f₂ a₂, ?_⟩
    rw [map_add, sq₂, hb₂]
    abel

end FiveLemma

section PowerBasis

open Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Leray–Hirsch, repackaged.**  If `c ↦ ∑_{i<r} c i • ξ^i` is a bijection
`(Fin r → A) → B`, then `1, ξ, …, ξ^{r-1}` is an `A`-basis of `B`, i.e. `ξ`
generates a `PowerBasis` of dimension `r`.  This is the hypothesis that the
Mayer–Vietoris induction produces and the input that the Chern relation of
`CharClass/ChernRelation.lean` consumes. -/
noncomputable def powerBasisOfBijective (ξ : B) (r : ℕ)
    (L : (Fin r → A) →ₗ[A] B) (hL : ∀ c : Fin r → A, L c = ∑ i : Fin r, c i • ξ ^ (i : ℕ))
    (hbij : Function.Bijective L) : PowerBasis A B where
  gen := ξ
  dim := r
  basis := Basis.ofEquivFun (LinearEquiv.ofBijective L hbij).symm
  basis_eq_pow := by
    intro i
    rw [Basis.coe_ofEquivFun]
    show ((LinearEquiv.ofBijective L hbij).symm.symm) (Pi.single i 1) = ξ ^ (i : ℕ)
    rw [LinearEquiv.symm_symm]
    show L (Pi.single i 1) = ξ ^ (i : ℕ)
    rw [hL]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- **Leray–Hirsch, repackaged, unbundled.**  The same statement as
`powerBasisOfBijective` but taking the bijectivity of the plain function
`c ↦ ∑ cᵢ ξ^i`, so that a caller with a non-canonical `Algebra` instance does not
have to bundle a `LinearMap` whose very type mentions that instance. -/
noncomputable def powerBasisOfBijective' (ξ : B) (r : ℕ)
    (hbij : Function.Bijective (fun c : Fin r → A => ∑ i : Fin r, c i • ξ ^ (i : ℕ))) :
    PowerBasis A B :=
  powerBasisOfBijective ξ r
    { toFun := fun c => ∑ i : Fin r, c i • ξ ^ (i : ℕ)
      map_add' := fun c c' => by
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := fun s c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
    (fun _ => rfl) hbij

@[simp]
theorem powerBasisOfBijective'_gen (ξ : B) (r : ℕ)
    (hbij : Function.Bijective (fun c : Fin r → A => ∑ i : Fin r, c i • ξ ^ (i : ℕ))) :
    (powerBasisOfBijective' ξ r hbij).gen = ξ := rfl

@[simp]
theorem powerBasisOfBijective'_dim (ξ : B) (r : ℕ)
    (hbij : Function.Bijective (fun c : Fin r → A => ∑ i : Fin r, c i • ξ ^ (i : ℕ))) :
    (powerBasisOfBijective' ξ r hbij).dim = r := rfl

@[simp]
theorem powerBasisOfBijective_gen (ξ : B) (r : ℕ)
    (L : (Fin r → A) →ₗ[A] B) (hL : ∀ c : Fin r → A, L c = ∑ i : Fin r, c i • ξ ^ (i : ℕ))
    (hbij : Function.Bijective L) :
    (powerBasisOfBijective ξ r L hL hbij).gen = ξ := rfl

@[simp]
theorem powerBasisOfBijective_dim (ξ : B) (r : ℕ)
    (L : (Fin r → A) →ₗ[A] B) (hL : ∀ c : Fin r → A, L c = ∑ i : Fin r, c i • ξ ^ (i : ℕ))
    (hbij : Function.Bijective L) :
    (powerBasisOfBijective ξ r L hL hbij).dim = r := rfl

end PowerBasis

end CharClass
end GroupApproximation
