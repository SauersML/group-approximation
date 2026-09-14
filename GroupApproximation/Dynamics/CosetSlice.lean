import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Canonical extension along coset slices

For a group homomorphism `f : H →* K`, a configuration on `K × G` restricts
at `k : K` to `h,t ↦ y (k * f h,t)`. An equivariant map on `H × G` therefore
extends canonically to `K × G`. Taking `f` to be a subgroup inclusion gives
the usual operation on left cosets. The construction needs neither a choice
of representatives nor finiteness. Its composition law supplies the nested
slice identity used in finitary split-extension surjunctivity.
-/

namespace GroupApproximation.Surjunctivity

universe uH uK uJ uG uB

variable {H : Type uH} {K : Type uK} {J : Type uJ}
  {G : Type uG} {B : Type uB} [Group H] [Group K] [Group J]

/-- Precomposition by left multiplication on the fiber coordinate. -/
def fiberTranslate (a : H) (y : H × G → B) : H × G → B :=
  fun p ↦ y (a * p.1, p.2)

/-- Commutation with all translations of the fiber coordinate. -/
def FiberEquivariant (φ : (H × G → B) → (H × G → B)) : Prop :=
  ∀ (a : H) (y : H × G → B),
    φ (fiberTranslate a y) = fiberTranslate a (φ y)

/-- The configuration pulled back to the slice based at `k`. -/
def cosetSlice (f : H →* K) (k : K) (y : K × G → B) : H × G → B :=
  fun p ↦ y (k * f p.1, p.2)

/-- Extension by applying a map to the slice based at the output coordinate. -/
def cosetExtension (f : H →* K) (φ : (H × G → B) → (H × G → B))
    (y : K × G → B) : K × G → B :=
  fun p ↦ φ (cosetSlice f p.1 y) (1, p.2)

theorem cosetSlice_mul (f : H →* K) (k : K) (h : H) (y : K × G → B) :
    cosetSlice f (k * f h) y = fiberTranslate h (cosetSlice f k y) := by
  funext p
  simp only [cosetSlice, fiberTranslate, map_mul, mul_assoc]

/-- Restriction to a whole slice agrees with the original equivariant map. -/
theorem cosetSlice_extension (f : H →* K)
    {φ : (H × G → B) → (H × G → B)} (hφ : FiberEquivariant φ)
    (k : K) (y : K × G → B) :
    cosetSlice f k (cosetExtension f φ y) = φ (cosetSlice f k y) := by
  funext p
  change φ (cosetSlice f (k * f p.1) y) (1, p.2) = _
  rw [cosetSlice_mul, hφ]
  simp only [fiberTranslate, mul_one]

/-- The extended map commutes with every translation in the ambient fiber. -/
theorem cosetExtension_equivariant (f : H →* K)
    (φ : (H × G → B) → (H × G → B)) :
    FiberEquivariant (cosetExtension f φ) := by
  intro a y
  funext p
  change φ (cosetSlice f p.1 (fiberTranslate a y)) (1, p.2) =
    φ (cosetSlice f (a * p.1) y) (1, p.2)
  congr 1
  funext q
  simp only [cosetSlice, fiberTranslate, mul_assoc]

@[simp] theorem cosetExtension_id (f : H →* K) :
    cosetExtension f (id : (H × G → B) → (H × G → B)) = id := by
  funext y p
  simp only [cosetExtension, cosetSlice, id_eq, map_one, mul_one]

/-- Extension preserves composition when the inner map is equivariant. -/
theorem cosetExtension_comp (f : H →* K)
    (φ ψ : (H × G → B) → (H × G → B)) (hψ : FiberEquivariant ψ) :
    cosetExtension f (φ ∘ ψ) = cosetExtension f φ ∘ cosetExtension f ψ := by
  funext y p
  change φ (ψ (cosetSlice f p.1 y)) (1, p.2) =
    φ (cosetSlice f p.1 (cosetExtension f ψ y)) (1, p.2)
  rw [cosetSlice_extension f hψ]

/-- An injective equivariant map remains injective on the ambient fibers. -/
theorem cosetExtension_injective (f : H →* K)
    {φ : (H × G → B) → (H × G → B)} (heq : FiberEquivariant φ)
    (hinj : Function.Injective φ) : Function.Injective (cosetExtension f φ) := by
  intro y z hyz
  funext p
  have hs : cosetSlice f p.1 y = cosetSlice f p.1 z := by
    apply hinj
    rw [← cosetSlice_extension f heq, ← cosetSlice_extension f heq, hyz]
  have h := congrFun hs (1, p.2)
  simpa only [cosetSlice, map_one, mul_one] using h

/-- Extension preserves a specified left inverse. -/
theorem cosetExtension_leftInverse (f : H →* K)
    {φ ψ : (H × G → B) → (H × G → B)} (hφ : FiberEquivariant φ)
    (hleft : Function.LeftInverse ψ φ) :
    Function.LeftInverse (cosetExtension f ψ) (cosetExtension f φ) := by
  intro y
  have hcomp : ψ ∘ φ = id := funext hleft
  have h := cosetExtension_comp f ψ φ hφ
  rw [hcomp, cosetExtension_id] at h
  exact congrFun h.symm y

/-- The inverse of an equivariant bijection is equivariant. -/
theorem fiberEquivariant_symm (e : (H × G → B) ≃ (H × G → B))
    (he : FiberEquivariant e) : FiberEquivariant e.symm := by
  intro a y
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Canonical extension of an equivariant bijection is bijective. -/
theorem cosetExtension_bijective (f : H →* K)
    {φ : (H × G → B) → (H × G → B)} (hφ : FiberEquivariant φ)
    (hbij : Function.Bijective φ) : Function.Bijective (cosetExtension f φ) := by
  let e : (H × G → B) ≃ (H × G → B) := Equiv.ofBijective φ hbij
  have he : FiberEquivariant e := hφ
  have hleft := cosetExtension_leftInverse f he e.symm_apply_apply
  have hright := cosetExtension_leftInverse f (fiberEquivariant_symm e he)
    e.apply_symm_apply
  exact ⟨hleft.injective, hright.surjective⟩

/-- Nested extension is extension along the composite homomorphism. -/
theorem cosetExtension_trans (f : H →* K) (j : J →* H)
    (ψ : (J × G → B) → (J × G → B)) :
    cosetExtension f (cosetExtension j ψ) = cosetExtension (f.comp j) ψ := by
  funext y p
  change ψ (cosetSlice j 1 (cosetSlice f p.1 y)) (1, p.2) =
    ψ (cosetSlice (f.comp j) p.1 y) (1, p.2)
  congr 1
  funext q
  simp only [cosetSlice, one_mul, MonoidHom.comp_apply]

/-- Extension preserves coordinatewise identity outside any base region. -/
theorem cosetExtension_eq_self (f : H →* K)
    {φ : (H × G → B) → (H × G → B)} {R : Set G}
    (hφ : ∀ y h g, g ∉ R → φ y (h, g) = y (h, g))
    (y : K × G → B) (k : K) (g : G) (hg : g ∉ R) :
    cosetExtension f φ y (k, g) = y (k, g) := by
  change φ (cosetSlice f k y) (1, g) = _
  rw [hφ _ _ _ hg]
  simp only [cosetSlice, map_one, mul_one]

end GroupApproximation.Surjunctivity
