import GroupApproximation.Analysis.CStarSeminormQuotient
import GroupApproximation.Analysis.CStarSeminormCompletion

/-!
# The enveloping C⋆-algebra of a ⋆-algebra with norm-bounded relations

Let `A` be a complex ⋆-algebra.  A *norm-bounded relation* on `A` is a pair `(a, c)` with
`a : A` and `c : ℝ≥0`, standing for `‖a‖ ≤ c`.  The relation `a = 0` is the pair `(a, 0)`.  A
*representation* of `(A, P)` (`EnvRep A P`) is a unital ⋆-homomorphism `π` from `A` into a
unital C⋆-algebra with `‖π a‖ ≤ c` for every `(a, c) ∈ P`.  Suppose every element of `A` is
norm-bounded over all representations (`IsBounded P`).  Then `‖a‖_P = sup_π ‖π a‖` is a
C⋆-seminorm, and completing `A` for it gives the *enveloping C⋆-algebra* `Envelope P hP`.

The supremum ranges over representations into algebras in the universe of `A`.  The universal
property still holds for targets in every universe: a representation `f : A → B` factors
through the completion of its own image seminorm, which lives in the universe of `A`
(`shrinkRep`).

## Main results

- `norm_envHom_rel`: the canonical map `envHom` satisfies the relations.  `envHom_rel`: it kills
  the relations with bound `0`.
- `envLift`, `envLift_envHom`, `envHom_ext`, `existsUnique_envLift`: the universal property, for
  targets in every universe.
- `isBounded_of_adjoin`: boundedness only has to be checked on a generating set.
- `isBoundedElem_of_mem`: an element with a norm bound in `P` is bounded.
- `isBoundedElem_of_idem`, `isBoundedElem_of_isometry_rel`, `isBoundedElem_of_idem_rel`: an
  element `a` with `star a * a` idempotent in every representation is bounded by `1`.  This
  covers projections, isometries, unitaries and partial isometries.

## References

- Blackadar, *Operator Algebras*, II.8.3.
- Loring, *Lifting Solutions to Perturbing Problems in C⋆-Algebras*, Ch. 3.
-/

namespace GroupApproximation
namespace CStarLimits

open CStarTensor
open scoped NNReal

noncomputable section

universe u v

variable (A : Type u) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- A representation of `A` satisfying the norm-bounded relations `P`, into a unital C⋆-algebra
in the universe of `A`. -/
structure EnvRep (P : Set (A × ℝ≥0)) : Type (u+1) where
  /-- The target C⋆-algebra. -/
  carrier : Type u
  /-- Its C⋆-structure. -/
  [cstar : CStarAlgebra carrier]
  /-- The representation. -/
  hom : A →⋆ₐ[ℂ] carrier
  /-- The relations hold. -/
  map_rel : ∀ p : A × ℝ≥0, p ∈ P → ‖hom p.1‖ ≤ p.2

attribute [instance] EnvRep.cstar

variable {A}

omit [StarModule ℂ A] in
/-- The zero function is a C⋆-seminorm. -/
theorem isCStarSeminorm_zero : IsCStarSeminorm (fun _ : A ↦ (0 : ℝ)) where
  nonneg _ := le_rfl
  add_le _ _ := le_of_eq (add_zero (0 : ℝ)).symm
  smul c _ := (mul_zero ‖c‖).symm
  mul_le _ _ := le_of_eq (mul_zero (0 : ℝ)).symm
  cstar _ := (mul_zero (0 : ℝ)).symm

/-- The zero representation, into the completion of `A` for the zero seminorm.  It shows that
there is at least one representation. -/
def zeroRep (P : Set (A × ℝ≥0)) : EnvRep A P where
  carrier := SeminormCompletion (isCStarSeminorm_zero (A := A))
  hom := toSeminormCompletion (isCStarSeminorm_zero (A := A))
  map_rel p _ :=
    (norm_toSeminormCompletion (isCStarSeminorm_zero (A := A)) p.1).le.trans
      (NNReal.coe_nonneg p.2)

instance (P : Set (A × ℝ≥0)) : Nonempty (EnvRep A P) := ⟨zeroRep P⟩

omit [StarModule ℂ A] in
/-- A representation kills the relations with bound `0`. -/
theorem EnvRep.map_rel_zero {P : Set (A × ℝ≥0)} (π : EnvRep A P) {r : A}
    (hr : (r, (0 : ℝ≥0)) ∈ P) : π.hom r = 0 := by
  have hn : ‖π.hom r‖ ≤ 0 := π.map_rel _ hr
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

omit [StarModule ℂ A] in
/-- A representation identifies `a` and `b` when `a - b = 0` is a relation. -/
theorem EnvRep.map_eq_of_sub_mem {P : Set (A × ℝ≥0)} (π : EnvRep A P) {a b : A}
    (h : (a - b, (0 : ℝ≥0)) ∈ P) : π.hom a = π.hom b :=
  sub_eq_zero.mp (by rw [← map_sub]; exact π.map_rel_zero h)

variable (P : Set (A × ℝ≥0))

/-- Every element of `A` is norm-bounded over all representations satisfying `P`. -/
def IsBounded : Prop := ∀ a : A, BddAbove (Set.range fun π : EnvRep A P ↦ ‖π.hom a‖)

/-- The universal seminorm: the supremum of `‖π a‖` over all representations satisfying `P`. -/
def repNorm (a : A) : ℝ := ⨆ π : EnvRep A P, ‖π.hom a‖

/-- If `P` is bounded, the universal seminorm is a C⋆-seminorm. -/
theorem isCStarSeminorm_repNorm (hP : IsBounded P) : IsCStarSeminorm (repNorm P) :=
  isCStarSeminorm_iSup (p := fun (π : EnvRep A P) (a : A) ↦ ‖π.hom a‖) ⟨zeroRep P⟩
    (fun π ↦ (isCStarSeminorm_norm (B := π.carrier)).comp π.hom) hP

/-- **The enveloping C⋆-algebra** of `A` with relations `P`. -/
abbrev Envelope (hP : IsBounded P) : Type u := SeminormCompletion (isCStarSeminorm_repNorm P hP)

/-- The canonical ⋆-homomorphism of `A` into its envelope. -/
def envHom (hP : IsBounded P) : A →⋆ₐ[ℂ] Envelope P hP :=
  toSeminormCompletion (isCStarSeminorm_repNorm P hP)

@[simp] theorem norm_envHom (hP : IsBounded P) (a : A) : ‖envHom P hP a‖ = repNorm P a :=
  norm_toSeminormCompletion (isCStarSeminorm_repNorm P hP) a

/-- The canonical map satisfies the relations. -/
theorem norm_envHom_rel (hP : IsBounded P) {p : A × ℝ≥0} (hp : p ∈ P) :
    ‖envHom P hP p.1‖ ≤ p.2 := by
  rw [norm_envHom]
  exact ciSup_le fun π ↦ π.map_rel p hp

/-- The canonical map kills the relations with bound `0`. -/
theorem envHom_rel (hP : IsBounded P) {r : A} (hr : (r, (0 : ℝ≥0)) ∈ P) :
    envHom P hP r = 0 := by
  have hn : ‖envHom P hP r‖ ≤ 0 := norm_envHom_rel P hP hr
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- The canonical map identifies `a` and `b` when `a - b = 0` is a relation. -/
theorem envHom_eq_of_sub_mem (hP : IsBounded P) {a b : A} (h : (a - b, (0 : ℝ≥0)) ∈ P) :
    envHom P hP a = envHom P hP b :=
  sub_eq_zero.mp (by rw [← map_sub]; exact envHom_rel P hP h)

variable {P}

/-- A representation satisfying `P`, into a C⋆-algebra in any universe, gives one in the
universe of `A`: the completion of `A` for the image seminorm `a ↦ ‖f a‖`. -/
def shrinkRep {B : Type v} [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ p : A × ℝ≥0, p ∈ P → ‖f p.1‖ ≤ p.2) : EnvRep A P where
  carrier := SeminormCompletion ((isCStarSeminorm_norm (B := B)).comp f)
  hom := toSeminormCompletion ((isCStarSeminorm_norm (B := B)).comp f)
  map_rel p hp := by
    have hn : ‖toSeminormCompletion ((isCStarSeminorm_norm (B := B)).comp f) p.1‖ = ‖f p.1‖ :=
      norm_toSeminormCompletion _ p.1
    rw [hn]
    exact hf p hp

/-- Every representation satisfying `P`, in any universe, is dominated by the universal
seminorm. -/
theorem norm_le_repNorm (hP : IsBounded P) {B : Type v} [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ p : A × ℝ≥0, p ∈ P → ‖f p.1‖ ≤ p.2) (a : A) : ‖f a‖ ≤ repNorm P a := by
  have hπ : ‖(shrinkRep f hf).hom a‖ = ‖f a‖ :=
    norm_toSeminormCompletion ((isCStarSeminorm_norm (B := B)).comp f) a
  exact (le_of_eq hπ.symm).trans (le_ciSup (hP a) (shrinkRep f hf))

/-- **The universal property of the envelope.**  A representation satisfying `P`, into a
C⋆-algebra in any universe, factors through `envHom`. -/
def envLift (hP : IsBounded P) {B : Type v} [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ p : A × ℝ≥0, p ∈ P → ‖f p.1‖ ≤ p.2) : Envelope P hP →⋆ₐ[ℂ] B :=
  seminormCompletionLift (isCStarSeminorm_repNorm P hP) f (norm_le_repNorm hP f hf)

@[simp] theorem envLift_envHom (hP : IsBounded P) {B : Type v} [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : ∀ p : A × ℝ≥0, p ∈ P → ‖f p.1‖ ≤ p.2) (a : A) :
    envLift hP f hf (envHom P hP a) = f a :=
  seminormCompletionLift_apply (isCStarSeminorm_repNorm P hP) f (norm_le_repNorm hP f hf) a

/-- Two ⋆-homomorphisms out of the envelope that agree on the image of `A` are equal. -/
theorem envHom_ext (hP : IsBounded P) {B : Type v} [CStarAlgebra B]
    {f₁ f₂ : Envelope P hP →⋆ₐ[ℂ] B}
    (h : ∀ a : A, f₁ (envHom P hP a) = f₂ (envHom P hP a)) : f₁ = f₂ :=
  seminormCompletion_ext (isCStarSeminorm_repNorm P hP) f₁ f₂ h

/-- Existence and uniqueness of the factorization through the envelope. -/
theorem existsUnique_envLift (hP : IsBounded P) {B : Type v} [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : ∀ p : A × ℝ≥0, p ∈ P → ‖f p.1‖ ≤ p.2) :
    ∃! F : Envelope P hP →⋆ₐ[ℂ] B, ∀ a : A, F (envHom P hP a) = f a :=
  seminormCompletion_existsUnique_lift (isCStarSeminorm_repNorm P hP) f
    (norm_le_repNorm hP f hf)

/-! ## Producers of boundedness -/

variable (P)

/-- `a` is norm-bounded over all representations satisfying `P`. -/
def IsBoundedElem (a : A) : Prop := ∃ C : ℝ, ∀ π : EnvRep A P, ‖π.hom a‖ ≤ C

/-- The bounded elements form a subalgebra. -/
def boundedSubalgebra : Subalgebra ℂ A where
  carrier := {a | IsBoundedElem P a}
  mul_mem' := by
    rintro a b ⟨C, hC⟩ ⟨D, hD⟩
    show ∃ E : ℝ, ∀ π : EnvRep A P, ‖π.hom (a * b)‖ ≤ E
    refine ⟨max C 0 * max D 0, fun π ↦ ?_⟩
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg ((hC π).trans (le_max_left _ _))
      ((hD π).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))
  add_mem' := by
    rintro a b ⟨C, hC⟩ ⟨D, hD⟩
    show ∃ E : ℝ, ∀ π : EnvRep A P, ‖π.hom (a + b)‖ ≤ E
    refine ⟨C + D, fun π ↦ ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hC π) (hD π))
  algebraMap_mem' r := by
    show ∃ E : ℝ, ∀ π : EnvRep A P, ‖π.hom (algebraMap ℂ A r)‖ ≤ E
    refine ⟨‖r‖, fun π ↦ ?_⟩
    rw [AlgHomClass.commutes]
    exact NonUnitalStarAlgHom.norm_apply_le (StarAlgHom.ofId ℂ π.carrier) r

omit [StarModule ℂ A] in
/-- An element with a norm bound in `P` is bounded. -/
theorem isBoundedElem_of_mem {a : A} {c : ℝ≥0} (h : (a, c) ∈ P) : IsBoundedElem P a :=
  ⟨(c : ℝ), fun π ↦ π.map_rel _ h⟩

omit [StarModule ℂ A] in
/-- The bounded elements are closed under `star`. -/
theorem isBoundedElem_star {a : A} (ha : IsBoundedElem P a) : IsBoundedElem P (star a) := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, fun π ↦ ?_⟩
  rw [StarHomClass.map_star, norm_star]
  exact hC π

omit [StarModule ℂ A] in
/-- **Boundedness is checked on generators.** -/
theorem isBounded_of_adjoin {S : Set A} (hS : Algebra.adjoin ℂ S = ⊤)
    (hb : ∀ s ∈ S, IsBoundedElem P s) : IsBounded P := by
  intro a
  have hsub : Algebra.adjoin ℂ S ≤ boundedSubalgebra P :=
    Algebra.adjoin_le fun s hs ↦ hb s hs
  have ha : a ∈ Algebra.adjoin ℂ S := by
    rw [hS]
    exact Algebra.mem_top
  obtain ⟨C, hC⟩ : IsBoundedElem P a := hsub ha
  exact bddAbove_def.mpr ⟨C, Set.forall_mem_range.mpr hC⟩

omit [StarModule ℂ A] in
/-- In a C⋆-algebra, if `star x * x` is idempotent then `‖x‖ ≤ 1`. -/
theorem norm_le_one_of_star_mul_self_idem {B : Type v} [CStarAlgebra B] {x : B}
    (h : (star x * x) * (star x * x) = star x * x) : ‖x‖ ≤ 1 := by
  have h1 : ‖star (star x * x) * (star x * x)‖ = ‖star x * x‖ * ‖star x * x‖ :=
    CStarRing.norm_star_mul_self
  rw [star_mul, star_star, h] at h1
  have hy : ‖star x * x‖ ≤ 1 := by nlinarith [norm_nonneg (star x * x)]
  have hx : ‖x‖ * ‖x‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self]
    exact hy
  nlinarith [norm_nonneg x]

omit [StarModule ℂ A] in
/-- **Partial isometries are bounded.**  If `star a * a` is idempotent in every representation
satisfying `P`, then `a` is bounded by `1`. -/
theorem isBoundedElem_of_idem {a : A}
    (h : ∀ π : EnvRep A P, π.hom (star a * a) * π.hom (star a * a) = π.hom (star a * a)) :
    IsBoundedElem P a := by
  refine ⟨1, fun π ↦ norm_le_one_of_star_mul_self_idem ?_⟩
  have hπ := h π
  rwa [map_mul, StarHomClass.map_star] at hπ

omit [StarModule ℂ A] in
/-- An element subject to the isometry relation `star a * a = 1` is bounded. -/
theorem isBoundedElem_of_isometry_rel {a : A} (h : (star a * a - 1, (0 : ℝ≥0)) ∈ P) :
    IsBoundedElem P a :=
  isBoundedElem_of_idem P fun π ↦ by rw [π.map_eq_of_sub_mem h, map_one, mul_one]

omit [StarModule ℂ A] in
/-- An element subject to the partial-isometry relation `(star a * a)² = star a * a` is
bounded. -/
theorem isBoundedElem_of_idem_rel {a : A}
    (h : ((star a * a) * (star a * a) - star a * a, (0 : ℝ≥0)) ∈ P) : IsBoundedElem P a :=
  isBoundedElem_of_idem P fun π ↦ by
    have hπ := π.map_eq_of_sub_mem h
    rwa [map_mul] at hπ

end

end CStarLimits
end GroupApproximation
