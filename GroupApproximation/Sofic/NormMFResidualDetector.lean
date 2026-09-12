import GroupApproximation.Sofic.WeakMFUltraproduct
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The universal-ultraproduct residual and the marked-compression endpoint

This file isolates the exact formal endpoint of the marked Kazhdan-compression
obstruction.  An element is `NormMFInvisible` when every homomorphism from its
group to every operator-norm matrix ultraproduct kills it.  The quantifier is
over every ultrafilter, including principal ultrafilters.  Such elements form
the universal-ultraproduct residual defined below.  This is not definitionally
the paper's cofinite-corona radical.  For countable groups,
`NormMFCoronaRadical` proves elementwise equivalence and equality of the two
subgroups.  A single nonidentity element in this residual precludes
weak/operator-norm MF approximation.

The final section records the group word used by the explicit construction:

`w = [t c t⁻¹, a (t c t⁻¹) a⁻¹]`.

This module supplies the residual/detector layer: it turns a proof that the
marked word is `NormMFInvisible`, together with `w ≠ 1`, into `¬ IsWeakMF G`
using the repository's faithful-ultraproduct theorem.  The analytic
invisibility theorem is proved downstream, without an added premise, in
`MarkedCompressionSequentialKill`; the concrete public assembly is
`ChosenNonMFTheorem`.

No C*-algebraic premise is hidden in the definitions below: the targets are
literally `UniversalWeakMF`, the operator-norm matrix ultraproduct already
constructed in `WeakMFUltraproduct`.
-/

namespace GroupApproximation

open Filter
open scoped commutatorElement

universe u
universe v

variable {G : Type u} [Group G]

/-! ## The universal operator-norm-ultraproduct residual -/

/-- An element is invisible to operator-norm matrix ultraproducts when every
homomorphism into every such ultraproduct kills it.  This includes targets
built from principal ultrafilters; use `CoronaMFInvisible` for the paper's
cofinite-corona formulation. -/
def NormMFInvisible (x : G) : Prop :=
  ∀ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X), rho x = 1

/-- The identity is invisible in every operator-norm matrix ultraproduct. -/
theorem normMFInvisible_one : NormMFInvisible (1 : G) := by
  intro I U X rho
  exact map_one rho

/-- MF-invisibility is functorial: every homomorphic image of an invisible
element is invisible.  Consequently, any image in which such an element
survives is automatically non-MF. -/
theorem NormMFInvisible.map {H : Type v} [Group H] {x : G}
    (hx : NormMFInvisible x) (f : G →* H) : NormMFInvisible (f x) := by
  intro I U X rho
  exact hx I U X (rho.comp f)

/-- Universal-ultraproduct-invisible elements form a subgroup.  The historical
name `normMFResidual` is not a definitional identification with the paper's
cofinite-corona radical; see `coronaMFResidual_eq_normMFResidual` for the
countable-group comparison theorem. -/
def normMFResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | NormMFInvisible x}
  one_mem' := normMFInvisible_one
  mul_mem' := by
    intro x y hx hy I U X rho
    rw [map_mul, hx I U X rho, hy I U X rho, one_mul]
  inv_mem' := by
    intro x hx I U X rho
    rw [map_inv, hx I U X rho, inv_one]

@[simp] theorem mem_normMFResidual_iff {x : G} :
    x ∈ normMFResidual G ↔ NormMFInvisible x :=
  Iff.rfl

/-- Every homomorphism to an operator-norm matrix ultraproduct kills the full
operator-norm MF residual. -/
theorem map_eq_one_of_mem_normMFResidual
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) {x : G}
    (hx : x ∈ normMFResidual G) : rho x = 1 :=
  hx I U X rho

/-- The image of the MF residual under any homomorphism lies in the MF
residual of the target. -/
theorem map_normMFResidual_le {H : Type v} [Group H] (f : G →* H) :
    (normMFResidual G).map f ≤ normMFResidual H := by
  rintro y ⟨x, hx, rfl⟩
  exact (show NormMFInvisible x from hx).map f

/-- The MF residual is normal. -/
instance normMFResidual_normal : (normMFResidual G).Normal := by
  constructor
  intro x hx g
  change NormMFInvisible (g * x * g⁻¹)
  intro I U X rho
  rw [map_mul, map_mul, map_inv, hx I U X rho]
  group

/-- **One-element non-MF criterion.**  A countable group containing a
nonidentity element killed by every operator-norm matrix-ultraproduct
representation is not weak/operator-norm MF.

The proof uses `exists_normUltraproductEmbedding_of_isWeakMF`: weak-MF would
give one injective homomorphism into precisely such a target. -/
theorem not_isWeakMF_of_normMFInvisible
    [Countable G] {x : G} (hx : NormMFInvisible x) (hne : x ≠ 1) :
    ¬ IsWeakMF G := by
  intro hMF
  obtain ⟨A, rho, hrho⟩ := exists_normUltraproductEmbedding_of_isWeakMF hMF
  apply hne
  apply hrho
  simpa using hx ℕ (Ultrafilter.of Filter.cofinite) A.model rho

/-- Subgroup-membership form of the one-element non-MF criterion. -/
theorem not_isWeakMF_of_mem_normMFResidual
    [Countable G] {x : G} (hx : x ∈ normMFResidual G) (hne : x ≠ 1) :
    ¬ IsWeakMF G :=
  not_isWeakMF_of_normMFInvisible hx hne

/-- If an MF-invisible element survives in a homomorphic image, that image is
not weak/operator-norm MF. -/
theorem not_isWeakMF_range_of_normMFInvisible
    [Countable G] {H : Type v} [Group H] {x : G}
    (hx : NormMFInvisible x) (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ IsWeakMF rho.range := by
  letI : Countable rho.range :=
    Function.Surjective.countable rho.rangeRestrict_surjective
  apply not_isWeakMF_of_normMFInvisible (hx.map rho.rangeRestrict)
  intro h
  apply hdetect
  simpa using congrArg Subtype.val h

/-- A weak-MF countable group has trivial operator-norm MF residual. -/
theorem normMFResidual_eq_bot_of_isWeakMF
    [Countable G] (hMF : IsWeakMF G) : normMFResidual G = ⊥ := by
  apply Subgroup.eq_bot_iff_forall (normMFResidual G) |>.2
  intro x hx
  by_contra hne
  exact not_isWeakMF_of_mem_normMFResidual hx hne hMF

/-! ## The marked compression word -/

/-- The marked commutator converting strict compression of a Kazhdan fixed
space into a group element:

`[t c t⁻¹, a (t c t⁻¹) a⁻¹]`.
-/
def markedCompressionWord (t a c : G) : G :=
  ⁅t * c * t⁻¹, a * (t * c * t⁻¹) * a⁻¹⁆

/-- Homomorphisms evaluate the marked compression word componentwise. -/
theorem map_markedCompressionWord
    {H : Type*} [Group H] (rho : G →* H) (t a c : G) :
    rho (markedCompressionWord t a c) =
      markedCompressionWord (rho t) (rho a) (rho c) := by
  simp [markedCompressionWord, map_commutatorElement]

/-- The exact certificate delivered by the marked-compression construction:
the marked word is both nontrivial and invisible to every operator-norm matrix
ultraproduct. -/
structure MarkedCompressionNormCertificate (G : Type u) [Group G] where
  t : G
  a : G
  c : G
  witness_ne_one : markedCompressionWord t a c ≠ 1
  witness_invisible : NormMFInvisible (markedCompressionWord t a c)

/-- **Formal non-MF endpoint for the marked construction.**  Any countable group
carrying the marked-compression certificate is not weak/operator-norm MF. -/
theorem MarkedCompressionNormCertificate.not_isWeakMF
    [Countable G] (C : MarkedCompressionNormCertificate G) :
    ¬ IsWeakMF G :=
  not_isWeakMF_of_normMFInvisible C.witness_invisible C.witness_ne_one

end GroupApproximation
