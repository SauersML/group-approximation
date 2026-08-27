import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# The cofinite-corona MF radical

The manuscript defines the MF radical of a countable group as the intersection
of the kernels of all homomorphisms to unitary groups of standard cofinite
norm-matrix C-star coronas.  This file uses the equivalent unitary-sequence
presentation; `Analysis.NormMatrixCoronaUnitary` proves the polar-correction
equivalence with the genuine quotient unitary group.  The older Lean API
instead defined `normMFResidual` by quantifying over all
operator-norm matrix ultraproducts.  This file proves equality with the
unitary-sequence radical for countable groups and states the corresponding
universal-quotient results.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-- An element is invisible to every representation in every standard
cofinite norm-matrix corona with positive matrix sizes. -/
def CoronaMFInvisible (x : G) : Prop :=
  ∀ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) →
    ∀ rho : G →* NormMatrixCoronaUnitary X, rho x = 1

/-- Elements invisible to all unitary-sequence presentations of standard
cofinite norm-matrix coronas form the Lean presentation of the manuscript's
MF radical. -/
def coronaMFResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | CoronaMFInvisible x}
  one_mem' := by
    intro X _ rho
    exact map_one rho
  mul_mem' := by
    intro x y hx hy X hX rho
    rw [map_mul, hx X hX rho, hy X hX rho, one_mul]
  inv_mem' := by
    intro x hx X hX rho
    rw [map_inv, hx X hX rho, inv_one]

@[simp] theorem mem_coronaMFResidual_iff {x : G} :
    x ∈ coronaMFResidual G ↔ CoronaMFInvisible x :=
  Iff.rfl

/-- Ultraproduct invisibility implies invisibility in every standard corona.
The proof is deliberately elementwise: a surviving corona image would yield a
sequential marked model and hence an ultraproduct detector. -/
theorem NormMFInvisible.toCoronaMFInvisible [Countable G] {x : G}
    (hx : NormMFInvisible x) : CoronaMFInvisible x := by
  intro X hX rho
  letI : Countable rho.range :=
    Function.Surjective.countable rho.rangeRestrict_surjective
  have hrangeMF : IsOperatorMF rho.range :=
    ⟨X, hX, rho.range.subtype, Subtype.val_injective⟩
  have hxrange : rho.rangeRestrict x ∈ normMFResidual rho.range :=
    mem_normMFResidual_iff.mpr (hx.map rho.rangeRestrict)
  rw [normMFResidual_eq_bot_of_isOperatorMF hrangeMF] at hxrange
  have hone : rho.rangeRestrict x = 1 := Subgroup.mem_bot.mp hxrange
  simpa using congrArg Subtype.val hone

/-- Cofinite-corona invisibility implies ultraproduct invisibility for a
countable group.  The single-corona realization of `normMFResidual` detects
exactly the elements outside that residual. -/
theorem CoronaMFInvisible.toNormMFInvisible [Countable G] {x : G}
    (hx : CoronaMFInvisible x) : NormMFInvisible x := by
  obtain ⟨X, hX, rho, hker⟩ :=
    exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual (G := G)
  have hxker : x ∈ rho.ker := hx X hX rho
  rw [hker] at hxker
  exact hxker

/-- For countable groups, the manuscript's cofinite-corona invisibility and
the ultraproduct invisibility predicate are equivalent. -/
theorem coronaMFInvisible_iff_normMFInvisible [Countable G] {x : G} :
    CoronaMFInvisible x ↔ NormMFInvisible x :=
  ⟨CoronaMFInvisible.toNormMFInvisible,
    NormMFInvisible.toCoronaMFInvisible⟩

/-- The manuscript's MF radical is exactly the existing norm-MF residual. -/
theorem coronaMFResidual_eq_normMFResidual [Countable G] :
    coronaMFResidual G = normMFResidual G := by
  ext x
  exact coronaMFInvisible_iff_normMFInvisible

/-- The unitary-sequence cofinite-corona MF radical is functorial under arbitrary
homomorphisms between countable groups. -/
theorem map_coronaMFResidual_le
    {H : Type v} [Group H] [Countable G] [Countable H] (f : G →* H) :
    (coronaMFResidual G).map f ≤ coronaMFResidual H := by
  rw [coronaMFResidual_eq_normMFResidual,
    coronaMFResidual_eq_normMFResidual]
  exact map_normMFResidual_le f

instance coronaMFResidual_normal : (coronaMFResidual G).Normal := by
  constructor
  intro x hx g
  change CoronaMFInvisible (g * x * g⁻¹)
  intro X hX rho
  rw [map_mul, map_mul, map_inv, hx X hX rho]
  group

/-- The quotient by the unitary-sequence cofinite-corona MF radical is MF. -/
theorem coronaMFQuotient_isOperatorMF [Countable G] :
    IsOperatorMF (G ⧸ coronaMFResidual G) := by
  let e : (G ⧸ coronaMFResidual G) ≃* normMFQuotient G :=
    QuotientGroup.quotientMulEquivOfEq
      (coronaMFResidual_eq_normMFResidual (G := G))
  obtain ⟨X, hX, rho, hrho⟩ := normMFQuotient_isOperatorMF (G := G)
  exact ⟨X, hX, rho.comp e.toMonoidHom, hrho.comp e.injective⟩

/-- A countable group is MF exactly when its unitary-sequence corona radical
is trivial. -/
theorem isOperatorMF_iff_coronaMFResidual_eq_bot [Countable G] :
    IsOperatorMF G ↔ coronaMFResidual G = ⊥ := by
  rw [coronaMFResidual_eq_normMFResidual]
  exact isOperatorMF_iff_normMFResidual_eq_bot

/-- The unitary-sequence cofinite-corona MF radical is the kernel of one standard
corona representation. -/
theorem exists_normMatrixCoronaRepresentation_ker_eq_coronaMFResidual
    [Countable G] :
    ∃ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : G →* NormMatrixCoronaUnitary X,
        rho.ker = coronaMFResidual G := by
  simpa only [coronaMFResidual_eq_normMFResidual] using
    (exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual (G := G))

/-- Every homomorphism from a countable group to a countable MF group factors
uniquely through the quotient by the manuscript's literal MF radical. -/
theorem existsUnique_coronaMFQuotient_factorization_to_isOperatorMF
    [Countable G] {H : Type v} [Group H] [Countable H]
    (f : G →* H) (hH : IsOperatorMF H) :
    ∃! fBar : (G ⧸ coronaMFResidual G) →* H,
      fBar.comp (QuotientGroup.mk' (coronaMFResidual G)) = f := by
  have hker : coronaMFResidual G ≤ f.ker := by
    rw [coronaMFResidual_eq_normMFResidual (G := G)]
    exact normMFResidual_le_ker_of_target_residual_eq_bot f
      (normMFResidual_eq_bot_of_isOperatorMF hH)
  let fBar : (G ⧸ coronaMFResidual G) →* H :=
    QuotientGroup.lift (coronaMFResidual G) f hker
  have hcomp :
      fBar.comp (QuotientGroup.mk' (coronaMFResidual G)) = f :=
    QuotientGroup.lift_comp_mk' (coronaMFResidual G) f hker
  refine ⟨fBar, hcomp, ?_⟩
  intro k hk
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (coronaMFResidual G) q
  exact DFunLike.congr_fun (hk.trans hcomp.symm) g

end GroupApproximation
