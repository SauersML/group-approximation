import GroupApproximation.Analysis.KazhdanProjectionAbsorption
import GroupApproximation.Analysis.QuasiRegularWitness

/-!
# Strict Kazhdan compression makes the maximal group C-star algebra
# properly infinite

The endpoint assembly of directive (c)
(`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1): from strict Kazhdan
compression data — a Kazhdan group mapped into `E`, conjugated strictly
inside itself by `t` — the maximal group C-star algebra of `E` carries a
`ProperProjectionCompression`: the Kazhdan projection `p` of the image
subgroup and its `t`-conjugate `q = u p u⁻¹` with `q` absorbing `p`
properly.  All conclusions of `ProperIsometryFromCompression` (a proper
isometry, failure of Dedekind-finiteness and stable finiteness, absence
of a faithful tracial state) follow.

The gap comes from `AbstractSpectralGap`, the projection from
`CStarSpectralProjection`, the absorption identities from
`KazhdanProjectionAbsorption`, and the properness from the quasi-regular
`ℓ²(E/K)` coordinate of `QuasiRegularWitness` — the base coset point
mass is fixed by the conjugated subgroup and moved by the strictness
witness.
-/

namespace GroupApproximation
namespace MaximalCStarProperCompression

open AbstractSpectralGap CStarSpectralProjection KazhdanProjectionAbsorption
open QuasiRegularWitness

noncomputable section

universe u w

/-- Strict Kazhdan compression data over the ambient group `E`. -/
structure StrictKazhdanCompression (Γ : Type w) (E : Type u) [Group Γ]
    [Group E] where
  /-- The Kazhdan source mapped into the ambient group. -/
  iota : Γ →* E
  /-- The compressing element. -/
  t : E
  /-- The Kazhdan set. -/
  Q : Finset Γ
  /-- The Kazhdan tolerance. -/
  ε : ℝ
  /-- The Kazhdan pair, at the universe of the maximal algebra. -/
  kazhdan : IsKazhdanPair.{w, u + 1} Γ Q ε
  /-- The symmetric generating superset used for averaging. -/
  S : Finset Γ
  /-- The Kazhdan set sits inside the averaging set. -/
  QS : Q ⊆ S
  /-- The identity belongs to the averaging set. -/
  one_mem : 1 ∈ S
  /-- The averaging set is symmetric. -/
  symm : ∀ γ ∈ S, γ⁻¹ ∈ S
  /-- Normalized tolerance. -/
  eps_le : ε ≤ 1
  /-- The averaging set generates the source. -/
  generates : Subgroup.closure (S : Set Γ) = ⊤
  /-- Conjugation by `t` carries the image into itself. -/
  compresses : ∀ γ : Γ, ∃ δ : Γ, t * iota γ * t⁻¹ = iota δ
  /-- Strictness: some image element escapes the conjugated image. -/
  strict : ∃ a : Γ,
    iota a ∉ iota.range.map (MulAut.conj t).toMonoidHom

namespace StrictKazhdanCompression

variable {Γ : Type w} {E : Type u} [Group Γ] [Group E]

local instance : PartialOrder (MaximalGroupCStar E) :=
  CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (MaximalGroupCStar E) :=
  CStarAlgebra.spectralOrderedRing _

variable (D : StrictKazhdanCompression Γ E)

/-- The image representation inside the maximal algebra's unitaries. -/
def rep : Γ →* unitary (MaximalGroupCStar E) :=
  (maximalGroupCStarUnitaryHom E).comp D.iota

/-- The averaging element. -/
def avg : MaximalGroupCStar E := unitaryAverage (rep D) D.S

/-- The spectral rate. -/
def rate : ℝ := 1 - D.ε ^ 2 / (4 * D.S.card)

/-- The Kazhdan projection. -/
def proj : MaximalGroupCStar E := spectralProjection (avg D) (rate D)

/-- The compressing unitary. -/
def shift : MaximalGroupCStar E := maximalGroupCStarGenerator E D.t

theorem rate_lt_one : rate D < 1 := by
  have hε : 0 < D.ε := D.kazhdan.1
  have hcard : (0 : ℝ) < D.S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, D.one_mem⟩
  have hq : 0 < D.ε ^ 2 / (4 * D.S.card) := by
    apply div_pos (by positivity) (by positivity)
  unfold rate
  linarith

theorem isSelfAdjoint_avg : IsSelfAdjoint (avg D) :=
  isSelfAdjoint_unitaryAverage (rep D) D.symm

theorem gap : ∀ μ ∈ spectrum ℝ (avg D), μ ≤ rate D ∨ μ = 1 := by
  intro μ hμ
  by_cases hμ1 : μ = 1
  · exact Or.inr hμ1
  · left
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ (avg D) := by
      have h := spectrum.algebraMap_mem ℂ hμ
      rwa [show (algebraMap ℝ ℂ) μ = (μ : ℂ) by simp] at h
    exact unitaryAverage_spectrum_le (rep D) D.kazhdan D.S D.QS D.one_mem
      D.symm D.eps_le hμℂ hμ1

theorem isSelfAdjoint_proj : IsSelfAdjoint (proj D) :=
  isSelfAdjoint_spectralProjection (avg D)

theorem proj_mul_proj : proj D * proj D = proj D :=
  isIdempotentElem_spectralProjection (avg D) (isSelfAdjoint_avg D)
    (rate_lt_one D) (gap D)

theorem avg_mul_proj : avg D * proj D = proj D :=
  mul_spectralProjection (avg D) (isSelfAdjoint_avg D) (rate_lt_one D)
    (gap D)

theorem proj_mul_avg : proj D * avg D = proj D :=
  spectralProjection_mul (avg D) (isSelfAdjoint_avg D) (rate_lt_one D)
    (gap D)

theorem shift_star_mul : star (shift D) * shift D = 1 := by
  unfold shift
  rw [star_maximalGroupCStarGenerator,
    maximalGroupCStarGenerator_mul, inv_mul_cancel]
  exact congrArg
    (fun w : unitary (MaximalGroupCStar E) => (w : MaximalGroupCStar E))
    (map_one (maximalGroupCStarUnitaryHom E))

theorem shift_mul_star : shift D * star (shift D) = 1 := by
  unfold shift
  rw [star_maximalGroupCStarGenerator,
    maximalGroupCStarGenerator_mul, mul_inv_cancel]
  exact congrArg
    (fun w : unitary (MaximalGroupCStar E) => (w : MaximalGroupCStar E))
    (map_one (maximalGroupCStarUnitaryHom E))

/-- Every image unitary fixes the Kazhdan projection. -/
theorem rep_mul_proj (γ : Γ) :
    ((rep D γ : unitary (MaximalGroupCStar E)) : MaximalGroupCStar E)
      * proj D = proj D := by
  have hfix := unitary_mul_eq_of_average_absorbs (rep D) D.symm
    (isSelfAdjoint_proj D) (proj_mul_proj D) (avg_mul_proj D)
    (proj_mul_avg D)
  have hγ : γ ∈ Subgroup.closure (D.S : Set Γ) := by
    rw [D.generates]
    trivial
  exact unitary_mul_eq_of_closure (rep D) hfix hγ

theorem shift_generator_conj (g : E) :
    shift D * maximalGroupCStarGenerator E g * star (shift D)
      = maximalGroupCStarGenerator E (D.t * g * D.t⁻¹) := by
  unfold shift
  rw [star_maximalGroupCStarGenerator,
    maximalGroupCStarGenerator_mul, maximalGroupCStarGenerator_mul]

/-- The conjugated average absorbs the projection on the left. -/
theorem conjugated_avg_mul_proj :
    (shift D * avg D * star (shift D)) * proj D = proj D := by
  classical
  have hcard : ((D.S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩
  have hconj : shift D * avg D * star (shift D)
      = ((D.S.card : ℂ))⁻¹ • ∑ γ ∈ D.S,
          maximalGroupCStarGenerator E (D.t * D.iota γ * D.t⁻¹) := by
    unfold avg unitaryAverage
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    exact shift_generator_conj D (D.iota γ)
  rw [hconj, smul_mul_assoc, Finset.sum_mul]
  have hterm : ∀ γ ∈ D.S,
      maximalGroupCStarGenerator E (D.t * D.iota γ * D.t⁻¹) * proj D
        = proj D := by
    intro γ _
    obtain ⟨δ, hδ⟩ := D.compresses γ
    rw [hδ]
    exact rep_mul_proj D δ
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ D.S.card (proj D), smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The conjugated projection absorbs the projection. -/
theorem conjugate_mul_proj :
    (shift D * proj D * star (shift D)) * proj D = proj D :=
  conjugated_projection_absorbs (isSelfAdjoint_avg D) (rate_lt_one D)
    (gap D) (shift_star_mul D) (shift_mul_star D)
    (conjugated_avg_mul_proj D)

theorem isSelfAdjoint_conjugate :
    IsSelfAdjoint (shift D * proj D * star (shift D)) := by
  rw [IsSelfAdjoint, star_mul, star_mul, star_star,
    (isSelfAdjoint_proj D).star_eq, mul_assoc]

theorem proj_mul_conjugate :
    proj D * (shift D * proj D * star (shift D)) = proj D := by
  have h := congrArg star (conjugate_mul_proj D)
  rw [star_mul, (isSelfAdjoint_proj D).star_eq,
    (isSelfAdjoint_conjugate D).star_eq] at h
  exact h

section Properness

/-- The image subgroup. -/
def lambda : Subgroup E := D.iota.range

/-- The conjugated image subgroup. -/
def conjLambda : Subgroup E :=
  (lambda D).map (MulAut.conj D.t).toMonoidHom

theorem conj_mem_conjLambda (γ : Γ) :
    D.t * D.iota γ * D.t⁻¹ ∈ conjLambda D := by
  refine ⟨D.iota γ, ⟨γ, rfl⟩, ?_⟩
  rfl

/-- The quasi-regular coordinate used for properness.

`@[reducible]` is load-bearing, not decoration: the proofs below apply
`evw D a` to a vector, which needs the elaborator to see through
`(witnessRep D).carrier` to the concrete operator type before it can find
a `CoeFun`.  Without it every such application fails with "Function
expected at ... but this term has type `(witnessRep D).carrier`". -/
@[reducible] def witnessRep : CStarUnitaryRepresentation E :=
  quasiRegularRepresentation E (conjLambda D)

/-- Evaluation at the witness coordinate.

The codomain is spelled concretely rather than as `(witnessRep D).carrier`.
The proofs below apply `evw D a` to a vector, and the elaborator looks for
a `CoeFun` on the *declared* type: written as a projection it stays
`(witnessRep D).carrier` and every application fails with "Function
expected", even though the projection is defeq to the operator algebra.
Marking `witnessRep`, `quasiRegularRepresentation` and `ofHom` reducible
does not help -- the type is never unfolded at all. -/
def evw : MaximalGroupCStar E →⋆ₐ[ℂ]
    (CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D)) :=
  maximalGroupCStarEval E (witnessRep D)

theorem baseVector_fixed_of_conj (γ : Γ)
    [DecidableEq (E ⧸ conjLambda D)] :
    quasiRegularOperator E (conjLambda D) (D.t * D.iota γ * D.t⁻¹)
      (baseVector E (conjLambda D)) = baseVector E (conjLambda D) :=
  quasiRegularOperator_baseVector_of_mem E (conjLambda D)
    (conj_mem_conjLambda D γ)

/-- **Properness**: the conjugated projection differs from the
projection, witnessed at the quasi-regular coordinate. -/
theorem conjugate_ne_proj :
    shift D * proj D * star (shift D) ≠ proj D := by
  classical
  letI : DecidableEq (E ⧸ conjLambda D) := Classical.decEq _
  obtain ⟨a, ha⟩ := D.strict
  intro hcontra
  -- `cmul` and `.sub_apply` are deprecated into a
  -- different namespace, and `-DwarningAsError=true` makes using them fatal.
  -- Both statements are `rfl` here: CLM multiplication IS composition and
  -- subtraction IS pointwise, so state them locally rather than chase names.
  have cmul : ∀ (f g : CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D)) (x : CosetHilbert E (conjLambda D)), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have csub : ∀ (f g : CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D)) (x : CosetHilbert E (conjLambda D)), (f - g) x = f x - g x :=
    fun _ _ _ => rfl
  have hgen : ∀ g : E, evw D (maximalGroupCStarGenerator E g)
      = (((witnessRep D).hom g : unitary (witnessRep D).carrier)
        : (witnessRep D).carrier) :=
    fun g => maximalGroupCStarEval_generator E (witnessRep D) g
  -- the moved base vector, fixed by every image generator
  have hfixw : ∀ γ : Γ,
      quasiRegularOperator E (conjLambda D) (D.iota γ)
        (quasiRegularOperator E (conjLambda D) D.t⁻¹
          (baseVector E (conjLambda D)))
      = quasiRegularOperator E (conjLambda D) D.t⁻¹
          (baseVector E (conjLambda D)) := by
    intro γ
    have h1 := baseVector_fixed_of_conj D γ
    have h2 : quasiRegularOperator E (conjLambda D) (D.iota γ)
        (quasiRegularOperator E (conjLambda D) D.t⁻¹
          (baseVector E (conjLambda D)))
        = quasiRegularOperator E (conjLambda D)
            (D.iota γ * D.t⁻¹) (baseVector E (conjLambda D)) := by
      rw [← quasiRegularOperator_mul]
      rfl
    have h3 : quasiRegularOperator E (conjLambda D)
        (D.iota γ * D.t⁻¹) (baseVector E (conjLambda D))
        = quasiRegularOperator E (conjLambda D) D.t⁻¹
            (quasiRegularOperator E (conjLambda D)
              (D.t * D.iota γ * D.t⁻¹) (baseVector E (conjLambda D))) := by
      rw [← cmul, quasiRegularOperator_mul]
      congr 2
      group
    rw [h2, h3, h1]
  -- the evaluated average fixes the moved base vector
  have hmw : evw D (avg D)
      (quasiRegularOperator E (conjLambda D) D.t⁻¹
        (baseVector E (conjLambda D)))
      = quasiRegularOperator E (conjLambda D) D.t⁻¹
          (baseVector E (conjLambda D)) := by
    have hcard : ((D.S.card : ℂ)) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩
    have h1 : evw D (avg D)
        = ((D.S.card : ℂ))⁻¹ • ∑ γ ∈ D.S,
            evw D (maximalGroupCStarGenerator E (D.iota γ)) := by
      have h2 : avg D = ((D.S.card : ℂ))⁻¹ • ∑ γ ∈ D.S,
          maximalGroupCStarGenerator E (D.iota γ) := rfl
      rw [h2, map_smul, map_sum]
    rw [h1, smul_apply, sum_apply]
    have hterm : ∀ γ ∈ D.S,
        evw D (maximalGroupCStarGenerator E (D.iota γ))
          (quasiRegularOperator E (conjLambda D) D.t⁻¹
            (baseVector E (conjLambda D)))
        = quasiRegularOperator E (conjLambda D) D.t⁻¹
            (baseVector E (conjLambda D)) := by
      intro γ _
      rw [hgen (D.iota γ)]
      exact hfixw γ
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ D.S.card, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  -- the complement of the conjugated projection kills the base vector
  have hfac' : (1 : MaximalGroupCStar E) - proj D
      = cfc (gapResolvent (rate D)) (avg D)
        * ((1 : MaximalGroupCStar E) - avg D) :=
    one_sub_spectralProjection_eq (avg D) (isSelfAdjoint_avg D)
      (rate_lt_one D) (gap D)
  have hq1 : (1 : MaximalGroupCStar E)
      - shift D * proj D * star (shift D)
      = shift D * (cfc (gapResolvent (rate D)) (avg D)
          * ((1 : MaximalGroupCStar E) - avg D)) * star (shift D) := by
    rw [show (1 : MaximalGroupCStar E)
        - shift D * proj D * star (shift D)
        = shift D * ((1 : MaximalGroupCStar E) - proj D)
          * star (shift D) by
      rw [mul_sub, sub_mul, mul_one, shift_mul_star]]
    rw [hfac']
  have hwv : evw D (star (shift D)) (baseVector E (conjLambda D))
      = quasiRegularOperator E (conjLambda D) D.t⁻¹
          (baseVector E (conjLambda D)) := by
    rw [show star (shift D)
        = maximalGroupCStarGenerator E D.t⁻¹ from
      star_maximalGroupCStarGenerator E D.t]
    rw [hgen D.t⁻¹]
    rfl
  have hsubw : ((1 : CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D)) - evw D (avg D))
      (quasiRegularOperator E (conjLambda D) D.t⁻¹
        (baseVector E (conjLambda D))) = 0 := by
    rw [csub, hmw]
    show quasiRegularOperator E (conjLambda D) D.t⁻¹
        (baseVector E (conjLambda D))
      - quasiRegularOperator E (conjLambda D) D.t⁻¹
        (baseVector E (conjLambda D)) = 0
    rw [sub_self]
  have h0 : evw D ((1 : MaximalGroupCStar E)
      - shift D * proj D * star (shift D))
      (baseVector E (conjLambda D)) = 0 := by
    rw [hq1, map_mul, map_mul, map_mul, map_sub, map_one,
      cmul, hwv, cmul,
      cmul, hsubw, map_zero, map_zero]
  have hqv : evw D (shift D * proj D * star (shift D))
      (baseVector E (conjLambda D)) = baseVector E (conjLambda D) := by
    have h2 : ((1 : CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D))
        - evw D (shift D * proj D * star (shift D)))
        (baseVector E (conjLambda D)) = 0 := by
      rw [← map_one (evw D), ← map_sub]
      exact h0
    rw [csub] at h2
    have h3 : baseVector E (conjLambda D)
        - evw D (shift D * proj D * star (shift D))
          (baseVector E (conjLambda D)) = 0 := h2
    exact (sub_eq_zero.mp h3).symm
  -- but the plain projection cannot fix the base vector
  have hpvne : evw D (proj D) (baseVector E (conjLambda D))
      ≠ baseVector E (conjLambda D) := by
    intro hpv
    have hfix : maximalGroupCStarGenerator E (D.iota a) * proj D
        = proj D := rep_mul_proj D a
    have h4 := congrArg (evw D) hfix
    rw [map_mul] at h4
    have h5 := congrArg
      (fun T : CosetHilbert E (conjLambda D) →L[ℂ] CosetHilbert E (conjLambda D) =>
        T (baseVector E (conjLambda D))) h4
    rw [cmul, hpv, hgen (D.iota a)] at h5
    exact quasiRegularOperator_baseVector_of_notMem E (conjLambda D)
      ha h5
  rw [hcontra] at hqv
  exact hpvne hqv

end Properness

/-- **The endpoint**: strict Kazhdan compression data yields a proper
projection compression of the maximal group C-star algebra. -/
def toProperProjectionCompression :
    ProperProjectionCompression (MaximalGroupCStar E) where
  p := proj D
  u := shift D
  p_star := (isSelfAdjoint_proj D).star_eq
  p_mul_p := proj_mul_proj D
  u_star_mul := shift_star_mul D
  u_mul_star := shift_mul_star D
  p_mul_conjugate := proj_mul_conjugate D
  conjugate_mul_p := conjugate_mul_proj D
  conjugate_ne := conjugate_ne_proj D

include D in
/-- The maximal algebra of a strictly Kazhdan-compressed group is not
Dedekind finite: it contains a one-sided-invertible non-unit. -/
theorem maximalCStar_not_isDedekindFiniteMonoid :
    ¬ IsDedekindFiniteMonoid (MaximalGroupCStar E) :=
  (toProperProjectionCompression D).not_isDedekindFiniteMonoid

include D in
/-- The maximal algebra of a strictly Kazhdan-compressed group is not
stably finite. -/
theorem maximalCStar_not_isStablyFiniteRing :
    ¬ IsStablyFiniteRing (MaximalGroupCStar E) :=
  (toProperProjectionCompression D).not_isStablyFiniteRing

include D in
/-- The maximal algebra of a strictly Kazhdan-compressed group carries no
faithful tracial state. -/
theorem maximalCStar_no_faithfulTracialState :
    ¬ Nonempty (FaithfulTracialState (MaximalGroupCStar E)) :=
  (toProperProjectionCompression D).no_faithfulTracialState

end StrictKazhdanCompression

end

end MaximalCStarProperCompression
end GroupApproximation
