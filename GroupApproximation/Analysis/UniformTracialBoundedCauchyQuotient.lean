import GroupApproximation.Analysis.UniformTracialCompletionIdentification
import Mathlib.Algebra.Star.TransferInstance
import Mathlib.Analysis.Normed.Ring.TransferInstance
import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# The bounded uniform-two Cauchy quotient

This file constructs the sequence quotient which is implicit in the bounded
uniform-tracial completion.  A representative is an operator-norm bounded
sequence from the unitized `c₀`-sum which is Cauchy uniformly over all
coordinate two-gauges.  Two representatives are identified exactly when
their same-index difference tends uniformly to zero.

Under the coordinate norm comparison already used by
`UniformTracialCompletionIdentification`, every representative has a unique
realization in `ℂ1 + J`.  The quotient is therefore equivalent to the closed
star subalgebra `scalarPlusJSubalgebra G`.  Its C-star structure is transported
across this proved bijection, after which the realization is bundled as a
star-algebra equivalence.  Thus no completeness, separation, or quotient
identification is postulated as a typeclass or hypothesis.
-/

namespace GroupApproximation
namespace UniformTracialBoundedCauchyQuotient

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- Uniform convergence in the coordinate two-gauges, with the limit written
first so that the expression agrees with the landed identification theorem. -/
def UniformTwoConverges (G : TracialTwoGauge D)
    (a : ℕ → BoundedCStarSequence D) (x : BoundedCStarSequence D) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (x n - a k n) < ε

/-- The uniform two-Cauchy predicate for an outer sequence of bounded block
sequences. -/
def UniformTwoCauchy (G : TracialTwoGauge D)
    (a : ℕ → BoundedCStarSequence D) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
    G.q n (a k n - a l n) < ε

/-- Same-index uniform two-null difference.  This is the equivalence relation
used in the bounded Cauchy completion. -/
def UniformTwoEquivalent (G : TracialTwoGauge D)
    (a b : ℕ → BoundedCStarSequence D) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (a k n - b k n) < ε

/-- A representative of the bounded uniform-two completion of the unitized
`c₀`-sum. -/
structure BoundedUniformTwoCauchySequence (G : TracialTwoGauge D) where
  /-- The approximating sequence. -/
  seq : ℕ → BoundedCStarSequence D
  /-- Every approximant belongs to the original unitized `c₀`-sum. -/
  mem_base : ∀ k, seq k ∈ unitizedC0Sum D
  /-- One operator-norm bound works for all approximants. -/
  norm_bounded : ∃ C : ℝ, ∀ k, ‖seq k‖ ≤ C
  /-- The approximants are uniformly two-Cauchy. -/
  uniform_cauchy : UniformTwoCauchy G seq

namespace BoundedUniformTwoCauchySequence

variable {G : TracialTwoGauge D}

/-- Equivalence of bounded Cauchy representatives is reflexive. -/
theorem equivalent_refl (a : BoundedUniformTwoCauchySequence G) :
    UniformTwoEquivalent G a.seq a.seq := by
  intro ε hε
  exact ⟨0, fun k _ n ↦ by simpa [G.zero] using hε⟩

/-- Equivalence of bounded Cauchy representatives is symmetric. -/
theorem equivalent_symm {a b : BoundedUniformTwoCauchySequence G}
    (h : UniformTwoEquivalent G a.seq b.seq) :
    UniformTwoEquivalent G b.seq a.seq := by
  intro ε hε
  obtain ⟨K, hK⟩ := h ε hε
  exact ⟨K, fun k hk n ↦ by rw [G.sub_comm_eq]; exact hK k hk n⟩

/-- Equivalence of bounded Cauchy representatives is transitive. -/
theorem equivalent_trans {a b c : BoundedUniformTwoCauchySequence G}
    (hab : UniformTwoEquivalent G a.seq b.seq)
    (hbc : UniformTwoEquivalent G b.seq c.seq) :
    UniformTwoEquivalent G a.seq c.seq := by
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := hab (ε / 2) (half_pos hε)
  obtain ⟨K₂, hK₂⟩ := hbc (ε / 2) (half_pos hε)
  refine ⟨max K₁ K₂, fun k hk n ↦ ?_⟩
  have h₁ := hK₁ k ((le_max_left K₁ K₂).trans hk) n
  have h₂ := hK₂ k ((le_max_right K₁ K₂).trans hk) n
  have ht := G.sub_le_sub_add_sub n (a.seq k n) (b.seq k n) (c.seq k n)
  linarith

end BoundedUniformTwoCauchySequence

/-- The exact setoid of bounded uniform-two Cauchy representatives modulo
uniform-two-null difference. -/
def boundedUniformTwoSetoid (G : TracialTwoGauge D) :
    Setoid (BoundedUniformTwoCauchySequence G) where
  r a b := UniformTwoEquivalent G a.seq b.seq
  iseqv := {
    refl := BoundedUniformTwoCauchySequence.equivalent_refl
    symm := BoundedUniformTwoCauchySequence.equivalent_symm
    trans := BoundedUniformTwoCauchySequence.equivalent_trans }

/-- The actual bounded uniform-two Cauchy completion quotient.  The comparison
datum is retained in the type because it is what identifies the abstract
quotient with bounded coordinate sequences. -/
def BoundedUniformTwoCompletion (G : TracialTwoGauge D) (r : ℕ → ℝ)
    (_hr : IsCoordinateNormComparison G r) : Type u :=
  Quotient (boundedUniformTwoSetoid G)

/-- The quotient class of a bounded uniform-two Cauchy representative. -/
def completionMk (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (a : BoundedUniformTwoCauchySequence G) : BoundedUniformTwoCompletion G r hr :=
  Quotient.mk (boundedUniformTwoSetoid G) a

/-- Equality of quotient classes is exactly uniform-two-null difference; the
quotient does not hide a coarser realization relation. -/
theorem completionMk_eq_iff {G : TracialTwoGauge D} {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (a b : BoundedUniformTwoCauchySequence G) :
    completionMk G hr a = completionMk G hr b ↔
      UniformTwoEquivalent G a.seq b.seq := by
  exact Quotient.eq_iff_equiv

/-! ## Realization in `ℂ1 + J` -/

variable (G : TracialTwoGauge D) {r : ℕ → ℝ}
  (hr : IsCoordinateNormComparison G r)

include hr

/-- Existence of a realization in `ℂ1 + J`, retaining both coordinatewise
operator-norm convergence and uniform-two convergence. -/
private theorem exists_realization (a : BoundedUniformTwoCauchySequence G) :
    ∃ y : scalarPlusJSubalgebra G,
      (∀ n, Tendsto (fun k ↦ a.seq k n) atTop (nhds (y.1 n))) ∧
      UniformTwoConverges G a.seq y.1 := by
  obtain ⟨C, hC⟩ := a.norm_bounded
  obtain ⟨y, hy, hycoord, hyconv⟩ :=
    exists_mem_scalarPlusJ_of_uniformTwoCauchy G hr a.seq a.mem_base hC a.uniform_cauchy
  exact ⟨⟨y, hy⟩, hycoord, hyconv⟩

/-- The chosen concrete realization of a bounded Cauchy representative. -/
noncomputable def realizeRepresentative
    (a : BoundedUniformTwoCauchySequence G) : scalarPlusJSubalgebra G :=
  Classical.choose (exists_realization G hr a)

theorem realizeRepresentative_coord_tendsto
    (a : BoundedUniformTwoCauchySequence G) (n : ℕ) :
    Tendsto (fun k ↦ a.seq k n) atTop
      (nhds ((realizeRepresentative G hr a).1 n)) :=
  (Classical.choose_spec (exists_realization G hr a)).1 n

theorem realizeRepresentative_uniformTwoConverges
    (a : BoundedUniformTwoCauchySequence G) :
    UniformTwoConverges G a.seq (realizeRepresentative G hr a).1 :=
  (Classical.choose_spec (exists_realization G hr a)).2

/-- Uniform-two convergence implies operator-norm convergence at each fixed
coordinate, by the coordinate norm comparison. -/
theorem coordinate_tendsto_of_uniformTwoConverges
    {a : ℕ → BoundedCStarSequence D} {x : BoundedCStarSequence D}
    (h : UniformTwoConverges G a x) (n : ℕ) :
    Tendsto (fun k ↦ a k n) atTop (nhds (x n)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hR : (0 : ℝ) < max (r n) 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨K, hK⟩ := h (ε / max (r n) 1) (div_pos hε hR)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hq := hK k hk n
  have hcompare : ‖x n - a k n‖ ≤ max (r n) 1 * G.q n (x n - a k n) :=
    (hr n _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (G.nonneg n _))
  have hmul : max (r n) 1 * G.q n (x n - a k n)
      < max (r n) 1 * (ε / max (r n) 1) :=
    mul_lt_mul_of_pos_left hq hR
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖x n - a k n‖ ≤ max (r n) 1 * G.q n (x n - a k n) := hcompare
    _ < max (r n) 1 * (ε / max (r n) 1) := hmul
    _ = ε := mul_div_cancel₀ ε hR.ne'

/-- A representative has at most one uniform-two limit in the bounded
product. -/
theorem uniformTwoLimit_unique (a : BoundedUniformTwoCauchySequence G)
    {x : BoundedCStarSequence D} (hx : UniformTwoConverges G a.seq x) :
    (realizeRepresentative G hr a).1 = x := by
  apply Subtype.ext
  funext n
  exact tendsto_nhds_unique
    (realizeRepresentative_coord_tendsto G hr a n)
    (coordinate_tendsto_of_uniformTwoConverges G hr hx n)

/-- Uniform-two equivalent representatives have the same concrete
realization. -/
theorem realizeRepresentative_eq_of_equivalent
    {a b : BoundedUniformTwoCauchySequence G}
    (hab : UniformTwoEquivalent G a.seq b.seq) :
    realizeRepresentative G hr a = realizeRepresentative G hr b := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  have hdiff : Tendsto (fun k ↦ a.seq k n - b.seq k n) atTop (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hR : (0 : ℝ) < max (r n) 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    obtain ⟨K, hK⟩ := hab (ε / max (r n) 1) (div_pos hε hR)
    filter_upwards [eventually_ge_atTop K] with k hk
    have hq := hK k hk n
    have hcompare : ‖a.seq k n - b.seq k n‖
        ≤ max (r n) 1 * G.q n (a.seq k n - b.seq k n) :=
      (hr n _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (G.nonneg n _))
    rw [dist_zero_right]
    calc
      ‖a.seq k n - b.seq k n‖
          ≤ max (r n) 1 * G.q n (a.seq k n - b.seq k n) := hcompare
      _ < max (r n) 1 * (ε / max (r n) 1) := mul_lt_mul_of_pos_left hq hR
      _ = ε := mul_div_cancel₀ ε hR.ne'
  have hlimit : Tendsto (fun k ↦ a.seq k n - b.seq k n) atTop
      (nhds ((realizeRepresentative G hr a).1 n
        - (realizeRepresentative G hr b).1 n)) :=
    (realizeRepresentative_coord_tendsto G hr a n).sub
      (realizeRepresentative_coord_tendsto G hr b n)
  exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hdiff)

/-- Conversely, equality of realizations forces uniform-two-null difference
of the representatives. -/
theorem equivalent_of_realizeRepresentative_eq
    {a b : BoundedUniformTwoCauchySequence G}
    (h : realizeRepresentative G hr a = realizeRepresentative G hr b) :
    UniformTwoEquivalent G a.seq b.seq := by
  intro ε hε
  obtain ⟨K₁, hK₁⟩ :=
    realizeRepresentative_uniformTwoConverges G hr a (ε / 2) (half_pos hε)
  obtain ⟨K₂, hK₂⟩ :=
    realizeRepresentative_uniformTwoConverges G hr b (ε / 2) (half_pos hε)
  refine ⟨max K₁ K₂, fun k hk n ↦ ?_⟩
  have h₁ := hK₁ k ((le_max_left K₁ K₂).trans hk) n
  have h₂ := hK₂ k ((le_max_right K₁ K₂).trans hk) n
  have ht := G.sub_le_sub_add_sub n (a.seq k n)
    ((realizeRepresentative G hr a).1 n) (b.seq k n)
  have hs : G.q n (a.seq k n - (realizeRepresentative G hr a).1 n)
      = G.q n ((realizeRepresentative G hr a).1 n - a.seq k n) :=
    G.sub_comm_eq n _ _
  have h₂' : G.q n ((realizeRepresentative G hr a).1 n - b.seq k n) < ε / 2 := by
    rw [h]
    exact h₂
  linarith [ht, hs, h₁, h₂']

theorem equivalent_iff_realizeRepresentative_eq
    (a b : BoundedUniformTwoCauchySequence G) :
    UniformTwoEquivalent G a.seq b.seq ↔
      realizeRepresentative G hr a = realizeRepresentative G hr b :=
  ⟨realizeRepresentative_eq_of_equivalent G hr,
    equivalent_of_realizeRepresentative_eq G hr⟩

/-- Realization descends to the actual Cauchy quotient. -/
noncomputable def realize :
    BoundedUniformTwoCompletion G r hr → scalarPlusJSubalgebra G :=
  Quotient.lift (realizeRepresentative G hr)
    (fun _ _ hab ↦ realizeRepresentative_eq_of_equivalent G hr hab)

@[simp] theorem realize_completionMk
    (a : BoundedUniformTwoCauchySequence G) :
    realize G hr (completionMk G hr a) = realizeRepresentative G hr a := rfl

theorem realize_injective : Function.Injective (realize G hr) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      apply (completionMk_eq_iff hr a b).2
      exact (equivalent_iff_realizeRepresentative_eq G hr a b).2 hxy

/-- Every element of `ℂ1 + J` has a bounded Cauchy representative from the
unitized `c₀`-sum, supplied explicitly by scalar truncations upstream. -/
private theorem exists_representative_converging
    (x : scalarPlusJSubalgebra G) :
    ∃ a : BoundedUniformTwoCauchySequence G, UniformTwoConverges G a.seq x.1 := by
  obtain ⟨a, C, hA, hC, hcauchy, hconv⟩ :=
    exists_uniformTwoCauchy_scalarTruncations G x.2
  exact ⟨⟨a, hA, ⟨C, hC⟩, hcauchy⟩, hconv⟩

theorem realize_surjective : Function.Surjective (realize G hr) := by
  intro x
  obtain ⟨a, ha⟩ := exists_representative_converging G hr x
  refine ⟨completionMk G hr a, ?_⟩
  rw [realize_completionMk]
  apply Subtype.ext
  exact uniformTwoLimit_unique G hr a ha

/-- The bounded uniform-two Cauchy quotient is genuinely equivalent, as a
type, to the concrete sequence algebra `ℂ1 + J`. -/
noncomputable def realizationEquiv :
    BoundedUniformTwoCompletion G r hr ≃ scalarPlusJSubalgebra G :=
  Equiv.ofBijective (realize G hr) ⟨realize_injective G hr, realize_surjective G hr⟩

@[simp] theorem realizationEquiv_apply (x : BoundedUniformTwoCompletion G r hr) :
    realizationEquiv G hr x = realize G hr x := rfl

/-! ## The transported C-star structure -/

/-- The concrete closed star subalgebra `ℂ1 + J` is a C-star algebra. -/
noncomputable instance scalarPlusJSubalgebraCStarAlgebra :
    CStarAlgebra (scalarPlusJSubalgebra G) :=
  { toNormedRing := inferInstance
    toStarRing := inferInstance
    toCompleteSpace := (isClosed_scalarPlusJ G).completeSpace_coe
    toCStarRing := inferInstance
    toNormedAlgebra := inferInstance
    toStarModule := inferInstance }

noncomputable instance boundedUniformTwoCompletionRing :
    Ring (BoundedUniformTwoCompletion G r hr) := (realizationEquiv G hr).ring

noncomputable instance boundedUniformTwoCompletionAlgebra :
    Algebra ℂ (BoundedUniformTwoCompletion G r hr) :=
  Equiv.algebra ℂ (realizationEquiv G hr)

noncomputable instance boundedUniformTwoCompletionStar :
    Star (BoundedUniformTwoCompletion G r hr) := (realizationEquiv G hr).star

noncomputable instance boundedUniformTwoCompletionStarRing :
    StarRing (BoundedUniformTwoCompletion G r hr) := (realizationEquiv G hr).starRing

noncomputable instance boundedUniformTwoCompletionNormedRing :
    NormedRing (BoundedUniformTwoCompletion G r hr) := (realizationEquiv G hr).normedRing

@[simp] theorem norm_realizationEquiv (x : BoundedUniformTwoCompletion G r hr) :
    ‖realizationEquiv G hr x‖ = ‖x‖ := rfl

noncomputable instance boundedUniformTwoCompletionNormedAlgebra :
    NormedAlgebra ℂ (BoundedUniformTwoCompletion G r hr) :=
  NormedAlgebra.induced ℂ (BoundedUniformTwoCompletion G r hr)
    (scalarPlusJSubalgebra G) (Equiv.algEquiv ℂ (realizationEquiv G hr))

noncomputable instance boundedUniformTwoCompletionCompleteSpace :
    CompleteSpace (BoundedUniformTwoCompletion G r hr) :=
  (completeSpace_congr
    (show IsUniformEmbedding (realizationEquiv G hr) from
      (show Isometry (realizationEquiv G hr) from fun _ _ ↦ rfl).isUniformEmbedding)).2
    inferInstance

noncomputable instance boundedUniformTwoCompletionStarModule :
    StarModule ℂ (BoundedUniformTwoCompletion G r hr) :=
  (realizationEquiv G hr).starModule ℂ

noncomputable instance boundedUniformTwoCompletionCStarRing :
    CStarRing (BoundedUniformTwoCompletion G r hr) where
  norm_mul_self_le x := by
    rw [← norm_realizationEquiv G hr x,
      ← norm_realizationEquiv G hr (star x * x)]
    change ‖realizationEquiv G hr x‖ * ‖realizationEquiv G hr x‖ ≤
      ‖star (realizationEquiv G hr x) * realizationEquiv G hr x‖
    exact CStarRing.norm_mul_self_le _

/-- The actual Cauchy quotient carries the C-star structure transported from
its uniquely proved concrete realization. -/
noncomputable instance boundedUniformTwoCompletionCStarAlgebra :
    CStarAlgebra (BoundedUniformTwoCompletion G r hr) :=
  { toNormedRing := boundedUniformTwoCompletionNormedRing G hr
    toStarRing := boundedUniformTwoCompletionStarRing G hr
    toCompleteSpace := boundedUniformTwoCompletionCompleteSpace G hr
    toCStarRing := boundedUniformTwoCompletionCStarRing G hr
    toNormedAlgebra := boundedUniformTwoCompletionNormedAlgebra G hr
    toStarModule := boundedUniformTwoCompletionStarModule G hr }

/-- The realization of the bounded uniform-two Cauchy quotient as
`scalarPlusJSubalgebra G`, now bundled at the full star-algebra level. -/
noncomputable def realizationStarAlgEquiv :
    BoundedUniformTwoCompletion G r hr ≃⋆ₐ[ℂ] scalarPlusJSubalgebra G :=
  { realizationEquiv G hr with
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    map_star' := fun _ ↦ rfl
    map_smul' := fun c x ↦
      map_smul (Equiv.algEquiv ℂ (realizationEquiv G hr)) c x }

@[simp] theorem realizationStarAlgEquiv_apply
    (x : BoundedUniformTwoCompletion G r hr) :
    realizationStarAlgEquiv G hr x = realize G hr x := by
  exact realizationEquiv_apply G hr x

end

end UniformTracialBoundedCauchyQuotient
end GroupApproximation
