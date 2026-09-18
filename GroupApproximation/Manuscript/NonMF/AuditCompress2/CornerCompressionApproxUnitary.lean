import GroupApproximation.Analysis.CollapseUnitaryLift
import GroupApproximation.Analysis.CollapseProjectionLift
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner compressions of a corona homomorphism are approximately unitary

`non_mf_groups_exist.tex`, lines 621–624:

> Restricting a corona homomorphism $\rho$ to a corner requires a
> correction: a projection $q$ commuting with $\rho(G)$ has lifts $q_n$
> that commute only asymptotically with unitary lifts $U_n(g)$ of
> $\rho(g)$, so the compressions $q_nU_n(g)q_n$ are only approximately
> unitary in the matrix corners.

The earlier row decl took a `PrintedCornerData` carrier. This module states
the sentence about the concrete objects: a group homomorphism `ρ` into the
unitary group of the norm matrix corona `∏ M_{X n} / ⊕ M_{X n}`, and a
projection `q` of that corona commuting with every `ρ g`.

The statement has three parts:

* `q` has lifts `q_n` that are orthogonal projection matrices (this is
  `CollapseProjectionLift.exists_projection_lift`);
* every `ρ g` has unitary lifts `U_n(g)` (this is
  `CollapseUnitaryLift.unitarySequenceToCorona_surjective`);
* for *every* such pair of lifts, `‖U_n q_n - q_n U_n‖ → 0`, and the corner
  compression `c_n = q_n U_n q_n` satisfies `‖c_n^* c_n - q_n‖ → 0` and
  `‖c_n c_n^* - q_n‖ → 0`. That is the printed "approximately unitary in the
  matrix corners", since `q_n` is the unit of the corner `q_n M q_n`.

Proof route: in the corona, `q ρ(g) q` is a unitary of the corner `q A q`.
That is pure ring algebra (`corner_isUnitaryInCorner`). Each of the three
defects is a bounded sequence whose class in the corona is `0`, and
`normMatrixCStarCoronaMk_eq_zero_iff` turns a vanishing class into a norm
sequence tending to `0`.

The words "requires a correction" and "only" are motivational. The
formalized content is the positive asymptotic statement; no exactness
counterexample is claimed.
-/

open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation.Manuscript.NonMF.AuditCompress2

universe u

/-- A bounded matrix sequence with vanishing corona class has operator norms
tending to `0` along `atTop`. -/
theorem tendsto_coord_norm_of_mk_eq_zero (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence (fun n ↦ X n))
    (h : normMatrixCStarCoronaMk (fun n ↦ X n) a = 0) :
    Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0) := by
  have hnull := (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) a).mp h
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at hnull
  exact hnull

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditCompress2.tendsto_coord_norm_of_mk_eq_zero

/-- In any star ring, if a projection `q` commutes with a unitary `r`, then
`q r q` is a unitary of the corner `q A q`. -/
theorem corner_isUnitaryInCorner {A : Type*} [Ring A] [StarRing A] {q r : A}
    (hsa : star q = q) (hidem : q * q = q) (hcomm : q * r = r * q)
    (hr : star r * r = 1) (hr' : r * star r = 1) :
    star (q * r * q) * (q * r * q) = q ∧ q * r * q * star (q * r * q) = q := by
  have hqrq : q * r * q = r * q := by rw [hcomm, mul_assoc, hidem]
  have hcomm' : q * star r = star r * q := by
    have h := congrArg (star : A → A) hcomm
    rw [star_mul, star_mul, hsa] at h
    exact h.symm
  have hstar : star (q * r * q) = star r * q := by
    rw [hqrq, star_mul, hsa, hcomm']
  constructor
  · rw [hstar, hqrq]
    calc star r * q * (r * q) = star r * (q * r) * q := by noncomm_ring
      _ = star r * r * (q * q) := by rw [hcomm]; noncomm_ring
      _ = q := by rw [hr, one_mul, hidem]
  · rw [hstar, hqrq]
    calc r * q * (star r * q) = r * (q * star r) * q := by noncomm_ring
      _ = r * star r * (q * q) := by rw [hcomm']; noncomm_ring
      _ = q := by rw [hr', one_mul, hidem]

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditCompress2.corner_isUnitaryInCorner

/-- **tex 621–624.** Let `ρ` be a homomorphism from `G` into the unitaries of
the norm matrix corona, and let `q` be a projection commuting with `ρ(G)`.
Then `q` has projection-matrix lifts `q_n`, and each `ρ g` has unitary lifts
`U_n(g)`. For any such lifts, `q_n` and `U_n(g)` commute asymptotically, and
the compressions `q_n U_n(g) q_n` are asymptotically unitary in the corners
`q_n M_{X n} q_n`. -/
theorem manuscriptSentence_cornerCompressionsOnlyApproximatelyUnitary
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {G : Type u} [Group G]
    (ρ : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hsa : star q = q) (hidem : q * q = q)
    (hcomm : ∀ g : G,
      q * (ρ g : NormMatrixCStarCorona (fun n ↦ X n)) =
        (ρ g : NormMatrixCStarCorona (fun n ↦ X n)) * q) :
    (∃ Q : BoundedMatrixSequence (fun n ↦ X n),
        (∀ n, (Q n : Matrix (X n) (X n) ℂ)ᴴ = Q n ∧
          (Q n : Matrix (X n) (X n) ℂ) * Q n = Q n) ∧
        normMatrixCStarCoronaMk (fun n ↦ X n) Q = q) ∧
      (∀ g : G, ∃ U : ∀ n, Matrix.unitaryGroup (X n) ℂ,
        unitarySequenceToCorona X U = ρ g) ∧
      ∀ Q : BoundedMatrixSequence (fun n ↦ X n),
        normMatrixCStarCoronaMk (fun n ↦ X n) Q = q →
        ∀ (g : G) (U : ∀ n, Matrix.unitaryGroup (X n) ℂ),
          unitarySequenceToCorona X U = ρ g →
          Tendsto (fun n ↦ ‖(U n : Matrix (X n) (X n) ℂ) * Q n -
              Q n * (U n : Matrix (X n) (X n) ℂ)‖) atTop (nhds 0) ∧
          Tendsto (fun n ↦
              ‖star ((Q n : Matrix (X n) (X n) ℂ) * (U n : Matrix (X n) (X n) ℂ) *
                  Q n) *
                ((Q n : Matrix (X n) (X n) ℂ) * (U n : Matrix (X n) (X n) ℂ) * Q n) -
                Q n‖) atTop (nhds 0) ∧
          Tendsto (fun n ↦
              ‖((Q n : Matrix (X n) (X n) ℂ) * (U n : Matrix (X n) (X n) ℂ) * Q n) *
                  star ((Q n : Matrix (X n) (X n) ℂ) *
                    (U n : Matrix (X n) (X n) ℂ) * Q n) -
                Q n‖) atTop (nhds 0) := by
  obtain ⟨Q₀, hQ₀, hQ₀mk⟩ := CollapseProjectionLift.exists_projection_lift X q hsa hidem
  refine ⟨⟨Q₀, fun n ↦ hQ₀ n, hQ₀mk⟩,
    fun g ↦ CollapseUnitaryLift.unitarySequenceToCorona_surjective X (ρ g), ?_⟩
  intro Q hQ g U hU
  have hU' := congrArg Subtype.val hU
  have hUmk : normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X U) =
      (ρ g : NormMatrixCStarCorona (fun n ↦ X n)) := hU'
  have hcorner := corner_isUnitaryInCorner hsa hidem (hcomm g)
    (Unitary.star_mul_self_of_mem (ρ g).property)
    (Unitary.mul_star_self_of_mem (ρ g).property)
  refine ⟨?_, ?_, ?_⟩
  · have hz : normMatrixCStarCoronaMk (fun n ↦ X n)
        (unitarySequenceBounded X U * Q - Q * unitarySequenceBounded X U) = 0 := by
      rw [map_sub, map_mul, map_mul, hUmk, hQ, hcomm g, sub_self]
    refine Tendsto.congr (fun n ↦ ?_) (tendsto_coord_norm_of_mk_eq_zero X _ hz)
    rfl
  · have hz : normMatrixCStarCoronaMk (fun n ↦ X n)
        (star (Q * unitarySequenceBounded X U * Q) *
          (Q * unitarySequenceBounded X U * Q) - Q) = 0 := by
      rw [map_sub, map_mul, ← normMatrixCStarCorona_star_mk (fun n ↦ X n), map_mul,
        map_mul, hUmk, hQ, hcorner.1, sub_self]
    refine Tendsto.congr (fun n ↦ ?_) (tendsto_coord_norm_of_mk_eq_zero X _ hz)
    rfl
  · have hz : normMatrixCStarCoronaMk (fun n ↦ X n)
        ((Q * unitarySequenceBounded X U * Q) *
          star (Q * unitarySequenceBounded X U * Q) - Q) = 0 := by
      rw [map_sub, map_mul, ← normMatrixCStarCorona_star_mk (fun n ↦ X n), map_mul,
        map_mul, hUmk, hQ, hcorner.2, sub_self]
    refine Tendsto.congr (fun n ↦ ?_) (tendsto_coord_norm_of_mk_eq_zero X _ hz)
    rfl

#audit_axioms manuscriptSentence_cornerCompressionsOnlyApproximatelyUnitary

end GroupApproximation.Manuscript.NonMF.AuditCompress2
