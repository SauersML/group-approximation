import GroupApproximation.Analysis.ShulmanFillNormingSeqHom
import GroupApproximation.Analysis.ShulmanFillNormingTailShiftLimit

/-!
# A tail lift as a unital `*`-homomorphism into a reduced product

`ShulmanFill.StarStrongAsymptoticLift.dHom` turns a lift into a unital
`*`-homomorphism `B → ∏_t 𝒟 / ⨁_t 𝒟`, which is what the gluing of
`Analysis/ShulmanFillNormingGluing` factors through.  Its clauses need the
defects to vanish in the norm of `𝒟`, and a `StarStrongTailLift` controls them
only past its cut.

Relabelling closes the gap without a corner.  At stage `t` the sequence is read
past `cut t` and reindexed, landing in the `𝒟` of the relabelled data, and

* the defects become norm-null there, by `tendsto_norm_shiftSeq_of_tailNull`;
* the unit is preserved, because relabelling is a unital `*`-homomorphism of
  bounded products --- the whole reason for relabelling rather than truncating;
* the `*`-strong limit is untouched, by `starStrongLimit_shiftSeq`.

## Why the coordinate algebra is an opaque `def` with an API

The cut has to grow --- a constant one would fix a coordinate and the character
argument of `Analysis/ShulmanFillNormingPrintedPairCharacter` would apply there
--- so the coordinate algebras genuinely vary with `t`, which is what `dHom`'s
constant family never had to face.  Written transparently, `One`, `Zero` and
`Add` on `↥(starStrongSubalgebra (shiftIota ι (c t)) …)` are found only by
unfolding the subalgebra's closure instances afresh at every `t`, and the search
does not terminate.

So `ShiftedD` is a `def`, opaque, with its instances pinned once by
`inferInstanceAs` --- the `cStarAlgebraDoubledEllTwo` idiom of
`Analysis/ShulmanFillNormingEllTwoModels`.  Opacity costs the subtype
coercions, so the def comes with `mk` and `val` and the handful of `rfl` lemmas
that relate them.  Everything below goes through that API and never rewrites
across the def: `exact` and `show` cross it at default transparency, `rw` does
not.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

section TailSeqHom

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- The `t`-th coordinate algebra: the `𝒟` of the data relabelled past `c t`,
kept opaque so that instance search never unfolds it. -/
def ShiftedD (c : ℕ → ℕ) (t : ℕ) : Type u :=
  StarStrong.starStrongSubalgebra (shiftIota ι (c t))
    (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))

noncomputable instance cStarAlgebraShiftedD (c : ℕ → ℕ) (t : ℕ) :
    CStarAlgebra (ShiftedD ι hnorm hone c t) :=
  inferInstanceAs (CStarAlgebra (StarStrong.starStrongSubalgebra
    (shiftIota ι (c t)) (shiftIota_norm_le ι hnorm (c t))
    (shiftIota_hone ι hone (c t))))

instance nontrivialShiftedD (c : ℕ → ℕ) (t : ℕ) :
    Nontrivial (ShiftedD ι hnorm hone c t) :=
  inferInstanceAs (Nontrivial (StarStrong.starStrongSubalgebra
    (shiftIota ι (c t)) (shiftIota_norm_le ι hnorm (c t))
    (shiftIota_hone ι hone (c t))))

/-- An element of the coordinate algebra, from a sequence in `𝒟`. -/
def ShiftedD.mk (c : ℕ → ℕ) (t : ℕ)
    (x : StarStrong.BoundedStarSequence (shiftModel (A := A) (c t)))
    (hx : x ∈ StarStrong.starStrongSubalgebra (shiftIota ι (c t))
      (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))) :
    ShiftedD ι hnorm hone c t := ⟨x, hx⟩

/-- The underlying sequence of an element of the coordinate algebra. -/
def ShiftedD.val (c : ℕ → ℕ) (t : ℕ) (y : ShiftedD ι hnorm hone c t) :
    StarStrong.BoundedStarSequence (shiftModel (A := A) (c t)) := Subtype.val y

variable {ι hnorm hone}

@[simp] theorem ShiftedD.val_mk (c : ℕ → ℕ) (t : ℕ)
    {x : StarStrong.BoundedStarSequence (shiftModel (A := A) (c t))}
    {hx : x ∈ StarStrong.starStrongSubalgebra (shiftIota ι (c t))
      (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))} :
    ShiftedD.val ι hnorm hone c t (ShiftedD.mk ι hnorm hone c t x hx) = x := rfl

theorem ShiftedD.norm_val (c : ℕ → ℕ) (t : ℕ)
    (y : ShiftedD ι hnorm hone c t) :
    ‖y‖ = ‖ShiftedD.val ι hnorm hone c t y‖ := rfl

theorem ShiftedD.val_sub (c : ℕ → ℕ) (t : ℕ)
    (y z : ShiftedD ι hnorm hone c t) :
    ShiftedD.val ι hnorm hone c t (y - z)
      = ShiftedD.val ι hnorm hone c t y - ShiftedD.val ι hnorm hone c t z := rfl

variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The relabelled sequence of a tail lift, stage by stage. -/
def sSeq (φ : StarStrongTailLift ι hnorm hone π) (b : B) :
    BoundedCStarSequence (fun t ↦ ShiftedD ι hnorm hone φ.cut t) :=
  ⟨fun t ↦ ShiftedD.mk ι hnorm hone φ.cut t
      (shiftSeq (A := A) (φ.cut t) (φ.toFun t b))
      (shiftSeq_mem ι hnorm hone (φ.cut t) (φ.mem t b)),
    memℓp_infty ⟨‖b‖, by
      rintro _ ⟨t, rfl⟩
      beta_reduce
      rw [ShiftedD.norm_val, ShiftedD.val_mk]
      exact norm_shiftSeq_le (φ.cut t) (φ.toFun t b) (norm_nonneg b)
        (fun n _ ↦ (lp.norm_apply_le_norm ENNReal.top_ne_zero
          (φ.toFun t b) n).trans (φ.norm_le t b))⟩⟩

@[simp] theorem val_sSeq_apply (φ : StarStrongTailLift ι hnorm hone π) (b : B)
    (t : ℕ) :
    ShiftedD.val ι hnorm hone φ.cut t (sSeq φ b t)
      = shiftSeq (A := A) (φ.cut t) (φ.toFun t b) := rfl

/-- The class of the relabelled sequence in the reduced product. -/
def sClass (φ : StarStrongTailLift ι hnorm hone π) (b : B) :
    CStarProductCorona (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite :=
  cStarProductCoronaQuotient (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite
    (sSeq φ b)

/-- **The transfer lemma for every defect.**  A defect controlled past the cut
is norm-null once relabelled there, so the two classes agree. -/
theorem sClass_eq_of_tailNull (φ : StarStrongTailLift ι hnorm hone π)
    (u v : ℕ → StarStrong.BoundedStarSequence A)
    (x y : BoundedCStarSequence (fun t ↦ ShiftedD ι hnorm hone φ.cut t))
    (hx : ∀ t, ShiftedD.val ι hnorm hone φ.cut t (x t)
      = shiftSeq (A := A) (φ.cut t) (u t))
    (hy : ∀ t, ShiftedD.val ι hnorm hone φ.cut t (y t)
      = shiftSeq (A := A) (φ.cut t) (v t))
    (h : TailNull φ.cut (fun t ↦ u t - v t)) :
    cStarProductCoronaQuotient (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite x
      = cStarProductCoronaQuotient (fun t ↦ ShiftedD ι hnorm hone φ.cut t)
          cofinite y := by
  refine cStarProductCoronaQuotient_eq_of_tendsto_norm_sub x y ?_
  refine (tendsto_norm_shiftSeq_of_tailNull h).congr fun t ↦ ?_
  rw [ShiftedD.norm_val, ShiftedD.val_sub, hx t, hy t, ← map_sub]

variable (φ : StarStrongTailLift ι hnorm hone π)

theorem sClass_one : sClass φ (1 : B) = 1 := by
  have hone' : (1 : CStarProductCorona
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite)
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite 1 :=
    (map_one (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite)).symm
  rw [sClass, hone']
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t 1) (fun _ ↦ 1)
    (sSeq φ 1) 1 (fun t ↦ val_sSeq_apply φ 1 t) (fun t ↦ ?_) φ.tail_one
  exact (map_one (shiftSeq (A := A) (φ.cut t))).symm

theorem sClass_zero : sClass φ (0 : B) = 0 := by
  have hz : TailNull φ.cut
      (fun t ↦ φ.toFun t (0 : B) - (0 : StarStrong.BoundedStarSequence A)) := by
    intro ε hε
    refine Eventually.of_forall fun t ↦ ?_
    intro n _hn
    have h0 : φ.toFun t (0 : B) = 0 := by
      have hle : ‖φ.toFun t (0 : B)‖ ≤ 0 := by simpa using φ.norm_le t 0
      exact norm_le_zero_iff.mp hle
    beta_reduce
    rw [h0, sub_zero]
    simpa using hε.le
  have hzero' : (0 : CStarProductCorona
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite)
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite 0 :=
    (map_zero (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite)).symm
  rw [sClass, hzero']
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t 0) (fun _ ↦ 0)
    (sSeq φ 0) 0 (fun t ↦ val_sSeq_apply φ 0 t) (fun t ↦ ?_) hz
  exact (map_zero (shiftSeq (A := A) (φ.cut t))).symm

theorem sClass_add (b c : B) : sClass φ (b + c) = sClass φ b + sClass φ c := by
  have hz : TailNull φ.cut
      (fun t ↦ φ.toFun t (b + c) - (φ.toFun t b + φ.toFun t c)) := by
    refine (φ.tail_add b c).mono fun t n ↦ ?_
    rw [show φ.toFun t (b + c) - (φ.toFun t b + φ.toFun t c)
      = φ.toFun t (b + c) - φ.toFun t b - φ.toFun t c from by abel]
  have hadd : sClass φ b + sClass φ c
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite (sSeq φ b + sSeq φ c) :=
    (map_add (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite) _ _).symm
  rw [sClass, hadd]
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t (b + c))
    (fun t ↦ φ.toFun t b + φ.toFun t c) (sSeq φ (b + c)) (sSeq φ b + sSeq φ c)
    (fun t ↦ val_sSeq_apply φ (b + c) t) (fun t ↦ ?_) hz
  exact (map_add (shiftSeq (A := A) (φ.cut t)) _ _).symm

theorem sClass_mul (b c : B) : sClass φ (b * c) = sClass φ b * sClass φ c := by
  have hmul : sClass φ b * sClass φ c
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite (sSeq φ b * sSeq φ c) :=
    (map_mul (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite) _ _).symm
  rw [sClass, hmul]
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t (b * c))
    (fun t ↦ φ.toFun t b * φ.toFun t c) (sSeq φ (b * c)) (sSeq φ b * sSeq φ c)
    (fun t ↦ val_sSeq_apply φ (b * c) t) (fun t ↦ ?_) (φ.tail_mul b c)
  exact (map_mul (shiftSeq (A := A) (φ.cut t)) _ _).symm

theorem sClass_smul (z : ℂ) (b : B) : sClass φ (z • b) = z • sClass φ b := by
  have hsm : z • sClass φ b
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite (z • sSeq φ b) :=
    (map_smul (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite) _ _).symm
  rw [sClass, hsm]
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t (z • b))
    (fun t ↦ z • φ.toFun t b) (sSeq φ (z • b)) (z • sSeq φ b)
    (fun t ↦ val_sSeq_apply φ (z • b) t) (fun t ↦ ?_) (φ.tail_smul z b)
  exact (map_smul (shiftSeq (A := A) (φ.cut t)) z _).symm

theorem sClass_star (b : B) : sClass φ (star b) = star (sClass φ b) := by
  have hst : star (sClass φ b)
      = cStarProductCoronaQuotient
        (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite (star (sSeq φ b)) :=
    (map_star (cStarProductCoronaQuotient
      (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite) _).symm
  rw [sClass, hst]
  refine sClass_eq_of_tailNull φ (fun t ↦ φ.toFun t (star b))
    (fun t ↦ star (φ.toFun t b)) (sSeq φ (star b)) (star (sSeq φ b))
    (fun t ↦ val_sSeq_apply φ (star b) t) (fun t ↦ ?_) (φ.tail_star b)
  exact (map_star (shiftSeq (A := A) (φ.cut t)) _).symm

/-- **A tail lift, as a unital `*`-homomorphism into `∏_t 𝒟_{cut t} / ⨁_t`.**
Unital because relabelling is, which is exactly what the corner construction
would have had to buy back. -/
def sHom : B →⋆ₐ[ℂ]
    CStarProductCorona (fun t ↦ ShiftedD ι hnorm hone φ.cut t) cofinite where
  toFun := sClass φ
  map_one' := sClass_one φ
  map_mul' := sClass_mul φ
  map_zero' := sClass_zero φ
  map_add' := sClass_add φ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      sClass_smul φ r 1, sClass_one φ]
  map_star' := sClass_star φ

@[simp] theorem sHom_apply (b : B) : sHom φ b = sClass φ b := rfl

end TailSeqHom

end

end ShulmanFill
end GroupApproximation
