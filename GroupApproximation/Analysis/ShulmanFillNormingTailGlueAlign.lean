import GroupApproximation.Analysis.ShulmanFillNormingTailPair
import GroupApproximation.Analysis.ShulmanFillNormingTailSeqHom

/-!
# Aligning two tail lifts at one cut, and the limit map on the coordinates

The gluing needs the two legs to be `*`-homomorphisms into *the same* algebra.
`sHom φ` lands in the reduced product over `fun t ↦ ShiftedD ι hnorm hone φ.cut t`,
so two lifts glue only once their cuts agree --- and as structures they carry
their own.

Nothing has to be assumed about that.  A lift can always be re-cut upwards:
`TailNull.mono_cut` says a larger cut asks for less, so replacing `cut` by any
pointwise larger function leaves every clause true.  `withCut` is that structure
update, and two lifts align at the pointwise maximum of their cuts.  This is why
`UnitalTailPairPackageStatement`'s shared-cut clause is a convenience rather than a
requirement: a consumer that does not have it can make it.

The module also carries the limit map on a coordinate algebra.  `ShiftedD` is
opaque, so `starStrongLimitHom` of the relabelled data has to be exposed through
it once, as `ShiftedD.limitHom`; `limitHom_mk` is the `rfl` lemma that connects
it to `Analysis/ShulmanFillNormingTailShiftLimit`, where the relabelled limit was
shown to be the original one.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

section Align

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- **A tail lift can be re-cut upwards.**  Every clause is the old one read
past a larger cut, which asks for less. -/
def StarStrongTailLift.withCut (φ : StarStrongTailLift ι hnorm hone π)
    (c : ℕ → ℕ) (hc : ∀ t, φ.cut t ≤ c t) :
    StarStrongTailLift ι hnorm hone π where
  toFun := φ.toFun
  cut := c
  mem := φ.mem
  norm_le := φ.norm_le
  tail_add b d := (φ.tail_add b d).mono_cut hc
  tail_smul z b := (φ.tail_smul z b).mono_cut hc
  tail_mul b d := (φ.tail_mul b d).mono_cut hc
  tail_star b := (φ.tail_star b).mono_cut hc
  tail_one := φ.tail_one.mono_cut hc
  tendsto_lift := φ.tendsto_lift

@[simp] theorem StarStrongTailLift.withCut_cut
    (φ : StarStrongTailLift ι hnorm hone π) (c : ℕ → ℕ)
    (hc : ∀ t, φ.cut t ≤ c t) : (φ.withCut c hc).cut = c := rfl

@[simp] theorem StarStrongTailLift.withCut_toFun
    (φ : StarStrongTailLift ι hnorm hone π) (c : ℕ → ℕ)
    (hc : ∀ t, φ.cut t ≤ c t) : (φ.withCut c hc).toFun = φ.toFun := rfl

/-- **Two lifts, aligned at the pointwise maximum of their cuts.**

The two may lift different representations, of different algebras: only their
cuts are read.  That generality is the point rather than a flourish --- the
gluing's two legs lift `ρ₁` and `ρ₂`, so a version stated for two lifts of one
representation cannot be applied to them. -/
def commonCut {B₁ B₂ : Type v} [CStarAlgebra B₁] [CStarAlgebra B₂]
    {π₁ : B₁ →⋆ₐ[ℂ] (H →L[ℂ] H)} {π₂ : B₂ →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongTailLift ι hnorm hone π₁)
    (φ₂ : StarStrongTailLift ι hnorm hone π₂) : ℕ → ℕ :=
  fun t ↦ max (φ₁.cut t) (φ₂.cut t)

theorem le_commonCut_left {B₁ B₂ : Type v} [CStarAlgebra B₁] [CStarAlgebra B₂]
    {π₁ : B₁ →⋆ₐ[ℂ] (H →L[ℂ] H)} {π₂ : B₂ →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongTailLift ι hnorm hone π₁)
    (φ₂ : StarStrongTailLift ι hnorm hone π₂) (t : ℕ) :
    φ₁.cut t ≤ commonCut φ₁ φ₂ t := le_max_left _ _

theorem le_commonCut_right {B₁ B₂ : Type v} [CStarAlgebra B₁] [CStarAlgebra B₂]
    {π₁ : B₁ →⋆ₐ[ℂ] (H →L[ℂ] H)} {π₂ : B₂ →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongTailLift ι hnorm hone π₁)
    (φ₂ : StarStrongTailLift ι hnorm hone π₂) (t : ℕ) :
    φ₂.cut t ≤ commonCut φ₁ φ₂ t := le_max_right _ _

variable (ι hnorm hone)

/-- **The `*`-strong limit on a coordinate algebra**, exposed through the opaque
`ShiftedD`. -/
def ShiftedD.limitHom (c : ℕ → ℕ) (t : ℕ) :
    ShiftedD ι hnorm hone c t →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  StarStrong.starStrongLimitHom (shiftIota ι (c t))
    (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))

variable {ι hnorm hone}

theorem ShiftedD.limitHom_mk (c : ℕ → ℕ) (t : ℕ)
    {x : StarStrong.BoundedStarSequence (shiftModel (A := A) (c t))}
    {hx : x ∈ StarStrong.starStrongSubalgebra (shiftIota ι (c t))
      (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))} :
    ShiftedD.limitHom ι hnorm hone c t (ShiftedD.mk ι hnorm hone c t x hx)
      = StarStrong.starStrongLimit (shiftIota ι (c t))
        (shiftIota_norm_le ι hnorm (c t)) (shiftIota_hone ι hone (c t))
        ⟨x, hx⟩ := rfl

/-- **The coordinate limits of a relabelled lift are the limits it started
with.**  `Analysis/ShulmanFillNormingTailShiftLimit` in the shape the gluing
consumes. -/
theorem limitHom_sSeq (φ : StarStrongTailLift ι hnorm hone π) (b : B) (t : ℕ) :
    ShiftedD.limitHom ι hnorm hone φ.cut t (sSeq φ b t)
      = StarStrong.starStrongLimit ι hnorm hone ⟨φ.toFun t b, φ.mem t b⟩ := by
  rw [show sSeq φ b t = ShiftedD.mk ι hnorm hone φ.cut t
      (shiftSeq (A := A) (φ.cut t) (φ.toFun t b))
      (shiftSeq_mem ι hnorm hone (φ.cut t) (φ.mem t b)) from rfl,
    ShiftedD.limitHom_mk]
  exact starStrongLimit_shiftSeq ι hnorm hone (φ.cut t) (φ.mem t b)

end Align

end

end ShulmanFill
end GroupApproximation
