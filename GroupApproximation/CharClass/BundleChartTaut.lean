import GroupApproximation.CharClass.BundleLineIntert
import GroupApproximation.CharClass.BundleLocalOn

/-!
# Complex vector bundles in the projection model, XXXIII: the chart carries the
tautological line, at every rank

`tautLineIsoCPOne` did this at rank one by trivialising a line through its own
column.  At general rank there is no free section, and this morning the
obstruction looked the same as for a general local `BundleIso`: the comparison
is conjugation by the intertwiner, which is invertible and not unitary.

`lineIntertIso` removes that obstruction, because the tautological line is rank
one **whatever the rank of the bundle is**.  The intertwiner to feed it is the
compression of `intert` by the standard frame, `A = Wᴴ ⬝ intert`, and both of its
hypotheses come out of facts already in the lane: `W Wᴴ = q x₀`, `intert`
intertwines, and `conjNormalize` of a rank-one projection is the line spanned by
the image.

The frame is not hidden: `stdFrame` is a named term, so `A` is writable.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section ChartTaut

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The standard frame at `x₀`, at the rank `q` has there. -/
noncomputable def chartFrame (q : Bundle X ι) (x₀ : X) (d : ℕ) (hr : q.rank x₀ = d + 1) :
    Matrix ι (Fin (d + 1)) ℂ :=
  stdFrame (q.isStarProjection x₀) (d + 1) (by rw [trace_eq_rank, hr])

/-- The `ℂP^d` component of the chart trivialisation. -/
noncomputable def chartCP (q : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet q x₀)
    (d : ℕ) (hr : q.rank x₀ = d + 1) : C(Proj (q.restrictTo V), CP d) :=
  ⟨fun z => (Bundle.projTrivStdOn q x₀ V hV d hr z).2,
    continuous_snd.comp (Bundle.projTrivStdOn q x₀ V hV d hr).continuous⟩

theorem chartCP_coe (q : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet q x₀)
    (d : ℕ) (hr : q.rank x₀ = d + 1) (z : Proj (q.restrictTo V)) :
    ((chartCP q x₀ V hV d hr z : CP d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
      = (chartFrame q x₀ d hr)ᴴ
        * conjNormalize (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)))
            (z : ↥V × Matrix ι ι ℂ).2
        * chartFrame q x₀ d hr := rfl

/-! ### The two fibre facts -/

omit [DecidableEq ι] in
/-- Conjugating by a frame and applying: if `W Wᴴ` and `R` both fix `w`, then the
compression fixes the compressed vector. -/
theorem frame_conj_mulVec {κ : Type} [Fintype κ] (W : Matrix ι κ ℂ) (Q R : Matrix ι ι ℂ)
    (w : ι → ℂ) (hW : W * Wᴴ = Q) (hQ : Q *ᵥ w = w) (hR : R *ᵥ w = w) :
    (Wᴴ * R * W) *ᵥ (Wᴴ *ᵥ w) = Wᴴ *ᵥ w := by
  rw [Matrix.mulVec_mulVec]
  calc ((Wᴴ * R * W) * Wᴴ) *ᵥ w
      = (Wᴴ * (R * (W * Wᴴ))) *ᵥ w := by simp only [Matrix.mul_assoc]
    _ = (Wᴴ * (R * Q)) *ᵥ w := by rw [hW]
    _ = Wᴴ *ᵥ (R *ᵥ (Q *ᵥ w)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = Wᴴ *ᵥ w := by rw [hQ, hR]


omit [DecidableEq ι] in
theorem base_mulVec_fixed (q : Bundle X ι) (V : Set X) (z : Proj (q.restrictTo V))
    {v : ι → ℂ} (hv : (z : ↥V × Matrix ι ι ℂ).2 *ᵥ v = v) :
    q (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v = v := by
  have habs : q (((z : ↥V × Matrix ι ι ℂ).1 : X)) * (z : ↥V × Matrix ι ι ℂ).2
      = (z : ↥V × Matrix ι ι ℂ).2 := z.2.2.2.2
  rw [← hv, Matrix.mulVec_mulVec, habs]

omit [DecidableEq ι] in
theorem frame_mulVec_ne_zero (q : Bundle X ι) (x₀ : X) (d : ℕ) (hr : q.rank x₀ = d + 1)
    {w : ι → ℂ} (hfix : q x₀ *ᵥ w = w) (hw : w ≠ 0) :
    (chartFrame q x₀ d hr)ᴴ *ᵥ w ≠ 0 := by
  intro h0
  refine hw ?_
  have hWW : chartFrame q x₀ d hr * (chartFrame q x₀ d hr)ᴴ = q x₀ :=
    stdFrame_mul_conjTranspose (q.isStarProjection x₀) (d + 1) _
  calc w = q x₀ *ᵥ w := hfix.symm
    _ = (chartFrame q x₀ d hr * (chartFrame q x₀ d hr)ᴴ) *ᵥ w := by rw [hWW]
    _ = chartFrame q x₀ d hr *ᵥ ((chartFrame q x₀ d hr)ᴴ *ᵥ w) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

/-- The normalised conjugate fixes the image of a fixed vector. -/
theorem conjNormalize_mulVec_self (q : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ trivSet q x₀) (z : Proj (q.restrictTo V)) {v : ι → ℂ}
    (hv : (z : ↥V × Matrix ι ι ℂ).2 *ᵥ v = v) :
    conjNormalize (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)))
        (z : ↥V × Matrix ι ι ℂ).2
      *ᵥ (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v)
      = intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v := by
  obtain ⟨u, hu, hzu⟩ := eq_rankOneProj_of_trace_one
    (isStarProjection_of_mem_projSet z.2) (trace_of_mem_projSet z.2)
  set g := intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) with hg
  have hgu : g *ᵥ u ≠ 0 :=
    mulVec_ne_zero_of_isUnit (isUnit_det_intert (hV (z : ↥V × Matrix ι ι ℂ).1.2))
      (ne_zero_of_eucNormSq_eq_one hu)
  set c : ℂ := ∑ k, star (u k) * v k with hcdef
  have hvc : c • u = v := by
    rw [hcdef, ← rankOneProj_mulVec, ← hzu, hv]
  rw [hzu, conjNormalize_rankOneProj, ← hvc, Matrix.mulVec_smul, Matrix.mulVec_smul,
    lineOf_mulVec_self hgu]

/-! ### The isomorphism -/

/-- **The chart trivialisation carries the tautological line to the pullback of
the tautological line of `ℂP^d`**, at every rank. -/
noncomputable def tautLineIsoChartCP (q : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ trivSet q x₀) (d : ℕ) (hr : q.rank x₀ = d + 1) :
    BundleIso (tautLine (q.restrictTo V))
      (comap (chartCP q x₀ V hV d hr) (cpTaut d)) := by
  have hbase : Continuous (fun z : Proj (q.restrictTo V) =>
      ((z : ↥V × Matrix ι ι ℂ).1 : X)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hW : chartFrame q x₀ d hr * (chartFrame q x₀ d hr)ᴴ = q x₀ :=
    stdFrame_mul_conjTranspose (q.isStarProjection x₀) (d + 1) _
  have hA : Continuous (fun z : Proj (q.restrictTo V) =>
      (chartFrame q x₀ d hr)ᴴ * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X))) := by
    refine continuous_const.matrix_mul ?_
    exact (continuous_intert q x₀).comp hbase
  refine lineIntertIso
    (fun z : Proj (q.restrictTo V) =>
      (chartFrame q x₀ d hr)ᴴ * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)))
    hA
    (tautLine (q.restrictTo V)) (comap (chartCP q x₀ V hV d hr) (cpTaut d))
    (fun z => trace_tautLine (q.restrictTo V) z)
    (fun z => trace_cpTaut d (chartCP q x₀ V hV d hr z)) ?_ ?_
  · intro z v hv
    have hbasefix := base_mulVec_fixed q V z hv
    have hgv : q x₀ *ᵥ (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v)
        = intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v := by
      rw [Matrix.mulVec_mulVec, ← intert_mul, ← Matrix.mulVec_mulVec, hbasefix]
    show ((chartCP q x₀ V hV d hr z : CP d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
        *ᵥ (((chartFrame q x₀ d hr)ᴴ
          * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X))) *ᵥ v)
      = ((chartFrame q x₀ d hr)ᴴ
          * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X))) *ᵥ v
    have hsplit : ((chartFrame q x₀ d hr)ᴴ
          * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X))) *ᵥ v
        = (chartFrame q x₀ d hr)ᴴ
          *ᵥ (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    rw [hsplit, chartCP_coe]
    exact frame_conj_mulVec (chartFrame q x₀ d hr) (q x₀) _ _ hW hgv
      (conjNormalize_mulVec_self q x₀ V hV z hv)
  · intro z v hv hv0
    have hbasefix := base_mulVec_fixed q V z hv
    have hgv0 : intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v ≠ 0 :=
      mulVec_ne_zero_of_isUnit
        (isUnit_det_intert (hV (z : ↥V × Matrix ι ι ℂ).1.2)) hv0
    have hgv : q x₀ *ᵥ (intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v)
        = intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X)) *ᵥ v := by
      rw [Matrix.mulVec_mulVec, ← intert_mul, ← Matrix.mulVec_mulVec, hbasefix]
    show ((chartFrame q x₀ d hr)ᴴ
        * intert q x₀ (((z : ↥V × Matrix ι ι ℂ).1 : X))) *ᵥ v ≠ 0
    rw [← Matrix.mulVec_mulVec]
    exact frame_mulVec_ne_zero q x₀ d hr hgv hgv0

end ChartTaut

end Bundle

end CharClass
end GroupApproximation
