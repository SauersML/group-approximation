import GroupApproximation.Analysis.UltraproductRigidityRoute
import GroupApproximation.Sofic.CompressionDefectSquare

/-!
# The negative-corner contradiction, on the printed route

Proof-ledger rows `TA.11` and `KC.02`.  Both are the same printed sentence read
at two data.  `p:A-defect-square` says

> for a detecting corona representation, the negative corner gives a model with
> `w = -1` exactly, while transport gives `u ~₂ 1` and hence `w ~₂ 1`,

and `p:constr-tietze` says

> rigidity forces `u ~₂ 1` while the Clifford model makes `u² = -1`.

The two consumers of that sentence --
`LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction` and
`KazhdanCliffordConstruction.negativeCorner_kazhdanTransport_contradiction` --
used to reach it through `KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation`,
whose one transport step is the finite-stage corner argument
(`commutatorMatrix_hsDistSq_vanishing`, which runs
`one_sub_corner_mul_moved_vanishing` and `displacement_vanishing` with the
explicit constants).  That is the alternative route, not the printed one, and
both rows record the gap in those words.

## What this file supplies

The same contradiction, with `u ~₂ 1` taken from the pinning seam
`KazhdanCompressionCore.CompressionDefectsHSTrivial` rather than re-derived at
the finite stage.  The seam is the one `LiteralNonMFEndpoint.kazhdanPinning`
already travels: `UltraproductRigidityRoute.compressionDefects_hsTrivial_literal`,
whose transport step is `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`
-- that is, `\ref{thm:kazhdan-transport}` proved by the printed §3 ultraproduct
argument.

The step the printed sentence adds on top of pinning is "hence `w ~₂ 1`", and
it is exactly one line of Hilbert--Schmidt algebra: `w = u²` (which is
`MarkedCompressionInclusionData.word_eq_compressionDefect_sq`, available
whenever the root involution satisfies `c² = 1`), and squaring at most doubles
the normalized Hilbert--Schmidt displacement from the identity
(`hsDistSq_sq_le_four`).  No estimate of the transport is reproved here and no
constant of the finite-stage appendix appears.

The finite-stage route is left standing beside this one, unchanged and proving
the same statement; a consumer picks its route by picking its name.  What is
shared between the two is the corner extraction
(`NegativeCornerModel.exists_negativeCorner_opAlmostRepresentation`) and the
final triangle inequality, which are operator-norm bookkeeping and not
transport.
-/

namespace GroupApproximation
namespace PrintedNegativeCornerKill

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator commutatorElement

universe u

variable {Γ : Type} [Group Γ] {E : Type u} [Group E]

/-! ## "hence `w ~₂ 1`" -/

/-- **Squaring at most quadruples the Hilbert--Schmidt displacement.**  For a
unitary `V`, the displacement of `V²` from the identity is at most four times
that of `V`, because `V² - 1 = V(V - 1) + (V - 1)` and left multiplication by a
unitary is an isometry for the normalized Hilbert--Schmidt norm.

This is the printed "hence `w ~₂ 1`" of `p:A-defect-square`: the mark is the
square of the pointwise compression defect, so pinning the defect pins the
mark. -/
theorem hsDistSq_sq_le_four {Y : FiniteModel} (hY : 0 < Fintype.card Y)
    {V : Matrix Y Y ℂ} (hV : V ∈ Matrix.unitaryGroup Y ℂ) :
    hsDistSq Y (V * V) 1 ≤ 4 * hsDistSq Y V 1 := by
  have hdecomp : V * V - 1 = V * (V - 1) + (V - 1) := by noncomm_ring
  have hterm : hsNormSq Y (V * (V - 1)) = hsNormSq Y (V - 1) :=
    hsNormSq_mul_left Y hV hY _
  change hsNormSq Y (V * V - 1) ≤ 4 * hsNormSq Y (V - 1)
  rw [hdecomp]
  calc
    hsNormSq Y (V * (V - 1) + (V - 1)) ≤
        2 * hsNormSq Y (V * (V - 1)) + 2 * hsNormSq Y (V - 1) :=
      hsNormSq_add_le Y _ _
    _ = 4 * hsNormSq Y (V - 1) := by rw [hterm]; ring

/-- **From the pinned defect to the pinned square.**  If a group element `u` is
Hilbert--Schmidt trivial in an operator-norm almost representation, then so is
its square, and hence so is any `w` equal to `u²`.

The three inputs are the pinning of `u`, the asymptotic multiplicativity of the
almost representation at the pair `(u, u)`, and the fact that the image of `1`
is asymptotically the identity matrix; the last two are structural and carry no
transport. -/
theorem word_hsDistSq_vanishing_of_defect
    (B : OpAlmostRepresentation E) {w u : E} (hw : w = u * u)
    (hdefect : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n) (B.map n u : Matrix (B.model n) (B.model n) ℂ)
        (B.map n 1) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        (B.map n w : Matrix (B.model n) (B.model n) ℂ) 1 ≤ ε := by
  intro ε hε
  have h48 : (0 : ℝ) < ε / 48 := by linarith
  have h6 : (0 : ℝ) < ε / 6 := by linarith
  have hsqrt48 : (Real.sqrt (ε / 48)) ^ 2 = ε / 48 := Real.sq_sqrt h48.le
  have hsqrt6 : (Real.sqrt (ε / 6)) ^ 2 = ε / 6 := Real.sq_sqrt h6.le
  obtain ⟨N₁, hN₁⟩ := hdefect (ε / 48) h48
  obtain ⟨N₂, hN₂⟩ :=
    map_one_vanishing B (Real.sqrt (ε / 48)) (Real.sqrt_pos.mpr h48)
  obtain ⟨N₃, hN₃⟩ :=
    multiplicativeDefect_vanishing B u u (Real.sqrt (ε / 6))
      (Real.sqrt_pos.mpr h6)
  refine ⟨max N₁ (max N₂ N₃), fun n hn ↦ ?_⟩
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n ≥ N₃ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hY : 0 < Fintype.card (B.model n) := B.modelNonempty n
  have hVu : (B.map n u : Matrix (B.model n) (B.model n) ℂ) ∈
      Matrix.unitaryGroup (B.model n) ℂ := (B.map n u).2
  -- the pinned defect, and the image of `1`
  have hstep1 : hsDistSq (B.model n)
      (B.map n u : Matrix (B.model n) (B.model n) ℂ) (B.map n 1) ≤ ε / 48 :=
    hN₁ n hn₁
  have hstep2 : hsDistSq (B.model n)
      (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) 1 ≤ ε / 48 := by
    refine (hsDistSq_le_sq_l2_opNorm (B.model n) _ _).trans ?_
    have h : ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖ ≤
        Real.sqrt (ε / 48) := hN₂ n hn₂
    nlinarith [norm_nonneg
      ((B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1)]
  have hstep3 : hsDistSq (B.model n)
      (B.map n u : Matrix (B.model n) (B.model n) ℂ) 1 ≤
      2 * (ε / 48) + 2 * (ε / 48) := by
    have h := hsDistSq_le_two_add_two (B.model n)
      (B.map n u : Matrix (B.model n) (B.model n) ℂ) 1 (B.map n 1)
    linarith
  -- squaring
  have hstep4 : hsDistSq (B.model n)
      ((B.map n u : Matrix (B.model n) (B.model n) ℂ) * B.map n u) 1 ≤
      4 * hsDistSq (B.model n)
        (B.map n u : Matrix (B.model n) (B.model n) ℂ) 1 :=
    hsDistSq_sq_le_four hY hVu
  -- and the multiplicative defect at the pair `(u, u)`
  have hstep5 : hsDistSq (B.model n)
      (B.map n w : Matrix (B.model n) (B.model n) ℂ)
      ((B.map n u : Matrix (B.model n) (B.model n) ℂ) * B.map n u) ≤
      ε / 6 := by
    refine (hsDistSq_le_sq_l2_opNorm (B.model n) _ _).trans ?_
    have h : ‖(B.map n (u * u) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n u : Matrix (B.model n) (B.model n) ℂ) * B.map n u‖ ≤
        Real.sqrt (ε / 6) := hN₃ n hn₃
    rw [← hw] at h
    nlinarith [norm_nonneg
      ((B.map n w : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n u : Matrix (B.model n) (B.model n) ℂ) * B.map n u)]
  have hfinal := hsDistSq_le_two_add_two (B.model n)
    (B.map n w : Matrix (B.model n) (B.model n) ℂ) 1
    ((B.map n u : Matrix (B.model n) (B.model n) ℂ) * B.map n u)
  linarith

/-! ## The contradiction -/

/-- **The negative corner against the pinned mark.**  An operator-norm almost
representation whose marked word tends to `-1` cannot have its compression
defects pinned, because the mark is the square of one of them.

This is `KazhdanCompressorCorner.false_of_marked_word_tends_to_neg_one` with the
transport step taken as a hypothesis in the shape the printed proof states it,
rather than rebuilt from the Kazhdan pair at the finite stage. -/
theorem false_of_marked_word_tends_to_neg_one_of_pinned
    (B : OpAlmostRepresentation E) (D : MarkedCompressionInclusionData Γ E)
    (hc : D.c ^ 2 = 1)
    (hpin : KazhdanCompressionCore.CompressionDefectsHSTrivial
      D.toKazhdanCompressionCore B)
    (hnegative : OpNormVanishing B (fun n ↦
      (B.map n D.word : Matrix (B.model n) (B.model n) ℂ) + 1)) :
    False := by
  have hdefect : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        (B.map n ⁅D.t * D.c * D.t⁻¹, D.iota D.a⁆ :
          Matrix (B.model n) (B.model n) ℂ)
        (B.map n 1) ≤ ε := hpin D.a
  have hword : D.word = ⁅D.t * D.c * D.t⁻¹, D.iota D.a⁆ *
      ⁅D.t * D.c * D.t⁻¹, D.iota D.a⁆ := by
    rw [D.word_eq_compressionDefect_sq hc, pow_two]
  obtain ⟨N₁, hN₁⟩ :=
    word_hsDistSq_vanishing_of_defect B hword hdefect (1 / 16) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := hnegative (1 / 4) (by norm_num)
  have hn₁ : max N₁ N₂ ≥ N₁ := le_max_left _ _
  have hn₂ : max N₁ N₂ ≥ N₂ := le_max_right _ _
  have hY : 0 < Fintype.card (B.model (max N₁ N₂)) :=
    B.modelNonempty (max N₁ N₂)
  have hone : hsDistSq (B.model (max N₁ N₂))
      (B.map (max N₁ N₂) D.word :
        Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) 1 ≤ 1 / 16 :=
    hN₁ (max N₁ N₂) hn₁
  have hnegNorm : ‖(B.map (max N₁ N₂) D.word :
      Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) + 1‖ ≤ 1 / 4 :=
    hN₂ (max N₁ N₂) hn₂
  have hneg : hsDistSq (B.model (max N₁ N₂))
      (B.map (max N₁ N₂) D.word :
        Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) (-1) ≤
      1 / 16 := by
    have h := hsDistSq_le_sq_l2_opNorm (B.model (max N₁ N₂))
      (B.map (max N₁ N₂) D.word :
        Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) (-1)
    rw [sub_neg_eq_add] at h
    nlinarith [norm_nonneg ((B.map (max N₁ N₂) D.word :
      Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) + 1)]
  have htri := hsDistSq_le_two_add_two (B.model (max N₁ N₂))
    (1 : Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) (-1)
    (B.map (max N₁ N₂) D.word)
  have honeNeg : hsDistSq (B.model (max N₁ N₂))
      (1 : Matrix (B.model (max N₁ N₂)) (B.model (max N₁ N₂)) ℂ) (-1) = 4 :=
    hsDistSq_one_neg_one (B.model (max N₁ N₂)) hY
  rw [honeNeg, hsDistSq_comm (B.model (max N₁ N₂)) 1
    (B.map (max N₁ N₂) D.word)] at htri
  linarith

/-- **The marked separation is impossible, from pinning alone.**  A separated
mark cuts to a negative corner by `lem:corner`, and on that corner the pinned
mark cannot also sit at `-1`.

The pinning hypothesis is quantified over *every* operator-norm almost
representation because the corner extraction produces a new one; that is
precisely the shape `LiteralNonMFEndpoint.kazhdanPinning` has. -/
theorem false_of_markedOpAlmostRepresentation_of_pinned
    (D : MarkedCompressionInclusionData Γ E) (hc : D.c ^ 2 = 1)
    (hpin : ∀ B : OpAlmostRepresentation E,
      KazhdanCompressionCore.CompressionDefectsHSTrivial
        D.toKazhdanCompressionCore B)
    (A : MarkedOpAlmostRepresentation E D.word) : False := by
  have hz : D.word * D.word = 1 := by
    have h := D.word_pow_two
    rwa [pow_two] at h
  have hcentral : ∀ g : E, D.word * g = g * D.word := fun g ↦
    (D.word_commute g).eq
  have hsep : ∃ N, ∀ n ≥ N, A.separation ≤
      ‖(A.toOpAlmostRepresentation.map n D.word :
        Matrix (A.toOpAlmostRepresentation.model n)
          (A.toOpAlmostRepresentation.model n) ℂ) -
        A.toOpAlmostRepresentation.map n 1‖ :=
    ⟨0, fun n _ ↦ A.marked_separated n⟩
  obtain ⟨B, hnegative⟩ :=
    NegativeCornerModel.exists_negativeCorner_opAlmostRepresentation
      A.toOpAlmostRepresentation hz hcentral A.separation_pos hsep
  exact false_of_marked_word_tends_to_neg_one_of_pinned B D hc (hpin B) hnegative

/-- **The printed route, assembled.**  The pinning is supplied by
`UltraproductRigidityRoute.compressionDefects_hsTrivial_literal`, whose one
transport step is `\ref{thm:kazhdan-transport}` by the printed §3 ultraproduct
proof.  This is the declaration the two endpoints consume; the finite-stage
`KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation` proves the same
statement and is untouched. -/
theorem false_of_markedOpAlmostRepresentation_printed
    (D : MarkedCompressionInclusionData Γ E) (hc : D.c ^ 2 = 1)
    (A : MarkedOpAlmostRepresentation E D.word) : False :=
  false_of_markedOpAlmostRepresentation_of_pinned D hc
    (fun B ↦ UltraproductRigidityRoute.compressionDefects_hsTrivial_literal
      D.toKazhdanCompressionCore B) A

end PrintedNegativeCornerKill
end GroupApproximation
