import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Analysis.AmenableTraceHyperlinear
import GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The Hilbert--Schmidt null elements form a normal subgroup: the printed displays

`non_mf_groups_exist.tex`, Section 2 (tex lines 404-412 at 73c867c5b):

> The elements `g` with `‖V_n(g) − 1‖₂ → 0` form a normal subgroup of `G`,
> because `‖a‖₂ ≤ ‖a‖`, the Hilbert--Schmidt norm is invariant under adjoints
> and unitary conjugation, and `‖V_n(g⁻¹) − V_n(g)*‖ → 0`:
> `‖V_n(gh)−1‖₂ ≤ ‖V_n(g)−1‖₂ + ‖V_n(h)−1‖₂ + o(1)`,
> `‖V_n(g⁻¹)−1‖₂ = ‖V_n(g)−1‖₂ + o(1)`,
> `‖V_n(ghg⁻¹)−1‖₂ = ‖V_n(h)−1‖₂ + o(1)`.

The development's carrier for this sentence (`OneSidedMFRadical.hsKernel`,
`hsKernel_normal`) proves normality through Hilbert--Schmidt ultraproducts, a
different argument.  This module proves it along the printed sentence: the three
cited facts, the three displayed estimates, and the subgroup they give, which is
then identified with `hsKernel`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Two consequences of the triangle inequality for `‖·‖₂` -/

theorem hsNorm_sub_le_add_nm (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (a b c : Matrix Y Y ℂ) :
    hsNorm Y (a - c) ≤ hsNorm Y (a - b) + hsNorm Y (b - c) := by
  have h := OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le Y hY
    (a - b) (b - c)
  rwa [sub_add_sub_cancel] at h

theorem abs_hsNorm_sub_hsNorm_le_nm (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (a b : Matrix Y Y ℂ) :
    |hsNorm Y a - hsNorm Y b| ≤ hsNorm Y (a - b) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le Y hY
      (a - b) b
    rw [sub_add_cancel] at h
    linarith
  · have h := OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le Y hY
      (b - a) a
    rw [sub_add_cancel, AmenableTraceHyperlinear.hsNorm_sub_comm Y b a] at h
    linarith

/-! ## The operator norm facts about an asymptotic representation -/

theorem opAlmost_tendsto_mulDefect {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (g h : G) :
    Tendsto (fun n ↦ ‖(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact (hN n hn).trans_lt (by linarith)

theorem opAlmost_norm_map_eq_one {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (n : ℕ) (g : G) : ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ = 1 := by
  haveI : Nonempty (B.model n) := Fintype.card_pos_iff.mp (B.modelNonempty n)
  exact CStarRing.norm_of_mem_unitary (B.map n g).2

theorem opAlmost_conjTranspose_map_mem {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (n : ℕ) (g : G) :
    (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ ∈
      Matrix.unitaryGroup (B.model n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h := Unitary.star_mul_self_of_mem (B.map n g).2
  rwa [Matrix.star_eq_conjTranspose] at h

theorem opAlmost_tendsto_map_one_sub_one {G : Type} [Group G]
    (B : OpAlmostRepresentation G) :
    Tendsto (fun n ↦ ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖)
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (opAlmost_tendsto_mulDefect B 1 1)
  dsimp only
  have hunit : star (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (B.map n 1).2
  have hkey : (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1
      = -(star (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n 1 : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) * B.map n 1)) := by
    rw [mul_sub, ← mul_assoc, hunit, one_mul, neg_sub]
  have hstar : ‖star (B.map n 1 : Matrix (B.model n) (B.model n) ℂ)‖ = 1 := by
    rw [norm_star]
    exact opAlmost_norm_map_eq_one B n 1
  calc ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖
      = ‖star (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n 1 : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) * B.map n 1)‖ := by
        rw [hkey, norm_neg]
    _ ≤ ‖star (B.map n 1 : Matrix (B.model n) (B.model n) ℂ)‖ *
          ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) * B.map n 1‖ :=
        norm_mul_le _ _
    _ = ‖(B.map n (1 * 1) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) * B.map n 1‖ := by
        rw [hstar, one_mul, mul_one]

/-- **The printed `‖V_n(g⁻¹) − V_n(g)*‖ → 0`.** -/
theorem opAlmost_tendsto_map_inv_sub_conjTranspose {G : Type} [Group G]
    (B : OpAlmostRepresentation G) (g : G) :
    Tendsto (fun n ↦ ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖) atTop (𝓝 0) := by
  have hsum := (opAlmost_tendsto_mulDefect B g⁻¹ g).add
    (opAlmost_tendsto_map_one_sub_one B)
  rw [add_zero] at hsum
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  dsimp only
  have hUU : (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
    have h := Unitary.mul_star_self_of_mem (B.map n g).2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hkey : (B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ
      = ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ := by
    rw [sub_mul, mul_assoc, hUU, mul_one, one_mul]
  have hnormU : ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact opAlmost_norm_map_eq_one B n g
  calc ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖
      = ‖((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ := by rw [hkey]
    _ ≤ ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1‖ *
        ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ := norm_mul_le _ _
    _ = ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1‖ := by
        rw [hnormU, mul_one]
    _ ≤ ‖(B.map n (g⁻¹ * g) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) * B.map n g‖ +
        ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖ := by
        rw [inv_mul_cancel]
        have htri := norm_sub_le_norm_sub_add_norm_sub
          ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ))
          (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) 1
        rwa [norm_sub_rev ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ))] at htri

/-! ## The three displays -/

/-- **First display**: `‖V_n(gh)−1‖₂ ≤ ‖V_n(g)−1‖₂ + ‖V_n(h)−1‖₂ + o(1)`. -/
theorem printedDisplay_mul {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (g h : G) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ,
      hsNorm (B.model n) ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) - 1)
        ≤ hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)
          + hsNorm (B.model n) ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1)
          + ε n := by
  refine ⟨fun n ↦ ‖(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h‖,
    opAlmost_tendsto_mulDefect B g h, fun n ↦ ?_⟩
  dsimp only
  have hY := B.modelNonempty n
  have hsplit : (B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) - 1
      = ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)
        + ((B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1)
          + ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)) := by
    noncomm_ring
  have h1 := OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le
    (B.model n) hY
    ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)
    ((B.map n g : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1)
      + ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1))
  have h2 := OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le
    (B.model n) hY
    ((B.map n g : Matrix (B.model n) (B.model n) ℂ) *
      ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1))
    ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)
  have h3 := PrelimNotation.hsNorm_mul_left (B.model n) (B.map n g).2
    ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1)
  have h4 := PrelimNotation.hsNorm_le_l2_opNorm (B.model n)
    ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)
  rw [hsplit]
  linarith

/-- **Second display**: `‖V_n(g⁻¹)−1‖₂ = ‖V_n(g)−1‖₂ + o(1)`. -/
theorem printedDisplay_inv {G : Type} [Group G] (B : OpAlmostRepresentation G) (g : G) :
    Tendsto (fun n ↦
      hsNorm (B.model n) ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1)
        - hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n ↦ ?_) (opAlmost_tendsto_map_inv_sub_conjTranspose B g)
  have hY := B.modelNonempty n
  have hadj : hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)
      = hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ - 1) := by
    rw [← AmenableTraceHyperlinear.hsNorm_conjTranspose (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1),
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [hadj, Real.norm_eq_abs]
  calc |hsNorm (B.model n) ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1)
        - hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ - 1)|
      ≤ hsNorm (B.model n)
          (((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1)
            - ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ - 1)) :=
        abs_hsNorm_sub_hsNorm_le_nm (B.model n) hY _ _
    _ = hsNorm (B.model n) ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ)
          - (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
        rw [sub_sub_sub_cancel_right]
    _ ≤ ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ)
          - (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ :=
        PrelimNotation.hsNorm_le_l2_opNorm (B.model n) _

/-- **Third display**: `‖V_n(ghg⁻¹)−1‖₂ = ‖V_n(h)−1‖₂ + o(1)`. -/
theorem printedDisplay_conj {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (g h : G) :
    Tendsto (fun n ↦
      hsNorm (B.model n) ((B.map n (g * h * g⁻¹) : Matrix (B.model n) (B.model n) ℂ) - 1)
        - hsNorm (B.model n) ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1))
      atTop (𝓝 0) := by
  have hlim := ((opAlmost_tendsto_mulDefect B (g * h) g⁻¹).add
    (opAlmost_tendsto_mulDefect B g h)).add
      (opAlmost_tendsto_map_inv_sub_conjTranspose B g)
  rw [add_zero, add_zero] at hlim
  refine squeeze_zero_norm (fun n ↦ ?_) hlim
  dsimp only
  have hY := B.modelNonempty n
  set Vc := (B.map n (g * h * g⁻¹) : Matrix (B.model n) (B.model n) ℂ) with hVc
  set Vgh := (B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) with hVgh
  set Vi := (B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) with hVi
  set Vg := (B.map n g : Matrix (B.model n) (B.model n) ℂ) with hVg
  set Vh := (B.map n h : Matrix (B.model n) (B.model n) ℂ) with hVh
  have hgg : Vg * Vgᴴ = 1 := by
    have hu := Unitary.mul_star_self_of_mem (B.map n g).2
    rwa [Matrix.star_eq_conjTranspose] at hu
  have hconjform : Vg * Vh * Vgᴴ - 1 = Vg * (Vh - 1) * Vgᴴ := by
    rw [mul_sub, sub_mul, mul_one, hgg]
  have hinvar : hsNorm (B.model n) (Vg * Vh * Vgᴴ - 1) = hsNorm (B.model n) (Vh - 1) := by
    rw [hconjform]
    exact PrelimNotation.hsNorm_unitary_mul_mul (B.model n) (B.map n g).2
      (opAlmost_conjTranspose_map_mem B n g) (Vh - 1)
  have hnormVi : ‖Vi‖ = 1 := opAlmost_norm_map_eq_one B n g⁻¹
  have hnormVg : ‖Vg‖ = 1 := opAlmost_norm_map_eq_one B n g
  have hnormVh : ‖Vh‖ = 1 := opAlmost_norm_map_eq_one B n h
  have hop : ‖Vc - Vg * Vh * Vgᴴ‖
      ≤ ‖Vc - Vgh * Vi‖ + ‖Vgh - Vg * Vh‖ + ‖Vi - Vgᴴ‖ := by
    have hsplit : Vc - Vg * Vh * Vgᴴ
        = (Vc - Vgh * Vi) + ((Vgh - Vg * Vh) * Vi + Vg * Vh * (Vi - Vgᴴ)) := by
      noncomm_ring
    have hVgVh : ‖Vg * Vh‖ ≤ 1 :=
      (norm_mul_le _ _).trans (le_of_eq (by rw [hnormVg, hnormVh, one_mul]))
    have hb : ‖Vg * Vh‖ * ‖Vi - Vgᴴ‖ ≤ ‖Vi - Vgᴴ‖ := by
      calc ‖Vg * Vh‖ * ‖Vi - Vgᴴ‖ ≤ 1 * ‖Vi - Vgᴴ‖ :=
            mul_le_mul_of_nonneg_right hVgVh (norm_nonneg _)
        _ = ‖Vi - Vgᴴ‖ := one_mul _
    have ha : ‖(Vgh - Vg * Vh) * Vi‖ ≤ ‖Vgh - Vg * Vh‖ :=
      (norm_mul_le _ _).trans (le_of_eq (by rw [hnormVi, mul_one]))
    have hc : ‖Vg * Vh * (Vi - Vgᴴ)‖ ≤ ‖Vg * Vh‖ * ‖Vi - Vgᴴ‖ := norm_mul_le _ _
    have hn1 := norm_add_le (Vc - Vgh * Vi) ((Vgh - Vg * Vh) * Vi + Vg * Vh * (Vi - Vgᴴ))
    have hn2 := norm_add_le ((Vgh - Vg * Vh) * Vi) (Vg * Vh * (Vi - Vgᴴ))
    rw [hsplit]
    linarith
  rw [Real.norm_eq_abs, ← hinvar]
  calc |hsNorm (B.model n) (Vc - 1) - hsNorm (B.model n) (Vg * Vh * Vgᴴ - 1)|
      ≤ hsNorm (B.model n) ((Vc - 1) - (Vg * Vh * Vgᴴ - 1)) :=
        abs_hsNorm_sub_hsNorm_le_nm (B.model n) hY _ _
    _ = hsNorm (B.model n) (Vc - Vg * Vh * Vgᴴ) := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖Vc - Vg * Vh * Vgᴴ‖ := PrelimNotation.hsNorm_le_l2_opNorm (B.model n) _
    _ ≤ ‖Vc - Vgh * Vi‖ + ‖Vgh - Vg * Vh‖ + ‖Vi - Vgᴴ‖ := hop

/-! ## The subgroup the displays give -/

/-- **The printed subgroup** `{g : ‖V_n(g) − 1‖₂ → 0}`, closed under products and
inverses by the first two displays. -/
def printedHSNullSubgroup {G : Type} [Group G] (B : OpAlmostRepresentation G) :
    Subgroup G where
  carrier := {g | Tendsto (fun n ↦
    hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)) atTop (𝓝 0)}
  one_mem' :=
    squeeze_zero (fun n ↦ hsNorm_nonneg _ _)
      (fun n ↦ PrelimNotation.hsNorm_le_l2_opNorm _ _)
      (opAlmost_tendsto_map_one_sub_one B)
  mul_mem' := by
    intro g h hg hh
    obtain ⟨ε, hε, hbound⟩ := printedDisplay_mul B g h
    have hsum := ((hg.add hh).add hε)
    rw [add_zero, add_zero] at hsum
    exact squeeze_zero (fun n ↦ hsNorm_nonneg _ _) hbound hsum
  inv_mem' := by
    intro g hg
    have hi := (printedDisplay_inv B g).add hg
    rw [add_zero] at hi
    exact hi.congr fun n ↦ sub_add_cancel _ _

/-- **Normality**, by the third display. -/
theorem printedHSNullSubgroup_normal {G : Type} [Group G] (B : OpAlmostRepresentation G) :
    (printedHSNullSubgroup B).Normal where
  conj_mem := by
    intro h hh g
    have hc := (printedDisplay_conj B g h).add hh
    rw [add_zero] at hc
    exact hc.congr fun n ↦ sub_add_cancel _ _

/-- The printed subgroup is the development's `K₂(V) = hsKernel V`. -/
theorem mem_printedHSNullSubgroup_iff_mem_hsKernel {G : Type} [Group G]
    (B : OpAlmostRepresentation G) (g : G) :
    g ∈ printedHSNullSubgroup B ↔ g ∈ OneSidedMFRadical.hsKernel B :=
  (OneSidedMFRadical.isHSNull_iff_tendsto B g).symm

/-- **The printed sentence (tex lines 404-412), every clause.** -/
def PrintedHSNullNormalSubgroupRoute : Prop :=
  ∀ (G : Type) [Group G] (B : OpAlmostRepresentation G),
    (∀ (n : ℕ) (A : Matrix (B.model n) (B.model n) ℂ), hsNorm (B.model n) A ≤ ‖A‖) ∧
    (∀ (n : ℕ) (A : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n) Aᴴ = hsNorm (B.model n) A) ∧
    (∀ (n : ℕ) (U W A : Matrix (B.model n) (B.model n) ℂ),
      U ∈ Matrix.unitaryGroup (B.model n) ℂ → W ∈ Matrix.unitaryGroup (B.model n) ℂ →
        hsNorm (B.model n) (U * A * W) = hsNorm (B.model n) A) ∧
    (∀ g : G, Tendsto (fun n ↦ ‖(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ‖) atTop (𝓝 0)) ∧
    (∀ g h : G, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ,
      hsNorm (B.model n) ((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) - 1)
        ≤ hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)
          + hsNorm (B.model n) ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1)
          + ε n) ∧
    (∀ g : G, Tendsto (fun n ↦
      hsNorm (B.model n) ((B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1)
        - hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1))
      atTop (𝓝 0)) ∧
    (∀ g h : G, Tendsto (fun n ↦
      hsNorm (B.model n) ((B.map n (g * h * g⁻¹) : Matrix (B.model n) (B.model n) ℂ) - 1)
        - hsNorm (B.model n) ((B.map n h : Matrix (B.model n) (B.model n) ℂ) - 1))
      atTop (𝓝 0)) ∧
    ∃ K : Subgroup G, K.Normal ∧ ∀ g : G, g ∈ K ↔
      Tendsto (fun n ↦
        hsNorm (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1)) atTop (𝓝 0)

theorem manuscriptSentence_hsNullNormalSubgroupPrintedRoute :
    PrintedHSNullNormalSubgroupRoute := by
  intro G _ B
  exact ⟨fun n A ↦ PrelimNotation.hsNorm_le_l2_opNorm (B.model n) A,
    fun n A ↦ AmenableTraceHyperlinear.hsNorm_conjTranspose (B.model n) A,
    fun n U W A hU hW ↦ PrelimNotation.hsNorm_unitary_mul_mul (B.model n) hU hW A,
    opAlmost_tendsto_map_inv_sub_conjTranspose B,
    printedDisplay_mul B, printedDisplay_inv B, printedDisplay_conj B,
    ⟨printedHSNullSubgroup B, printedHSNullSubgroup_normal B, fun _ ↦ Iff.rfl⟩⟩

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_hsNullNormalSubgroupPrintedRoute
