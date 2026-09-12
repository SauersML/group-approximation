import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Sofic.KazhdanCornerMatrices
import GroupApproximation.Sofic.NormUltraproductSequentialExtraction

/-!
# The normalized almost representations printed in Section 3

The manuscript's definition includes the exact normalization `V_n(1)=1`.
The underlying `OpAlmostRepresentation` intentionally does not require that
normalization, so this file records the literal printed subtype and connects
it to the existing Hilbert--Schmidt kernel construction.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

/-- The operator-norm asymptotic representations exactly as defined in the
manuscript, including `V_n(1)=1` at every coordinate. -/
structure PrintedOpAlmostRepresentation (G : Type) [Group G]
    extends OpAlmostRepresentation G where
  map_one : ∀ n, toOpAlmostRepresentation.map n 1 = 1

/-! ## Exact normalization without changing nonidentity values -/

/-- Replace only the value at the identity by the identity matrix.  This is
the normalization implicit in the printed definition.  In particular, it
does not alter the matrix assigned to any nonidentity group element. -/
noncomputable def normalizedOpMap (A : OpAlmostRepresentation G)
    (n : ℕ) (g : G) : Matrix.unitaryGroup (A.model n) ℂ := by
  classical
  exact if g = 1 then 1 else A.map n g

@[simp] theorem normalizedOpMap_one (A : OpAlmostRepresentation G) (n : ℕ) :
    normalizedOpMap A n 1 = 1 := by
  simp [normalizedOpMap]

@[simp] theorem normalizedOpMap_of_ne_one (A : OpAlmostRepresentation G)
    (n : ℕ) {g : G} (hg : g ≠ 1) :
    normalizedOpMap A n g = A.map n g := by
  simp [normalizedOpMap, hg]

/-- The normalization is an operator-norm null perturbation at each fixed
group element.  At a nonidentity element it is literally unchanged; at the
identity this is exactly `map_one_vanishing`. -/
theorem normalizedOpMap_sub_vanishing (A : OpAlmostRepresentation G) (g : G) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (normalizedOpMap A n g : Matrix (A.model n) (A.model n) ℂ) -
        A.map n g) := by
  classical
  by_cases hg : g = 1
  · subst g
    refine (KazhdanCornerMatrices.map_one_vanishing A).neg.congr ?_
    intro n
    rw [normalizedOpMap_one]
    change -((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) =
      (1 : Matrix (A.model n) (A.model n) ℂ) - A.map n 1
    abel
  · refine (KazhdanCornerMatrices.opNormVanishing_zero A).congr ?_
    intro n
    rw [normalizedOpMap_of_ne_one A n hg]
    simp

/-- Changing only the identity value preserves asymptotic
multiplicativity.  The proof expands the new defect as the old defect plus
three pointwise null perturbations. -/
theorem normalizedOpMap_multiplicative_vanishing
    (A : OpAlmostRepresentation G) (g h : G) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (normalizedOpMap A n (g * h) :
          Matrix (A.model n) (A.model n) ℂ) -
        (normalizedOpMap A n g :
          Matrix (A.model n) (A.model n) ℂ) *
          normalizedOpMap A n h) := by
  have hgh := normalizedOpMap_sub_vanishing A (g * h)
  have hmul := KazhdanCornerMatrices.multiplicativeDefect_vanishing A g h
  have hg := normalizedOpMap_sub_vanishing A g
  have hh := normalizedOpMap_sub_vanishing A h
  have hAh : ∀ n,
      ‖(A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 := by
    intro n
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary (A.map n h).2).le
  have hBg : ∀ n,
      ‖(normalizedOpMap A n g :
          Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 := by
    intro n
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary
      (normalizedOpMap A n g).2).le
  have hleft := hg.neg.mul_right_of_norm_le_one
    (fun n ↦ (A.map n h : Matrix (A.model n) (A.model n) ℂ)) hAh
  have hright := hh.neg.mul_left_of_norm_le_one
    (fun n ↦ (normalizedOpMap A n g :
      Matrix (A.model n) (A.model n) ℂ)) hBg
  have htotal := hgh.add (hmul.add (hleft.add hright))
  exact htotal.congr fun n ↦ by
    noncomm_ring

/-- Every existing `OpAlmostRepresentation` has an equivalent representative
with the exact printed identity equation. -/
noncomputable def opAlmostRepresentationToPrinted
    (A : OpAlmostRepresentation G) : PrintedOpAlmostRepresentation G where
  toOpAlmostRepresentation := {
    model := A.model
    modelNonempty := A.modelNonempty
    map := normalizedOpMap A
    asymptoticallyMultiplicative :=
      normalizedOpMap_multiplicative_vanishing A }
  map_one := normalizedOpMap_one A

@[simp] theorem opAlmostRepresentationToPrinted_model
    (A : OpAlmostRepresentation G) (n : ℕ) :
    (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation.model n =
      A.model n := rfl

@[simp] theorem opAlmostRepresentationToPrinted_map
    (A : OpAlmostRepresentation G) (n : ℕ) (g : G) :
    (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation.map n g =
      normalizedOpMap A n g := rfl

/-- Full row-108 normalization package: exact preservation off the identity,
exact normalization at the identity, and operator-norm equivalence at every
fixed group element.  No stronger input structure is assumed. -/
theorem manuscriptEveryOpAlmostRepresentationHasPrintedNormalization
    (A : OpAlmostRepresentation G) :
    (∀ n, (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation.map n 1 = 1) ∧
      (∀ (g : G), g ≠ 1 → ∀ n,
        (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation.map n g =
          A.map n g) ∧
      (∀ g : G, KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
        (normalizedOpMap A n g : Matrix (A.model n) (A.model n) ℂ) -
          A.map n g)) := by
  refine ⟨(opAlmostRepresentationToPrinted A).map_one, ?_, ?_⟩
  · intro g hg n
    exact normalizedOpMap_of_ne_one A n hg
  · exact normalizedOpMap_sub_vanishing A

/-! ## The induced corona representation is unchanged -/

/-- The cofinite-corona homomorphism represented by any operator-norm almost
representation.  Exact preservation of `1` is not needed here: its defect is
null in the quotient. -/
def opAlmostRepresentationCofiniteCoronaHom (A : OpAlmostRepresentation G) :
    G →* NormMatrixCoronaUnitary A.model := by
  have hnull : ∀ g h : G,
      (fun n ↦ A.map n g * A.map n h)⁻¹ *
          (fun n ↦ A.map n (g * h)) ∈
        nullCofiniteOpSubgroup A.model := by
    intro g h epsilon hepsilon
    obtain ⟨N, hN⟩ :=
      A.asymptoticallyMultiplicative g h (epsilon / 2) (by linarith)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    change opLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < epsilon
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  exact MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g))
    (fun g h ↦ by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq.mpr (hnull g h)).symm)

/-- At every group element, normalization gives the same element of the norm
matrix corona. -/
theorem normalizedOpMap_coronaClass_eq
    (A : OpAlmostRepresentation G) (g : G) :
    (QuotientGroup.mk (fun n ↦ normalizedOpMap A n g) :
        NormMatrixCoronaUnitary A.model) =
      QuotientGroup.mk (fun n ↦ A.map n g) := by
  symm
  apply QuotientGroup.eq.mpr
  intro epsilon hepsilon
  rw [Nat.cofinite_eq_atTop]
  obtain ⟨N, hN⟩ := normalizedOpMap_sub_vanishing A g
    (epsilon / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  change opLength (A.model n)
    ((A.map n g)⁻¹ * normalizedOpMap A n g) < epsilon
  rw [opLength_inv_mul]
  exact (hN n hn).trans_lt (by linarith)

/-- Thus normalization preserves the entire induced corona homomorphism, not
only its kernel or one marked value. -/
theorem opAlmostRepresentationToPrinted_cofiniteCoronaHom_eq
    (A : OpAlmostRepresentation G) :
    opAlmostRepresentationCofiniteCoronaHom
        (opAlmostRepresentationToPrinted A).toOpAlmostRepresentation =
      opAlmostRepresentationCofiniteCoronaHom A := by
  apply MonoidHom.ext
  intro g
  exact normalizedOpMap_coronaClass_eq A g

/-! ## Preservation of marked detection -/

/-- A marked almost representation's marked element survives in the
cofinite norm-matrix corona represented by it. -/
theorem markedOpAlmostRepresentationCofiniteCoronaHom_mark_ne_one
    {z : G} (A : MarkedOpAlmostRepresentation G z) :
    opAlmostRepresentationCofiniteCoronaHom A.toOpAlmostRepresentation z ≠ 1 := by
  intro hz
  have heq : opAlmostRepresentationCofiniteCoronaHom A.toOpAlmostRepresentation z =
      opAlmostRepresentationCofiniteCoronaHom A.toOpAlmostRepresentation 1 := by
    simpa using hz
  have hmem :
      (fun n ↦ A.map n 1)⁻¹ * (fun n ↦ A.map n z) ∈
        nullCofiniteOpSubgroup A.model :=
    QuotientGroup.eq.mp heq.symm
  obtain ⟨n, hn⟩ :=
    (hmem A.separation A.separation_pos).exists
  change opLength (A.model n) ((A.map n 1)⁻¹ * A.map n z) <
    A.separation at hn
  rw [opLength_inv_mul] at hn
  exact (not_lt_of_ge (A.marked_separated n)) hn

/-- Exact normalization preserves the marked corona value, hence preserves
the detector rather than merely reconstructing some unrelated detector. -/
theorem markedOpAlmostRepresentationToPrintedCofiniteCoronaHom_mark_ne_one
    {z : G} (A : MarkedOpAlmostRepresentation G z) :
    opAlmostRepresentationCofiniteCoronaHom
        (opAlmostRepresentationToPrinted
          A.toOpAlmostRepresentation).toOpAlmostRepresentation z ≠ 1 := by
  rw [opAlmostRepresentationToPrinted_cofiniteCoronaHom_eq]
  exact markedOpAlmostRepresentationCofiniteCoronaHom_mark_ne_one A

/-- The original uniform marked separation becomes half of the same
separation eventually after exact identity normalization.  Together with
the preceding corona equality this records both the finite-coordinate and
quotient-level preservation used by the manuscript. -/
theorem markedOpAlmostRepresentationToPrinted_eventually_half_separated
    {z : G} (A : MarkedOpAlmostRepresentation G z) :
    ∃ N, ∀ n ≥ N,
      A.separation / 2 ≤
        ‖(normalizedOpMap A.toOpAlmostRepresentation n z :
            Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
  have hz : z ≠ 1 := by
    intro hz
    subst z
    have hsep := A.marked_separated 0
    simp only [sub_self, norm_zero] at hsep
    exact (not_lt_of_ge hsep) A.separation_pos
  obtain ⟨N, hN⟩ :=
    KazhdanCornerMatrices.map_one_vanishing A.toOpAlmostRepresentation
      (A.separation / 2) (half_pos A.separation_pos)
  refine ⟨N, fun n hn ↦ ?_⟩
  have htri :
      ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ ≤
        ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - 1‖ +
          ‖(1 : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ := by
    rw [show (A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1 =
      ((A.map n z : Matrix (A.model n) (A.model n) ℂ) - 1) +
        (1 - A.map n 1) by abel]
    exact norm_add_le _ _
  have hone :
      ‖(1 : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ ≤
        A.separation / 2 := by
    rw [show (1 : Matrix (A.model n) (A.model n) ℂ) - A.map n 1 =
      -((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) by abel,
      norm_neg]
    exact hN n hn
  rw [normalizedOpMap_of_ne_one A.toOpAlmostRepresentation n hz]
  linarith [A.marked_separated n]

/-- **Sentence-census row 108.**  The structure's epsilon estimate is
equivalent to the displayed convergence assertion, while its exact identity
normalization remains visible as the first conjunct. -/
theorem manuscriptPrintedOpAlmostRepresentationDefinition
    (V : PrintedOpAlmostRepresentation G) :
    (∀ n, V.toOpAlmostRepresentation.map n 1 = 1) ∧
      ∀ g h : G,
        Tendsto (fun n ↦
          ‖(V.toOpAlmostRepresentation.map n (g * h) :
              Matrix (V.toOpAlmostRepresentation.model n)
                (V.toOpAlmostRepresentation.model n) ℂ) -
            (V.toOpAlmostRepresentation.map n g :
              Matrix (V.toOpAlmostRepresentation.model n)
                (V.toOpAlmostRepresentation.model n) ℂ) *
              V.toOpAlmostRepresentation.map n h‖)
          atTop (nhds 0) := by
  refine ⟨V.map_one, ?_⟩
  intro g h
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := V.toOpAlmostRepresentation.asymptoticallyMultiplicative
    g h (epsilon / 2) (half_pos hepsilon)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact (hN n hn).trans_lt (half_lt_self hepsilon)

/-- **Sentence-census row 109.**  For a literally normalized printed almost
representation, membership in `K₂(V)` is exactly ordinary convergence of
the normalized Hilbert--Schmidt displacement from the identity. -/
theorem manuscriptPrintedHSKernelMembership
    (V : PrintedOpAlmostRepresentation G) (g : G) :
    g ∈ hsKernel V.toOpAlmostRepresentation ↔
      Tendsto
        (fun n ↦ Real.sqrt (hsLengthSq
          (V.toOpAlmostRepresentation.model n)
          ((V.toOpAlmostRepresentation.map n g :
            Matrix (V.toOpAlmostRepresentation.model n)
              (V.toOpAlmostRepresentation.model n) ℂ))))
        atTop (nhds 0) :=
  (mem_hsKernel_iff V.toOpAlmostRepresentation g).trans
    (isHSNull_iff_tendsto V.toOpAlmostRepresentation g)

/-- **Sentence-census row 111.**  The Hilbert--Schmidt kernel of every
literally normalized printed almost representation is normal in `G`. -/
theorem manuscriptPrintedHSKernelNormal
    (V : PrintedOpAlmostRepresentation G) :
    (hsKernel V.toOpAlmostRepresentation).Normal :=
  hsKernel_normal V.toOpAlmostRepresentation

end OneSidedMFRadical
end Manuscript
end GroupApproximation
