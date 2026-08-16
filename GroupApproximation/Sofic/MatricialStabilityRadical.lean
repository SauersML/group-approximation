import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.DirectSumAmplification

/-!
# Matricial stability identifies the MF radical with the
# finite-dimensional residual

A countable group is point-norm matricially stable when every
operator-norm almost representation is pointwise operator-norm close to a
sequence of genuine finite-dimensional unitary representations.  For such
a group the two natural residuals coincide: the literal genuine-corona MF
radical equals the intersection of the kernels of all finite-dimensional
unitary representations.

One inclusion needs no stability: a finite-dimensional representation `π`
on `ℂ^d` amplifies to the direct sums `π^{⊕n}` on `ℂ^{nd}`, whose dimensions
strictly increase and whose operator-norm displacement from the identity is
that of `π` itself, so the amplified sequence is null exactly when `π(x) = 1`
and the MF radical lies in every finite-dimensional kernel.  That is the
manuscript's own route, and `Sofic.DirectSumAmplification` carries it; the
constant-sequence representation `constCoronaRep` below is kept because it is
the same construction with the amplification suppressed, and it records what
the printed proof would look like without the increasing dimensions.  For the
other inclusion, a corona representation
that detects an element of the finite-dimensional residual extracts a
marked operator-norm almost representation with a uniform gap at that
element; stability replaces it pointwise by genuine representations,
which kill the element, and the gap collapses.

Consequently a matricially stable group whose finite-dimensional residual
is nontrivial is not MF — an obstruction axis with no torsion, no marked
word, and no compression datum, and for stable groups the MF radical is
computable by finite-dimensional representation theory alone.
-/

namespace GroupApproximation
namespace MatricialStabilityRadical

open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- Point-norm matricial stability: every operator-norm almost
representation is pointwise operator-norm close to genuine
finite-dimensional unitary representations on the same models. -/
def IsPointNormMatriciallyStable (G : Type u) [Group G] : Prop :=
  ∀ B : OpAlmostRepresentation G,
    ∃ pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ,
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) -
          (pi n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤ ε

/-- The finite-dimensional unitary residual: the intersection of the
kernels of all finite-dimensional unitary representations. -/
def fdUnitaryResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ (Y : FiniteModel) (phi : G →* Matrix.unitaryGroup Y ℂ), phi.ker

theorem mem_fdUnitaryResidual_iff {x : G} :
    x ∈ fdUnitaryResidual G ↔
      ∀ (Y : FiniteModel) (phi : G →* Matrix.unitaryGroup Y ℂ),
        phi x = 1 := by
  unfold fdUnitaryResidual
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- The constant-sequence corona representation attached to a
finite-dimensional unitary representation. -/
def constCoronaRep (Y : FiniteModel)
    (phi : G →* Matrix.unitaryGroup Y ℂ) :
    G →* NormMatrixCoronaUnitary (fun _ : ℕ ↦ Y) :=
  (QuotientGroup.mk' (nullCofiniteOpSubgroup (fun _ : ℕ ↦ Y))).comp
    (MonoidHom.pi fun _ : ℕ ↦ phi)

/-- **No stability needed**: the MF radical lies in every
finite-dimensional kernel.

The proof is the manuscript's.  Amplify `phi` to the direct sums
`phi^{⊕(n+1)}` of `Sofic.DirectSumAmplification`: the dimensions
`(n+1)·d` strictly increase, so the amplified sequence is a homomorphism into
a corona built on increasing dimensions, and the operator-norm displacement of
`phi^{⊕(n+1)}(x)` from the identity equals that of `phi(x)` at every
coordinate.  An element of the radical is killed by that homomorphism, so the
amplified sequence is null; since every coordinate carries the same number,
that number is zero and `phi(x) = 1`.

The group is quantified inside the proposition, not carried in from the
section `variable` above: a manuscript endpoint must state on its own face
what a caller has to supply, and here that is nothing. -/
theorem actualCoronaMFResidual_le_fdUnitaryResidual :
    ∀ {G : Type u} [Group G],
      actualCoronaMFResidual G ≤ fdUnitaryResidual G := by
  intro G _ x hx
  rw [mem_fdUnitaryResidual_iff]
  intro Y phi
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY | hY
  · -- an empty coordinate type carries a subsingleton unitary group
    haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY
    apply Subtype.ext
    ext i j
    exact isEmptyElim i
  · have hx' : CoronaMFInvisible x :=
      actualCoronaMFInvisible_iff_coronaMFInvisible.mp hx
    -- the printed amplification: `π^{⊕(n+1)}` on strictly increasing dimensions
    have h1 := hx' (DirectSumAmplification.directSumModel Y)
      (DirectSumAmplification.card_directSumModel_pos Y hY)
      (DirectSumAmplification.directSumCoronaRep Y phi)
    have hnull :
        (fun n ↦ DirectSumAmplification.directSumRep Y phi n x) ∈
          nullCofiniteOpSubgroup (DirectSumAmplification.directSumModel Y) := by
      have h2 : (QuotientGroup.mk'
          (nullCofiniteOpSubgroup (DirectSumAmplification.directSumModel Y)))
          (fun n ↦ DirectSumAmplification.directSumRep Y phi n x) = 1 := h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    apply Subtype.ext
    exact DirectSumAmplification.opLength_eq_zero_of_null Y phi x hnull

/-- **Stability converts finite-dimensional blindness into MF
blindness.** -/
theorem fdUnitaryResidual_le_coronaMFResidual [Countable G]
    (hstab : IsPointNormMatriciallyStable G) :
    fdUnitaryResidual G ≤ coronaMFResidual G := by
  intro x hx X hX rho
  by_contra hne
  obtain ⟨A⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
      X rho hne
  obtain ⟨pi, hpi⟩ := hstab A.toOpAlmostRepresentation
  have hδ := A.separation_pos
  obtain ⟨Nz, hNz⟩ := hpi x (A.separation / 3) (by linarith)
  obtain ⟨N1, hN1⟩ := hpi 1 (A.separation / 3) (by linarith)
  set n := max Nz N1 with hn
  have hz := hNz n (le_max_left _ _)
  have h1 := hN1 n (le_max_right _ _)
  have hπx : pi n x = 1 :=
    mem_fdUnitaryResidual_iff.mp hx (A.model n) (pi n)
  have hπ1 : pi n (1 : G) = 1 := map_one _
  have hsep := A.marked_separated n
  -- triangle through the genuine representation
  have htri : ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) -
      A.map n 1‖ ≤
      ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) -
        (pi n x : Matrix (A.model n) (A.model n) ℂ)‖ +
      ‖(pi n 1 : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ := by
    have h2 : ((pi n x : Matrix (A.model n) (A.model n) ℂ)) =
        ((pi n 1 : Matrix (A.model n) (A.model n) ℂ)) := by
      rw [hπx, hπ1]
    calc ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ =
        dist (A.map n x : Matrix (A.model n) (A.model n) ℂ)
          (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) :=
          (dist_eq_norm _ _).symm
      _ ≤ dist (A.map n x : Matrix (A.model n) (A.model n) ℂ)
            (pi n x : Matrix (A.model n) (A.model n) ℂ) +
          dist (pi n x : Matrix (A.model n) (A.model n) ℂ)
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) :=
          dist_triangle _ _ _
      _ = ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) -
            (pi n x : Matrix (A.model n) (A.model n) ℂ)‖ +
          ‖(pi n 1 : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ := by
          rw [dist_eq_norm, dist_eq_norm, h2]
  have hflip : ‖(pi n 1 : Matrix (A.model n) (A.model n) ℂ) -
      (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ =
      ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
        (pi n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
    norm_sub_rev _ _
  have hlt : ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) -
      A.map n 1‖ < A.separation := by
    calc ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ ≤
        ‖(A.map n x : Matrix (A.model n) (A.model n) ℂ) -
          (pi n x : Matrix (A.model n) (A.model n) ℂ)‖ +
        ‖(pi n 1 : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ := htri
      _ ≤ A.separation / 3 + A.separation / 3 := by
          rw [hflip]
          exact add_le_add hz h1
      _ < A.separation := by linarith
  exact absurd hsep (not_le_of_gt hlt)

/-- **Matricial stability identifies the radicals.** -/
theorem actualCoronaMFResidual_eq_fdUnitaryResidual :
    ∀ {G : Type u} [Group G] [Countable G]
      (_hstab : IsPointNormMatriciallyStable G),
      actualCoronaMFResidual G = fdUnitaryResidual G := by
  intro G _ _ hstab
  refine le_antisymm actualCoronaMFResidual_le_fdUnitaryResidual ?_
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  exact fdUnitaryResidual_le_coronaMFResidual hstab

/-- A matricially stable group with nontrivial finite-dimensional
residual is not MF. -/
theorem not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot :
    ∀ {G : Type u} [Group G] [Countable G]
      (_hstab : IsPointNormMatriciallyStable G)
      (_hne : fdUnitaryResidual G ≠ ⊥),
      ¬ IsCDEOperatorMF G := by
  intro G _ _ hstab hne hMF
  apply hne
  rw [← actualCoronaMFResidual_eq_fdUnitaryResidual hstab]
  exact isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF

end MatricialStabilityRadical
end GroupApproximation
