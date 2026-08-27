import GroupApproximation.Analysis.CollapseNormalizedSetup
import GroupApproximation.Analysis.CollapseUnitaryLift
import GroupApproximation.Analysis.PrintedCornerRelabelling

/-!
# Central corners of a norm-matrix corona representation

This is the manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Lemma `lem:central-corona-corner`.

The conclusion retains the projection lift, the increasing subsequence, and
the polar-corrected corner representation.  It also records inside the
original corona that the coordinate compressions represent `q * rho(g)`.
Thus the last convergence clause is precisely the assertion that the corona
class of the resulting corner representation is the corner representation
`g \mapsto q rho(g)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix Topology
open CollapseUnitaryLift CollapseNormalizedSetup
open PrintedCornerCompression PrintedCornerRelabelling
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Lemma `lem:central-corona-corner`.**  A nonzero central projection of a
countable norm-matrix-corona representation yields, on an infinite coordinate
subsequence, an operator-norm asymptotic representation on nonzero corners.

The existential `PrintedCornerData` contains the actual polar-corrected maps;
its `cornerRepresentation` is an `OpAlmostRepresentation`.  The penultimate
clauses follow the field order of Lemma `lem:central-corona-corner`: `Q` lifts
the printed `q`, `φ` is the infinite coordinate subsequence, `D.q` and `D.V`
are the relabelled `q_n` and `U_n(g)`, with `U_n(1)=I`, and every
`D.cornerModel` is nonzero.  In the concrete corner coordinates the identity
matrix is the projection `q_n`; accordingly the two exact identity clauses for
`cornerMap` and `cornerRepresentation.map` formalize `W_n(1)=q_n`.
For each `g`, the final paired clause first identifies the uncorrected
compression class with the displayed corner value `q rho(g)`, then states
that the actual polar-corrected map `D.cornerRepresentation.map k g` differs
from that compression by a norm-null sequence. -/
def CentralCoronaCorner : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∃ (Q : BoundedMatrixSequence (fun n ↦ X n)) (φ : ℕ → ℕ)
      (D : PrintedCornerData G (fun k ↦ X (φ k))),
      StrictMono φ ∧
      (∀ n, IsOrthogonalProjectionMatrix
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ X n) Q = q ∧
      (∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ k g, (D.V k g : Matrix (X (φ k)) (X (φ k)) ℂ) =
        CollapseUnitaryLift.liftFam X rho g (φ k)) ∧
      (∀ k, D.V k (1 : G) = 1) ∧
      (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
      (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
      (∀ k, D.cornerMap k (1 : G) = 1) ∧
      (∀ k, D.cornerRepresentation.map k (1 : G) = 1) ∧
      (∀ g : G,
        normMatrixCStarCoronaMk (fun n ↦ X n)
              (Q * unitarySequenceBounded X
                (CollapseUnitaryLift.liftFam X rho g) * Q)
            = q * ((rho g : unitary
                (NormMatrixCStarCorona (fun n ↦ X n))) :
                  NormMatrixCStarCorona (fun n ↦ X n)) ∧
        Tendsto (fun k ↦
          ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
            - D.compress k g‖) atTop (nhds 0))

/-- Closed proof of the central-corona-corner lemma. -/
theorem manuscriptCentralCoronaCorner : CentralCoronaCorner := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral
  obtain ⟨Q, omega, hQproj, hQmk, homegaCof, homegaRank⟩ :=
    CollapseNormalizedSetup.exists_projection_lift_and_ultrafilter
      X q hqstar hqid hqne
  let V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ :=
    fun n g ↦ CollapseUnitaryLift.liftFam X rho g n
  have hVclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun n ↦ X n)
          (unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g))
        = ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    exact congrArg Subtype.val
      (CollapseUnitaryLift.unitarySequenceToCorona_liftFam X rho g)
  have hcommCof : ∀ g : G, IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g) * Q -
        Q * unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g)) := by
    intro g
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, map_mul, map_mul,
      hVclass g, hQmk, hcentral g, sub_self]
  have hcommOmega : ∀ g : G, Tendsto (fun n ↦
      ‖(V n g : Matrix (X n) (X n) ℂ) *
          (Q : ∀ n, Matrix (X n) (X n) ℂ) n -
        (Q : ∀ n, Matrix (X n) (X n) ℂ) n *
          (V n g : Matrix (X n) (X n) ℂ)‖)
      (omega : Filter ℕ) (nhds 0) := by
    intro g
    have h := (hcommCof g).mono_left homegaCof
    refine h.congr' (Eventually.of_forall fun n ↦ ?_)
    rw [PrintedCornerRelabelling.commutator_coord X
      (unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g)) Q n,
      unitarySequenceBounded_apply]
  have hnonzero : {n : ℕ |
      (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0} ∈ (omega : Filter ℕ) := by
    filter_upwards [homegaRank] with n hn
    intro hzero
    have hrankZero :
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n).rank = 0 := by
      rw [hzero]
      exact Matrix.rank_zero
    exact (Nat.ne_of_gt hn) hrankZero
  have hmul : ∀ g h : G, Tendsto (fun n ↦
      ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
        (V n g : Matrix (X n) (X n) ℂ) *
          (V n h : Matrix (X n) (X n) ℂ)‖) atTop (nhds 0) := by
    intro g h
    simpa only [V, Nat.cofinite_eq_atTop] using
      (CollapseUnitaryLift.tendsto_defect X rho g h)
  obtain ⟨φ, hφmono, hφne, hφcomm⟩ :=
    PrintedCornerRelabelling.exists_relabelling homegaCof V
      (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n)
      hnonzero hcommOmega
  let D : PrintedCornerData G (fun k ↦ X (φ k)) :=
    PrintedCornerRelabelling.relabelled V
      (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n)
      φ hφmono hQproj hφne hmul hφcomm
  have hcornerClass : ∀ g : G,
      normMatrixCStarCoronaMk (fun n ↦ X n)
          (Q * unitarySequenceBounded X
            (CollapseUnitaryLift.liftFam X rho g) * Q)
        = q * ((rho g : unitary
            (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    rw [map_mul, map_mul, hQmk, hVclass g, mul_assoc, hcentral g,
      ← mul_assoc, hqid]
  have hcornerCorrection : ∀ g : G, Tendsto (fun k ↦
      ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
        - D.compress k g‖) atTop (nhds 0) :=
    PrintedCornerData.cornerMap_sub_compress_tendsto D
  have hVone : ∀ k, D.V k (1 : G) = 1 := by
    intro k
    change CollapseUnitaryLift.liftFam X rho (1 : G) (φ k) = 1
    exact CollapseUnitaryLift.liftFam_one_apply X rho (φ k)
  exact ⟨Q, φ, D, hφmono, hQproj, hQmk, fun _ ↦ rfl, fun _ _ ↦ rfl, hVone,
    PrintedCornerData.cornerModel_card_pos D, fun _ _ ↦ HEq.rfl,
    fun k ↦ PrintedCornerData.cornerMap_one_of_V_one D k (hVone k),
    fun k ↦ PrintedCornerData.cornerRepresentation_map_one_of_V_one D k (hVone k),
    fun g ↦ ⟨hcornerClass g, hcornerCorrection g⟩⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
