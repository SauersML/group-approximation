import GroupApproximation.Analysis.PrintedCornerCompression
import GroupApproximation.Analysis.PrintedDiagonalSubsequence
import GroupApproximation.Analysis.OmegaCoronaKazhdanProjection

/-!
# `NK.07`'s second clause, end to end

Proof-ledger row `NK.07`.  The row's second clause is one printed sentence with
three moves in it:

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)`, nonzero along `ω` and with
> `‖[q_n, V_{g,n}]‖ →_ω 0` for every `g ∈ H̄` … To obtain ordinary convergence
> before compressing, pass to a subsequence … Compressing every model to
> `q_n M_{d_n}(ℂ) q_n` and polar-correcting now yields an operator-norm
> asymptotic representation `(W_{g,n})` of `H̄` on nonzero blocks.

Each move is proved in its own file and this one joins them on the printed
objects:

* the lift is `OmegaCoronaKazhdanProjection.manuscriptComplementProjectionLift`,
  which produces genuine projection matrices whose class in `B_ω` is the printed
  `q = 1 − P`;
* the relabelling is `Analysis/PrintedDiagonalSubsequence`, the printed `A_j`;
* the compression is `Analysis/PrintedCornerCompression`.

`manuscriptCoronaCornerRepresentation` is the three of them as one statement:
the projections it produces are the lifted ones — their corona class is named in
the conclusion, not merely asserted to exist — the subsequence is the printed
one, and the corner models are all nonzero.

## The one hypothesis that is not corona data

`OmegaUnitaryRep` requires the multiplication defects of `(V_{g,n})` to vanish
along `ω` only.  The printed proof has more than that at this point: the models
come from `prop:mf-equivalences` applied along an exhaustion of `H̄` (row
`NK.03`), so they are an operator-norm asymptotic representation in the
ordinary sense already.  That is the hypothesis `hmul` below, and it is the
printed one.  It is a hypothesis rather than a consequence because the ordinary
statement is strictly stronger than the `ω` statement `OmegaUnitaryRep` carries,
and taking it from the print is honest where deriving it would not be.
-/

namespace GroupApproximation
namespace PrintedCornerRelabelling

open Filter Topology Matrix
open KazhdanCornerMatrices
open PrintedCornerCompression
open AbstractSpectralGap VectorOmegaAction VectorOmegaCoronaAction
open VectorOmegaKazhdanGap VectorHilbertUltraproduct
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

universe u

/-! ## The relabelling -/

section Relabel

variable {G : Type u} [Group G] {Y : ℕ → FiniteModel} {ω : Ultrafilter ℕ}

omit [Group G] in
/-- **The printed `A_j`, applied to the compression paragraph's data.**  The
`ω`-large set is the printed `q_n ≠ 0` and the vanishing family is the printed
`‖[q_n, V_{g,n}]‖`, one member for each `g` in the enumeration of `H̄`. -/
theorem exists_relabelling [Countable G] (hω : (ω : Filter ℕ) ≤ cofinite)
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hne : {n | q n ≠ 0} ∈ (ω : Filter ℕ))
    (hcomm : ∀ g : G, Tendsto (fun n ↦
        ‖(V n g : Matrix (Y n) (Y n) ℂ) * q n -
          q n * (V n g : Matrix (Y n) (Y n) ℂ)‖) (ω : Filter ℕ) (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, q (φ k) ≠ 0) ∧
      ∀ g : G, Tendsto (fun k ↦
        ‖(V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * q (φ k) -
          q (φ k) * (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)‖) atTop (𝓝 0) :=
  PrintedDiagonalSubsequence.exists_strictMono_mem_tendsto_zero hω hne
    (fun (g : G) n ↦ ‖(V n g : Matrix (Y n) (Y n) ℂ) * q n -
      q n * (V n g : Matrix (Y n) (Y n) ℂ)‖) hcomm

/-- **The relabelled data**: `(V_{g,n_j}, q_{n_j})` along the printed
subsequence, packaged as the input the compression consumes. -/
def relabelled
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ) (φ : ℕ → ℕ) (hmono : StrictMono φ)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (q n))
    (hne : ∀ k, q (φ k) ≠ 0)
    (hmul : ∀ g h : G, Tendsto (fun n ↦
        ‖(V n (g * h) : Matrix (Y n) (Y n) ℂ) -
          (V n g : Matrix (Y n) (Y n) ℂ) * V n h‖) atTop (𝓝 0))
    (hcomm : ∀ g : G, Tendsto (fun k ↦
        ‖(V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * q (φ k) -
          q (φ k) * (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)‖) atTop (𝓝 0)) :
    PrintedCornerData G (fun k ↦ Y (φ k)) where
  V := fun k g ↦ V (φ k) g
  q := fun k ↦ q (φ k)
  q_projection := fun k ↦ hproj (φ k)
  q_ne_zero := hne
  mul_vanishing := fun g h ↦ (hmul g h).comp hmono.tendsto_atTop
  commutator_vanishing := hcomm

/-- The same package, built from hypotheses already stated along the
subsequence.  `relabelled` composes an `atTop` hypothesis with `φ`; this one is
handed the composed statements directly, which is what the extraction below
produces when the multiplication defects are extracted alongside the
commutators instead of assumed. -/
def relabelledDirect
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ) (φ : ℕ → ℕ)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (q n))
    (hne : ∀ k, q (φ k) ≠ 0)
    (hmul : ∀ g h : G, Tendsto (fun k ↦
        ‖(V (φ k) (g * h) : Matrix (Y (φ k)) (Y (φ k)) ℂ) -
          (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * V (φ k) h‖) atTop (𝓝 0))
    (hcomm : ∀ g : G, Tendsto (fun k ↦
        ‖(V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * q (φ k) -
          q (φ k) * (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)‖) atTop (𝓝 0)) :
    PrintedCornerData G (fun k ↦ Y (φ k)) where
  V := fun k g ↦ V (φ k) g
  q := fun k ↦ q (φ k)
  q_projection := fun k ↦ hproj (φ k)
  q_ne_zero := hne
  mul_vanishing := hmul
  commutator_vanishing := hcomm

/-- **The printed `A_j`, with the multiplication defects carried in it.**

The printed `A_j` constrains `q_n ≠ 0` and the commutators, because at that
point in the printed proof the models are *already* an operator-norm asymptotic
representation in the ordinary sense — `prop:mf-equivalences` along an
exhaustion of `H̄` supplies that, which is row `NK.03`.  The corona data alone
supplies only the `ω` form, so assuming the ordinary form would be an
assumption this file has no right to make.

It does not have to.  `H̄ ⊕ H̄ × H̄` is countable whenever `H̄` is, so the
multiplication defects go into the extracted family beside the commutators and
come out as ordinary limits with them.  The subsequence is one subsequence and
the conclusion carries no hypothesis the corona did not supply. -/
theorem exists_relabelling_full [Countable G] (hω : (ω : Filter ℕ) ≤ cofinite)
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hne : {n | q n ≠ 0} ∈ (ω : Filter ℕ))
    (hcomm : ∀ g : G, Tendsto (fun n ↦
        ‖(V n g : Matrix (Y n) (Y n) ℂ) * q n -
          q n * (V n g : Matrix (Y n) (Y n) ℂ)‖) (ω : Filter ℕ) (𝓝 0))
    (hmul : ∀ g h : G, Tendsto (fun n ↦
        ‖(V n (g * h) : Matrix (Y n) (Y n) ℂ) -
          (V n g : Matrix (Y n) (Y n) ℂ) * V n h‖) (ω : Filter ℕ) (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, q (φ k) ≠ 0) ∧
      (∀ g : G, Tendsto (fun k ↦
        ‖(V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * q (φ k) -
          q (φ k) * (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)‖) atTop (𝓝 0)) ∧
      (∀ g h : G, Tendsto (fun k ↦
        ‖(V (φ k) (g * h) : Matrix (Y (φ k)) (Y (φ k)) ℂ) -
          (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) * V (φ k) h‖)
        atTop (𝓝 0)) := by
  obtain ⟨φ, hmono, hmem, hconv⟩ :=
    PrintedDiagonalSubsequence.exists_strictMono_mem_tendsto_zero
      (ι := G ⊕ G × G) hω hne
      (fun i n ↦ match i with
        | Sum.inl g => ‖(V n g : Matrix (Y n) (Y n) ℂ) * q n -
            q n * (V n g : Matrix (Y n) (Y n) ℂ)‖
        | Sum.inr gh => ‖(V n (gh.1 * gh.2) : Matrix (Y n) (Y n) ℂ) -
            (V n gh.1 : Matrix (Y n) (Y n) ℂ) * V n gh.2‖)
      (fun i ↦ by cases i with
        | inl g => exact hcomm g
        | inr gh => exact hmul gh.1 gh.2)
  exact ⟨φ, hmono, hmem, fun g ↦ hconv (Sum.inl g),
    fun g h ↦ hconv (Sum.inr (g, h))⟩

@[simp] theorem relabelled_q
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ) (φ : ℕ → ℕ) (hmono : StrictMono φ)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (q n))
    (hne : ∀ k, q (φ k) ≠ 0) (hmul) (hcomm) (k : ℕ) :
    (relabelled V q φ hmono hproj hne hmul hcomm).q k = q (φ k) := rfl

@[simp] theorem relabelled_V
    (V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ)
    (q : ∀ n, Matrix (Y n) (Y n) ℂ) (φ : ℕ → ℕ) (hmono : StrictMono φ)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (q n))
    (hne : ∀ k, q (φ k) ≠ 0) (hmul) (hcomm) (k : ℕ) (g : G) :
    ((relabelled V q φ hmono hproj hne hmul hcomm).V k g :
        Matrix (Y (φ k)) (Y (φ k)) ℂ)
      = (V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ) := rfl

end Relabel

/-! ## From the corona lift to the corner representation -/

section Corona

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]
variable {G : Type u} [Group G]

open OmegaCoronaKazhdanProjection

omit [∀ n, Nonempty (Y n)] in
/-- The coordinates of a commutator of bounded sequences are the commutators of
the coordinates.  `lp` at `∞` multiplies pointwise; this is that, written out,
because the printed estimate is about coordinates. -/
theorem commutator_coord (a b : BoundedMatrixSequence (Idx Y)) (n : ℕ) :
    ((a * b - b * a : BoundedMatrixSequence (Idx Y)) :
        ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
          (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
        - (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
          (a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n := by
  have hab : ((a * b : BoundedMatrixSequence (Idx Y)) :
      ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
        (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n := by
    ext i j; rfl
  have hba : ((b * a : BoundedMatrixSequence (Idx Y)) :
      ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
        (a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n := by
    ext i j; rfl
  rw [lp.coeFn_sub, Pi.sub_apply, hab, hba]

omit [∀ n, Nonempty (Y n)] in
/-- The coordinates of a multiplication defect are the coordinate defects. -/
theorem mulDefect_coord (a b c : BoundedMatrixSequence (Idx Y)) (n : ℕ) :
    ((a - b * c : BoundedMatrixSequence (Idx Y)) :
        ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
        - (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
          (c : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n := by
  have hbc : ((b * c : BoundedMatrixSequence (Idx Y)) :
      ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (b : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
        (c : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n := by
    ext i j; rfl
  rw [lp.coeFn_sub, Pi.sub_apply, hbc]

/-- **`NK.07`'s second clause, with no hypothesis beyond the corona data.**

Identical to `manuscriptCoronaCornerRepresentation` except that the ordinary
multiplicativity of `(V_{g,n})` is not assumed.  `OmegaUnitaryRep` carries the
`ω` form and that is all this theorem uses: the multiplication defects join the
commutators inside the printed `A_j`, and one subsequence delivers both in the
ordinary sense.  Every hypothesis below is corona data or a printed hypothesis
of `thm:abstract-nk`; none of them is a statement the printed proof obtains
from elsewhere and this file takes on trust. -/
theorem manuscriptCoronaCornerRepresentationUnconditional [Countable G]
    (hω : (ω : Filter ℕ) ≤ cofinite) (R : OmegaUnitaryRep Y ω G)
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (S : Finset G) (hS : S.Nonempty) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1)
    (hnorm : ∀ g : G, ∀ k ∈ Subgroup.closure (S : Set G),
      g * k * g⁻¹ ∈ Subgroup.closure (S : Set G))
    (hnt : ∃ g ∈ S, ((repUnitary' Y ω R g :
      unitary (VecOmega Y ω →L[ℂ] VecOmega Y ω)) :
      VecOmega Y ω →L[ℂ] VecOmega Y ω) ≠ 1) :
    ∃ (qn : BoundedMatrixSequence (Idx Y)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ n, IsOrthogonalProjectionMatrix
        ((qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)) ∧
      filterMatrixCStarCoronaMk (Idx Y) (ω : Filter ℕ) qn
        = (1 : FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ))
          - manuscriptKazhdanProjection Y ω R S (1 - ε ^ 2 / (4 * S.card)) ∧
      ∃ D : PrintedCornerData G (fun k ↦ Y (φ k)),
        (∀ k, D.q k = (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) (φ k)) ∧
        (∀ k g, (D.V k g : Matrix (Y (φ k)) (Y (φ k)) ℂ)
            = (R.V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)) ∧
        (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
        (∀ g : G, Tendsto (fun k ↦
          ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
            - D.compress k g‖) atTop (𝓝 0)) := by
  obtain ⟨qn, hproj, hmk, hnezero, hnull⟩ :=
    manuscriptComplementProjectionLift Y ω R hQ S hS hQS hone hsymm hεone hnorm hnt
  have hcomm : ∀ g : G, Tendsto (fun n ↦
      ‖(R.V n g : Matrix (Y n) (Y n) ℂ) *
          (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n -
        (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
          (R.V n g : Matrix (Y n) (Y n) ℂ)‖) (ω : Filter ℕ) (𝓝 0) := by
    intro g
    refine (hnull g).congr fun n ↦ ?_
    rw [commutator_coord Y (unitarySeq Y R.V g) qn n, unitarySeq_apply]
  -- the `ω` form of multiplicativity, which is all `OmegaUnitaryRep` carries
  have hmulω : ∀ g h : G, Tendsto (fun n ↦
      ‖(R.V n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (R.V n g : Matrix (Y n) (Y n) ℂ) * R.V n h‖) (ω : Filter ℕ) (𝓝 0) := by
    intro g h
    refine (R.mul_null g h).congr fun n ↦ ?_
    rw [mulDefect_coord Y (unitarySeq Y R.V (g * h)) (unitarySeq Y R.V g)
      (unitarySeq Y R.V h) n, unitarySeq_apply, unitarySeq_apply, unitarySeq_apply]
  obtain ⟨φ, hmono, hne, hcommφ, hmulφ⟩ :=
    exists_relabelling_full hω R.V
      (fun n ↦ (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n) hnezero hcomm hmulω
  refine ⟨qn, φ, hmono, hproj, hmk,
    relabelledDirect R.V (fun n ↦ (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n) φ
      hproj hne hmulφ hcommφ,
    fun _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_⟩
  · exact PrintedCornerData.cornerModel_card_pos _
  · exact PrintedCornerData.cornerMap_sub_compress_tendsto _

/-- **`NK.07`'s second clause, whole.**

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)`, nonzero along `ω` and with
> `‖[q_n, V_{g,n}]‖ →_ω 0` for every `g ∈ H̄` … pass to a subsequence …
> Compressing every model to `q_n M_{d_n}(ℂ) q_n` and polar-correcting now
> yields an operator-norm asymptotic representation `(W_{g,n})` of `H̄` on
> nonzero blocks.

The projections are the printed ones: their class in `B_ω` is `q = 1 − P` for
the printed `P`, which the conclusion states rather than assumes.  The
subsequence is the printed `A_j`.  The corner models are all nonzero, and
`PrintedCornerData.cornerRepresentation` of the data produced here is the
printed `(W_{g,n})` — an `OpAlmostRepresentation` of `H̄` by construction, whose
maps are the polar-corrected compressions and differ from them by `o(1)`. -/
theorem manuscriptCoronaCornerRepresentation [Countable G]
    (hω : (ω : Filter ℕ) ≤ cofinite) (R : OmegaUnitaryRep Y ω G)
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (S : Finset G) (hS : S.Nonempty) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1)
    (hnorm : ∀ g : G, ∀ k ∈ Subgroup.closure (S : Set G),
      g * k * g⁻¹ ∈ Subgroup.closure (S : Set G))
    (hnt : ∃ g ∈ S, ((repUnitary' Y ω R g :
      unitary (VecOmega Y ω →L[ℂ] VecOmega Y ω)) :
      VecOmega Y ω →L[ℂ] VecOmega Y ω) ≠ 1)
    (hmul : ∀ g h : G, Tendsto (fun n ↦
        ‖(R.V n (g * h) : Matrix (Y n) (Y n) ℂ) -
          (R.V n g : Matrix (Y n) (Y n) ℂ) * R.V n h‖) atTop (𝓝 0)) :
    ∃ (qn : BoundedMatrixSequence (Idx Y)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ n, IsOrthogonalProjectionMatrix
        ((qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)) ∧
      filterMatrixCStarCoronaMk (Idx Y) (ω : Filter ℕ) qn
        = (1 : FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ))
          - manuscriptKazhdanProjection Y ω R S (1 - ε ^ 2 / (4 * S.card)) ∧
      ∃ D : PrintedCornerData G (fun k ↦ Y (φ k)),
        (∀ k, D.q k = (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) (φ k)) ∧
        (∀ k g, (D.V k g : Matrix (Y (φ k)) (Y (φ k)) ℂ)
            = (R.V (φ k) g : Matrix (Y (φ k)) (Y (φ k)) ℂ)) ∧
        (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
        (∀ g : G, Tendsto (fun k ↦
          ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
            - D.compress k g‖) atTop (𝓝 0)) := by
  obtain ⟨qn, hproj, hmk, hnezero, hnull⟩ :=
    manuscriptComplementProjectionLift Y ω R hQ S hS hQS hone hsymm hεone hnorm hnt
  -- The printed `‖[q_n, V_{g,n}]‖ →_ω 0`, read on coordinates.
  have hcomm : ∀ g : G, Tendsto (fun n ↦
      ‖(R.V n g : Matrix (Y n) (Y n) ℂ) *
          (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n -
        (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n *
          (R.V n g : Matrix (Y n) (Y n) ℂ)‖) (ω : Filter ℕ) (𝓝 0) := by
    intro g
    refine (hnull g).congr fun n ↦ ?_
    rw [commutator_coord Y (unitarySeq Y R.V g) qn n, unitarySeq_apply]
  obtain ⟨φ, hmono, hne, hcommφ⟩ :=
    exists_relabelling hω R.V (fun n ↦ (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)
      hnezero hcomm
  refine ⟨qn, φ, hmono, hproj, hmk,
    relabelled R.V (fun n ↦ (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n) φ hmono
      hproj hne hmul hcommφ,
    fun _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_⟩
  · exact PrintedCornerData.cornerModel_card_pos _
  · exact PrintedCornerData.cornerMap_sub_compress_tendsto _

end Corona

end

end PrintedCornerRelabelling
end GroupApproximation
