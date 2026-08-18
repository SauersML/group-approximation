import GroupApproximation.Analysis.MatrixReindexHilbertSchmidt
import GroupApproximation.Sofic.ManuscriptKazhdanTransport

/-!
# Kazhdan transport over an arbitrary finite-model family

`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` is the literal
Section-3 theorem (`non_mf_groups_exist.tex`, `\label{thm:kazhdan-transport}`),
proved by the printed route: the norm ultraproduct `B_ω`, the Kazhdan
projection, one-sided compression, and finiteness.  It is stated in the
manuscript's own coordinates, so its models are the literal matrix algebras
`M_{d n}(ℂ)` — in Lean, `naturalFiniteModel (d n)`, carried by `Fin (d n)`.

Proof-ledger rows `FN.03` and `ID.05` ask two consumers to stop invoking the
Appendix-B surrogate `finiteStageKazhdanTransport` and invoke the literal
theorem instead.  Those consumers are stated over an arbitrary
`OpAlmostRepresentation`, whose coordinates are arbitrary finite models rather
than `Fin (d n)`, so the rewiring is not a citation swap: it needs the literal
theorem *over an arbitrary model family*.  `generalModelKazhdanTransport` is
that, and it is derived from the literal theorem by a change of basis, so this
file contains no second proof of transport — the mathematics is still the
printed ultraproduct argument.

The change of basis rests on `Analysis/MatrixReindexHilbertSchmidt`, whose
`hsNormSq_naturalize` is the invariance the transport statement needs and the
corpus did not have: the transport hypothesis and conclusion are written in the
normalized Hilbert--Schmidt norm, where only the operator-norm invariance was
previously available.

Nothing here rewires the consumers.  That is the next step, and per the lane
protocol it waits on a green build of this module.
-/

namespace GroupApproximation
namespace GeneralModelTransport

open KazhdanAsymptoticCommutant MatrixReindexHS
open Matrix
open scoped Matrix.Norms.L2Operator

universe u w

-- `[Group H]` is deliberately NOT a section variable: an instance binder whose
-- type mentions an included variable is itself included automatically, and only
-- `generalModelKazhdanTransport` uses the group structure of `H`.  Left in the
-- section it would be an unused section variable in the four declarations
-- below, which this project's linter treats as fatal.
variable {H : Type u}

/-! ## Carrying the data onto the literal coordinates -/

/-- An operator-norm asymptotic representation, read in the literal natural
coordinates of the same dimensions. -/
noncomputable def naturalizeUnitary (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (n : ℕ) (g : H) :
    Matrix.unitaryGroup (naturalizedModel Y n) ℂ :=
  unitaryReindexEquiv (Fintype.equivFin (Y n)) (U n g)

/-- A matrix sequence, read in the literal natural coordinates. -/
noncomputable def naturalizeSeq (Y : ℕ → FiniteModel)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ) (n : ℕ) :
    Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ :=
  naturalize Y n (x n)

@[simp] theorem naturalizeSeq_apply (Y : ℕ → FiniteModel)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ) (n : ℕ) :
    naturalizeSeq Y x n = naturalize Y n (x n) := rfl

theorem coe_naturalizeUnitary (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (n : ℕ) (g : H) :
    ((naturalizeUnitary Y U n g :
        Matrix.unitaryGroup (naturalizedModel Y n) ℂ) :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ)
      = naturalize Y n (U n g : Matrix (Y n) (Y n) ℂ) :=
  coe_unitaryReindexEquiv Y n (U n g)

/-- Reindexing a unitary conjugation, in one step.  Split out of the transport
proof because a single `simp only` over the whole conjugated commutator never
exposed a `naturalize (·ᴴ)` for `naturalize_conjTranspose` to fire on; here the
three rewrites are explicit and the adjoint is reached by construction. -/
theorem naturalize_conj (Y : ℕ → FiniteModel) (n : ℕ)
    (u a : Matrix (Y n) (Y n) ℂ) :
    naturalize Y n (u * a * uᴴ)
      = naturalize Y n u * naturalize Y n a * (naturalize Y n u)ᴴ := by
  rw [map_mul, map_mul, naturalize_conjTranspose]

/-- Reindexing a commutator against a transported unitary.  This is the shape
both the hypothesis and the conclusion of the transport theorem are stated in,
so it is proved once and used at both ends. -/
theorem naturalize_commutator (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (n : ℕ) (g : H)
    (a : Matrix (Y n) (Y n) ℂ) :
    naturalize Y n a *
        (naturalizeUnitary Y U n g :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
      (naturalizeUnitary Y U n g :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
        naturalize Y n a
      = naturalize Y n (a * (U n g : Matrix (Y n) (Y n) ℂ) -
          (U n g : Matrix (Y n) (Y n) ℂ) * a) := by
  rw [map_sub, map_mul, map_mul, coe_naturalizeUnitary]

/-! ## The statement over a general model family -/

/-- The Hilbert--Schmidt commutator-vanishing predicate of
`\label{thm:kazhdan-transport}`, over an arbitrary finite-model family.  At
`Y = fun n ↦ naturalFiniteModel (d n)` it is
`KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing`. -/
def GeneralHSCommutatorVanishing
    (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (g : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    Real.sqrt (hsNormSq (Y n) (x n * U n g - U n g * x n)) ≤ ε

/-- **Kazhdan transport over an arbitrary finite-model family.**

The statement of `manuscriptKazhdanTransport` with the manuscript's literal
matrix coordinates `M_{d n}(ℂ)` replaced by an arbitrary family of finite
models.  The proof reindexes the data onto the literal coordinates, applies the
literal theorem there, and carries the conclusion back; no hypothesis is added,
dropped or weakened, and the transport itself is not reproved. -/
theorem generalModelKazhdanTransport
    {Γ : Type} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (Y : ℕ → FiniteModel) (hY : ∀ n, 0 < Fintype.card (Y n))
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, GeneralHSCommutatorVanishing Y U x (iota γ)) :
    ∀ γ : Γ, GeneralHSCommutatorVanishing Y U (fun n ↦
      (U n s : Matrix (Y n) (Y n) ℂ) * x n *
        (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) (iota γ) := by
  classical
  -- Almost multiplicativity survives, because reindexing is isometric.
  have hU' : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(naturalizeUnitary Y U n (g * h) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n g :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeUnitary Y U n h‖ ≤ ε := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := hU g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hrw : (naturalizeUnitary Y U n (g * h) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n g :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeUnitary Y U n h
        = naturalize Y n ((U n (g * h) : Matrix (Y n) (Y n) ℂ) -
            (U n g : Matrix (Y n) (Y n) ℂ) * U n h) := by
      simp only [map_sub, map_mul, coe_naturalizeUnitary]
    rw [hrw, norm_naturalize]
    exact hN n hn
  -- Uniform boundedness survives for the same reason.
  have hbound' : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖naturalizeSeq Y x n‖ ≤ M := by
    obtain ⟨M, hM0, hM⟩ := hbound
    refine ⟨M, hM0, fun n ↦ ?_⟩
    rw [naturalizeSeq_apply, norm_naturalize]
    exact hM n
  -- The asymptotic-commutant hypothesis survives by Hilbert--Schmidt
  -- invariance, which is the piece the corpus was missing.
  have hx' : ∀ γ : Γ, NaturalHSCommutatorVanishing
      (fun n ↦ Fintype.card (Y n)) (naturalizeUnitary Y U)
      (naturalizeSeq Y x) (iota γ) := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    show Real.sqrt (hsNormSq (naturalizedModel Y n)
      (naturalizeSeq Y x n *
          (naturalizeUnitary Y U n (iota γ) :
            Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n (iota γ) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeSeq Y x n)) ≤ ε
    have hrw : naturalizeSeq Y x n *
          (naturalizeUnitary Y U n (iota γ) :
            Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n (iota γ) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeSeq Y x n
        = naturalize Y n (x n * (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n) := by
      simp only [map_sub, map_mul, coe_naturalizeUnitary, naturalizeSeq_apply]
    rw [hrw, hsNormSq_naturalize]
    exact hN n hn
  -- The literal Section-3 theorem, on the literal coordinates.
  have hmain := manuscriptKazhdanTransport hT iota s hs
    (fun n ↦ Fintype.card (Y n)) hY (naturalizeUnitary Y U) hU'
    (naturalizeSeq Y x) hbound' hx'
  -- Carry the conclusion back.
  intro γ ε hε
  obtain ⟨N, hN⟩ := hmain γ ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hstep := hN n hn
  -- First collapse the conjugated triple into a single reindexed matrix.  This
  -- is the only step where the adjoint is involved, and it is `naturalize_conj`.
  have hPconj : (naturalizeUnitary Y U n s :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
        naturalizeSeq Y x n *
        (naturalizeUnitary Y U n s :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ)ᴴ
      = naturalize Y n ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
          (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) := by
    rw [naturalize_conj, coe_naturalizeUnitary, naturalizeSeq_apply]
  -- `simp only`, not `rw`: `hstep` carries the conjugated block as an
  -- un-beta-reduced `(fun n => …) n`, which `rw` matches syntactically and so
  -- cannot see through, while `simp only` beta-reduces first.
  simp only [hPconj] at hstep
  -- What is left is the commutator shape, which `naturalize_commutator`
  -- already handles at both ends of the proof.
  simp only [naturalize_commutator Y U n (iota γ)
    ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)ᴴ)] at hstep
  -- `hstep` spells the index as `naturalFiniteModel (Fintype.card (Y n))`,
  -- which is `naturalizedModel Y n` by definition but not syntactically, so
  -- `hsNormSq_naturalize` cannot match it.  Restate at the spelling the lemma
  -- is stated in -- the two are definitionally equal, so this is `hstep`
  -- itself -- and only then rewrite.
  have hstep' : Real.sqrt (hsNormSq (naturalizedModel Y n)
      (naturalize Y n ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
          (U n s : Matrix (Y n) (Y n) ℂ)ᴴ *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ)))) ≤ ε := hstep
  rw [hsNormSq_naturalize] at hstep'
  exact hstep'

end GeneralModelTransport
end GroupApproximation
