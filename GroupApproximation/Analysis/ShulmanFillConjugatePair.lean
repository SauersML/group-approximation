import GroupApproximation.Analysis.ShulmanFillWordNorming

/-!
# Conjugating one factor, and what is left of Theorem 16

`WordNormingStatement` asks, for a word `y` of the amalgam, for *some*
compatible representation with an MF carrier that nearly attains `‖y‖`.  The
analytic construction does not search among all representations: it starts
from the compatible corona pair `(l, r)` supplied by the hypothesis and moves
only the second factor, by conjugating it with a unitary of the corona that
commutes with the amalgamated part.  Conjugation by such a unitary preserves
compatibility — that is `unitaryConj_comp_compatible` below — so every such
unitary produces a compatible representation whose carrier is again the
corona, hence MF.

`ConjugateWordNormingStatement` is the residual in that shape, and
`wordNorming_of_conjugateWordNorming` closes the word form of the input from
it.  What the residual asks is exactly the analytic core of Shulman's proof;
the rest of this docstring says how the peer lane's modules discharge it.

## The construction the residual asks for

Write `Q = ∏_n M_{k_n} / ⨁_n M_{k_n}` for the corona, `γ = l ∘ ι_A = r ∘ ι_B`
for the common image of `C`, and let `y` be a word in the two factor images.

1. **Unitalize.**  `Analysis/CompatibleCoronaSupportCorner` replaces the two
   possibly nonunital embeddings `φ_A`, `φ_B` of the printed hypothesis by
   unital ones into a relabelled corner corona: compatible faithful
   embeddings have the same support projection `φ_A(1) = φ_B(1)`, so a single
   projection lift unitalizes both at once.  This step is already proved.

2. **Discrete models.**  `ShulmanContractiveAsymptoticLift.lift` chooses, for
   each element, a representative whose every coordinate is bounded by the
   element's norm.  It yields contractive discrete asymptotic models
   `l_n : A₁ → M_{k_n}` and `r_n : A₂ → M_{k_n}` whose algebraic defects are
   null, by `NormCoronaAsymptoticLiftCore.tendsto_lift_mul` and its siblings.

3. **Asymptotic amalgamation.**  The two models agree asymptotically on `C`:
   `NormCoronaAsymptoticLift.tendsto_model_map_sub_of_comp_eq` gives
   `‖l_n(ι_A c) - r_n(ι_B c)‖ → 0` for one `c` from `l ∘ ι_A = r ∘ ι_B`, and
   `ShulmanDenseCompatibility.tendsto_norm_sub_of_dense` upgrades that from a
   dense sequence of `C` to every `c`, using contractivity and asymptotic
   additivity of the models.  This is the level at which the amalgamation
   constraint lives: it is an asymptotic identity, not an exact one.

4. **Unitaries commuting with the amalgamated part.**  The residual's unitary
   `u` is produced as a corona class of finite-dimensional unitaries `u_n`
   with `‖[u_n, l_n(ι_A c)]‖ → 0` for every `c`.  Two peer modules are the
   engine here: `ShulmanCoronaHalmos*` and `ShulmanHalmosDilation*` dilate a
   contraction with a small commutator defect to a unitary with a controlled
   defect, and `ShulmanUnitaryConjugationControl` turns finite commutator
   control on a dense sequence into asymptotic compatibility
   (`tendsto_conjugation_sub_of_initial_commutator_controls`).
   `ShulmanDiagonalConjugation.exists_strictMono_conjugate_compatibility`
   then extracts the subsequence along which the commutator estimates hold
   simultaneously.

5. **Generic position.**  The one genuinely analytic step: the `u_n` must be
   chosen so that the conjugated pair `(l_n, u_n r_n u_n^*)` reproduces, on
   the given word and up to `δ`, the supremum over *all* compatible pairs
   that defines the full amalgamated free product norm.  Diagonal selection
   (`ShulmanDiagonalSelection`) is the intended source of the `u_n`; the
   estimate itself is of Haagerup--Thorbjørnsen type and is not in the
   repository.

## Intermediate statements worth naming

* `commutantUnitary_of_asymptotic_commutator`: a sequence of unitaries
  `u_n ∈ U(k_n)` with `‖[u_n, l_n(ι_A c)]‖ → 0` for all `c` defines a unitary
  of `Q` commuting with `γ(C)`.  Pieces: `NormMatrixCoronaUnitary` for the
  class being unitary, `normMatrixCStarCoronaMk_eq_zero_iff` for the
  commutator vanishing in the quotient.
* `norm_eval_conjugateRepresentation_word`: for a word `y`, the norm
  `‖eval_{R_u} y‖` is the limsup over `n` of the norm of the same word
  evaluated in `(l_n, u_n r_n u_n^*)`.  This is the bridge between the corona
  statement and the finite-dimensional estimate, and it is where step 5 is
  actually used.  It needs only the quotient norm formula
  `norm_normMatrixCStarCoronaMk_eq_limsup` and the model defect estimates of
  step 2, so it is formalizable now.
* `exists_diagonal_unitaries_attaining_word_norm`: step 5 itself.

`GroupApproximation.lean` imports this module, and so does
`Manuscript.MFRecognition.RecognitionDebts`, so `thm:recognition` rests on it.
It was authored while builds were suspended and has not been elaborated since.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-! ## Conjugation by a unitary -/

variable {D : Type} [CStarAlgebra D]

/-- Conjugation by a unitary, as a unital `*`-algebra endomorphism. -/
def unitaryConj (u : unitary D) : D →⋆ₐ[ℂ] D where
  toFun x := (u : D) * x * star (u : D)
  map_one' := by
    rw [mul_one]
    exact Unitary.mul_star_self_of_mem u.2
  map_mul' x y := by
    show (u : D) * (x * y) * star (u : D)
      = ((u : D) * x * star (u : D)) * ((u : D) * y * star (u : D))
    have hu : star (u : D) * (u : D) = 1 := Unitary.star_mul_self_of_mem u.2
    calc (u : D) * (x * y) * star (u : D)
        = (u : D) * x * (star (u : D) * (u : D)) * y * star (u : D) := by
          rw [hu, mul_one]
          simp only [mul_assoc]
      _ = ((u : D) * x * star (u : D)) * ((u : D) * y * star (u : D)) := by
          simp only [mul_assoc]
  map_zero' := by
    show (u : D) * 0 * star (u : D) = 0
    simp
  map_add' x y := by
    show (u : D) * (x + y) * star (u : D)
      = (u : D) * x * star (u : D) + (u : D) * y * star (u : D)
    rw [mul_add, add_mul]
  commutes' c := by
    show (u : D) * algebraMap ℂ D c * star (u : D) = algebraMap ℂ D c
    have hcomm : (u : D) * algebraMap ℂ D c = algebraMap ℂ D c * (u : D) :=
      (Algebra.commutes c (u : D)).symm
    rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem u.2, mul_one]
  map_star' x := by
    show (u : D) * star x * star (u : D) = star ((u : D) * x * star (u : D))
    rw [star_mul, star_mul, star_star, mul_assoc]

@[simp] theorem unitaryConj_apply (u : unitary D) (x : D) :
    unitaryConj u x = (u : D) * x * star (u : D) := rfl

/-! ## Conjugating one factor of a compatible pair -/

variable {C A B : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]

/-- **Conjugation preserves compatibility.**  A unitary that commutes with the
image of the amalgamated algebra may be applied to one factor alone: the two
factor maps still agree on `C`. -/
theorem unitaryConj_comp_compatible
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (l : A →⋆ₐ[ℂ] D) (r : B →⋆ₐ[ℂ] D) (hlr : l.comp iA = r.comp iB)
    (u : unitary D)
    (hu : ∀ c : C, (u : D) * l (iA c) = l (iA c) * (u : D)) :
    l.comp iA = ((unitaryConj u).comp r).comp iB := by
  apply StarAlgHom.ext
  intro c
  have hc : l (iA c) = r (iB c) := DFunLike.congr_fun hlr c
  show l (iA c) = (u : D) * r (iB c) * star (u : D)
  rw [← hc, hu c, mul_assoc, Unitary.mul_star_self_of_mem u.2, mul_one]

/-- The compatible representation carried by a conjugated pair. -/
def conjugateRepresentation [Nontrivial D]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (l : A →⋆ₐ[ℂ] D) (r : B →⋆ₐ[ℂ] D) (hlr : l.comp iA = r.comp iB)
    (u : unitary D)
    (hu : ∀ c : C, (u : D) * l (iA c) = l (iA c) * (u : D)) :
    CStarAmalgamRepresentation iA iB :=
  CStarAmalgamRepresentation.ofCompatiblePair iA iB l ((unitaryConj u).comp r)
    (unitaryConj_comp_compatible iA iB l r hlr u hu)

/-! ## The residual, in the shape the construction produces -/

/-- **The analytic core of Theorem 16.**  Under the hypotheses of the printed
criterion, every word of the amalgam has its norm approximated by the
evaluation at a *conjugate* of a unital compatible corona pair, the conjugating
unitary commuting with the image of the amalgamated algebra.

Compared with `WordNormingStatement` nothing is left to choose but the models
and the unitary: the representation is built from them by
`conjugateRepresentation`, and its carrier is a corona, so the MF clause is
automatic. -/
def ConjugateWordNormingStatement : Prop :=
  ∀ {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁]
    [CStarAlgebra A₂] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    [Nonempty (CStarAmalgamRepresentation iA iB)],
      TopologicalSpace.SeparableSpace C →
      TopologicalSpace.SeparableSpace A₁ →
      TopologicalSpace.SeparableSpace A₂ →
      ∀ (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
        (phiA : A₁ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
        (phiB : A₂ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)),
        Function.Injective phiA → Function.Injective phiB →
          (∀ c : C, phiA (iA c) = phiB (iB c)) →
            ∀ y ∈ adjoinSet iA iB, ∀ δ : ℝ, 0 < δ →
              ∃ Z : ℕ → FiniteModel, ∃ hZ : ∀ n, Nonempty (Z n),
                letI : ∀ n, Nonempty (Z n) := hZ
                ∃ l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
                  ∃ r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
                    ∃ hlr : l.comp iA = r.comp iB,
                      ∃ u : unitary (NormMatrixCStarCorona (fun n ↦ Z n)),
                        ∃ hu : ∀ c : C,
                          (u : NormMatrixCStarCorona (fun n ↦ Z n)) *
                              l (iA c) =
                            l (iA c) *
                              (u : NormMatrixCStarCorona (fun n ↦ Z n)),
                          ‖y‖ - δ ≤ ‖universalCStarAmalgamEval iA iB
                            (conjugateRepresentation iA iB l r hlr u hu) y‖

open Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit in
/-- The word form of the input follows from its conjugate form: the carrier of
a conjugated corona pair is a norm corona, so it is MF. -/
theorem wordNorming_of_conjugateWordNorming
    (hconj : ConjugateWordNormingStatement) : WordNormingStatement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp y hy δ hδ
  obtain ⟨Z, hZ, l, r, hlr, u, hu, hnorm⟩ :=
    hconj iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp y hy δ hδ
  letI : ∀ n, Nonempty (Z n) := hZ
  exact ⟨conjugateRepresentation iA iB l r hlr u hu,
    normMatrixCorona_hasMFEmbedding_of_positive Z hZ, hnorm⟩

/-- **Shulman's Theorem 16 from the conjugate form of the input.** -/
theorem shulmanTheorem16_of_conjugateWordNorming
    (hconj : ConjugateWordNormingStatement) :
    Manuscript.MFRecognition.HNNPermanence.ShulmanTheorem16Statement :=
  shulmanTheorem16_of_wordNorming
    (wordNorming_of_conjugateWordNorming hconj)

end

end ShulmanFill
end GroupApproximation
