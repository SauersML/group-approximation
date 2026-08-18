import GroupApproximation.Sofic.LiteralUniformObstruction
import GroupApproximation.Sofic.RelatorDefectBudget

/-!
# The uniform obstruction on the printed relators

`Sofic/LiteralUniformObstruction.lean` proves the compactness form of uniform
invisibility for the literal marked word: there are a defect budget `δ > 0`
and a finite set `F₀ ⊆ E` such that every unitary family that is
`δ`-multiplicative on `F₀` sends the mark into the open unit ball about the
identity, in every matrix dimension.

That statement is not checkable.  `F₀` is an unnamed finite subset of an
infinite finitely presented group, and the hypothesis is about a map defined
on all of `E`.  Nobody handed a tuple of matrices can decide whether it
satisfies the hypothesis.

This file replaces `F₀` by the **forty-one printed relators**.  The hypothesis
becomes: eight unitary matrices, of any size, whose forty-one relator words
all evaluate within `δ` of the identity in operator norm.  That is a finite
condition on a finite tuple, written in the alphabet the manuscript prints,
and the conclusion is the same: the marked word is within distance `1` of the
identity, uniformly in the dimension.

## How the test set is replaced

`RelatorDefectBudget` supplies the bridge.  Given an assignment `u` of
unitaries to the eight letters, choose once and for all a word `rep g` in the
free group representing each `g ∈ E`, and read `u` on all of `E` through
the map `g ↦ u(rep g)`.  Its multiplicative defect at `(g, h)` is the
value at `u` of the word `(rep g · rep h)⁻¹ · rep (gh)`, which lies in the
normal closure of the relators because it dies in `E`; so it is a product of
`pairBudget g h` conjugates of relators, and operator-norm displacement is
subadditive under products and invariant under inversion and unitary
conjugation.  Hence its defect is at most `pairBudget g h · δ`.  Taking the
maximum of `pairBudget` over the finite set `F₀ ×ˢ F₀` turns a relator budget
into a multiplicativity budget on `F₀`, and the compactness statement applies.
One more budget, `markBudget`, converts the conclusion about `u(rep w)`
back into a conclusion about the printed word `markedWord` itself.

## What is still not effective, and exactly why

The threshold `δ` produced here is still not a number.  Two inputs are
non-effective, and neither is repaired by anything in this file.

* `uniform_invisibility` is proved by a compactness diagonal: a hypothetical
  sequence of counterexamples is assembled into a homomorphism to an
  operator-norm matrix ultraproduct and contradicted there.  A proof by
  contradiction through an ultrafilter returns no rate.
* The robust spectral gap that the transport step consumes -- "once the
  multiplicative defects are small enough, no eigenvalue of the Hermitian
  average lies in the forbidden window" -- is proved through a hyperreal
  standard part in `Sofic/WeakMFVectorGNS.lean`.  Everything downstream of it
  is already explicit; `Sofic/FiniteStageRobustGap.lean` carries that
  bookkeeping with named constants and records this same single gap in its own
  "What is not proved here".

Making `δ` a number therefore does not need a new argument at this level.  It
needs the exact sum-of-squares certificate of
`Sofic/LiteralP13HodgeCertificate.lean` -- which proves the spectral gap
`1/500` for exact orthogonal representations of the base -- to be lifted from
the group ring of the base to the free group, so that it can be evaluated at
an assignment with controlled relator defects rather than at a representation.
That lift is a Fox-derivative computation producing explicit coefficients for
the thirteen base relators; the repository does not contain those
coefficients, and this file does not manufacture them.  What this file does
change is that the *test set* is now the printed relator list rather than an
unspecified finite subset of `E`, so the remaining gap is one rational number
and not also an unnamed set.
-/

namespace GroupApproximation
namespace LiteralRelatorObstruction

open Matrix
open scoped Matrix.Norms.L2Operator
open LiteralNonMFPresentation
open RelatorDefectBudget

noncomputable section

/-! ## The printed relator set, and word representatives -/

/-- The forty-one printed relators, as a subset of the free group on the eight
letters. -/
abbrev literalRelatorSet : Set (FreeGroup Generator) :=
  ((relators : Finset (FreeGroup Generator)) : Set (FreeGroup Generator))

/-- A chosen free-group word representing each element of `E`. -/
noncomputable def rep (g : MarkedGroup) : FreeGroup Generator :=
  (PresentedGroup.mk_surjective literalRelatorSet g).choose

@[simp] theorem rep_spec (g : MarkedGroup) : wordInMarkedGroup (rep g) = g :=
  (PresentedGroup.mk_surjective literalRelatorSet g).choose_spec

/-- Two words with the same image in `E` differ by an element of the normal
closure of the printed relators. -/
theorem inv_mul_mem_normalClosure {w w' : FreeGroup Generator}
    (h : wordInMarkedGroup w = wordInMarkedGroup w') :
    w'⁻¹ * w ∈ Subgroup.normalClosure literalRelatorSet := by
  rw [← PresentedGroup.mk_eq_one_iff, map_mul, map_inv, h]
  exact inv_mul_cancel _

/-! ## The two derivation budgets -/

theorem pair_mem_normalClosure (g h : MarkedGroup) :
    (rep g * rep h)⁻¹ * rep (g * h) ∈
      Subgroup.normalClosure literalRelatorSet := by
  refine inv_mul_mem_normalClosure ?_
  rw [rep_spec, map_mul, rep_spec, rep_spec]

/-- The number of conjugates of printed relators needed to reconcile
`rep g · rep h` with `rep (gh)`.  It depends on the presentation alone: no
matrix, no dimension and no unitary occurs in its definition. -/
noncomputable def pairBudget (g h : MarkedGroup) : ℕ :=
  (exists_isRelatorProduct (pair_mem_normalClosure g h)).choose

theorem pairBudget_spec (g h : MarkedGroup) :
    IsRelatorProduct literalRelatorSet (pairBudget g h)
      ((rep g * rep h)⁻¹ * rep (g * h)) :=
  (exists_isRelatorProduct (pair_mem_normalClosure g h)).choose_spec

theorem mark_mem_normalClosure :
    (rep mark)⁻¹ * markedWord ∈ Subgroup.normalClosure literalRelatorSet := by
  refine inv_mul_mem_normalClosure ?_
  show wordInMarkedGroup markedWord = wordInMarkedGroup (rep mark)
  rw [rep_spec]

/-- The number of conjugates of printed relators needed to reconcile the
chosen representative of the mark with the printed marked word. -/
noncomputable def markBudget : ℕ :=
  (exists_isRelatorProduct mark_mem_normalClosure).choose

theorem markBudget_spec :
    IsRelatorProduct literalRelatorSet markBudget ((rep mark)⁻¹ * markedWord) :=
  (exists_isRelatorProduct mark_mem_normalClosure).choose_spec

/-! ## The induced almost representation

The map on all of `E` induced by an assignment `u` of unitaries to the eight
letters is `g ↦ u(rep g)`.  It is written inline below rather than given a
name: naming it puts a second spelling of the same term into the goal, and the
defeq checks that reconcile the two spellings against the `FreeGroup.lift`
form produced by `RelatorDefectBudget` are what exhausted the elaborator's
budget when this file first compiled. -/

/-! ## The obstruction on the printed relators

The three lemmas below are separated out so that the budgets `pairBudget` and
`markBudget` -- each a `Classical.choose` over a normal-closure membership
proof for a forty-one element relator set -- never reach an arithmetic tactic
as an *evaluable* term.  They enter the main proof only as opaque natural
numbers obtained by `obtain`, which is what keeps the elaboration inside its
default heartbeat budget: given the literal spelling, `positivity` and
`nlinarith` try to normalise `(markBudget : ℝ)` and unfold the choice. -/

/-- One derivation budget serves a whole finite set of pairs. -/
theorem exists_pair_budget_bound (F : Finset MarkedGroup) :
    ∃ N : ℕ, ∀ g ∈ F, ∀ h ∈ F, ∃ k : ℕ, k ≤ N ∧
      IsRelatorProduct literalRelatorSet k
        ((rep g * rep h)⁻¹ * rep (g * h)) := by
  classical
  refine ⟨(F ×ˢ F).sup (fun p ↦ pairBudget p.1 p.2), ?_⟩
  intro g hg h hh
  refine ⟨pairBudget g h, ?_, pairBudget_spec g h⟩
  have hmem := Finset.le_sup
    (f := fun p : MarkedGroup × MarkedGroup ↦ pairBudget p.1 p.2)
    (Finset.mk_mem_product hg hh)
  simpa using hmem

/-- The multiplicative defect of the induced map at one pair, from a relator
budget for that pair. -/
theorem norm_defect_le {Y : FiniteModel}
    (u : Generator → Matrix.unitaryGroup Y ℂ) {delta : ℝ}
    (hu : ∀ r ∈ literalRelatorSet, opLength Y (FreeGroup.lift u r) ≤ delta)
    {k : ℕ} {g h : MarkedGroup}
    (hk : IsRelatorProduct literalRelatorSet k
      ((rep g * rep h)⁻¹ * rep (g * h))) :
    ‖((FreeGroup.lift u (rep (g * h)) : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ) -
        ((FreeGroup.lift u (rep g) : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
          ((FreeGroup.lift u (rep h) : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ)‖
      ≤ (k : ℝ) * delta := by
  have hb := opLength_le_of_isRelatorProduct (FreeGroup.lift u) hu hk
  rw [map_mul, map_inv, map_mul, opLength_inv_mul] at hb
  have hcoe : ((FreeGroup.lift u (rep g) * FreeGroup.lift u (rep h) :
        Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)
      = ((FreeGroup.lift u (rep g) : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
        ((FreeGroup.lift u (rep h) : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ) := rfl
  rw [hcoe] at hb
  exact hb

/-- Two words with a relator budget between them are that far apart in
operator-norm displacement.

The two words are variables rather than `rep mark` and `markedWord`.  Spelling
them out makes `markedWord` -- a closed twelve-letter word in the free group --
available to `whnf`, and evaluating `FreeGroup.lift u markedWord` through the
quotient by word reduction is what exhausted the heartbeat budget here; with
variables there is nothing to evaluate.  The instance the caller needs is
recovered by unifying `?v⁻¹ * ?w` against the budget's own statement. -/
theorem norm_le_of_budget {Y : FiniteModel}
    (u : Generator → Matrix.unitaryGroup Y ℂ) {delta : ℝ}
    (hu : ∀ r ∈ literalRelatorSet, opLength Y (FreeGroup.lift u r) ≤ delta)
    {M : ℕ} {v w : FreeGroup Generator}
    (hM : IsRelatorProduct literalRelatorSet M (v⁻¹ * w)) :
    opLength Y (FreeGroup.lift u w)
      ≤ opLength Y (FreeGroup.lift u v) + (M : ℝ) * delta := by
  have hb1 := opLength_le_of_isRelatorProduct (FreeGroup.lift u) hu hM
  have hsplit : FreeGroup.lift u w
      = FreeGroup.lift u v * FreeGroup.lift u (v⁻¹ * w) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [hsplit]
  exact (opLength_mul_le Y _ _).trans (add_le_add_left hb1 _)

/-- **The uniform obstruction with the printed relators as its test set.**

There is one positive defect budget `δ`, independent of the matrix dimension,
such that: whenever eight unitary matrices of any size satisfy each of the
forty-one printed relators of `E` to within `δ` in operator norm, the printed
marked word evaluates strictly inside the unit ball about the identity.

This is `LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction`
with the unnamed finite test set `F₀ ⊆ E` replaced by the printed relator
list.  The budget `δ` is still obtained from compactness and is not a number;
see the module docstring for the two inputs that would have to be made
effective. -/
theorem literal_relator_uniform_obstruction :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (Y : FiniteModel) (u : Generator → Matrix.unitaryGroup Y ℂ),
        (∀ r ∈ relators,
          ‖((FreeGroup.lift u r : Matrix.unitaryGroup Y ℂ) :
              Matrix Y Y ℂ) - 1‖ ≤ delta) →
        ‖((FreeGroup.lift u markedWord : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ) - 1‖ < 1 := by
  classical
  obtain ⟨eps, F₀, heps, hobs⟩ :=
    uniform_invisibility LiteralNonMFEndpoint.literal_mark_normMFInvisible
      (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := exists_pair_budget_bound F₀
  obtain ⟨M, hM⟩ : ∃ M : ℕ,
      IsRelatorProduct literalRelatorSet M ((rep mark)⁻¹ * markedWord) :=
    ⟨markBudget, markBudget_spec⟩
  refine ⟨min (eps / ((N : ℝ) + 1)) (1 / (2 * ((M : ℝ) + 1))), ?_, ?_⟩
  · exact lt_min (div_pos heps (by positivity)) (by positivity)
  intro Y u hu
  set delta : ℝ :=
    min (eps / ((N : ℝ) + 1)) (1 / (2 * ((M : ℝ) + 1))) with hdelta
  have hdpos : 0 < delta :=
    lt_min (div_pos heps (by positivity)) (by positivity)
  have hdnn : (0 : ℝ) ≤ delta := hdpos.le
  have hNbound : (N : ℝ) * delta ≤ eps := by
    have h1 : delta ≤ eps / ((N : ℝ) + 1) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [hdnn, h1]
  have hMbound : (M : ℝ) * delta ≤ 1 / 2 := by
    have h1 : delta ≤ 1 / (2 * ((M : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [hdnn, h1]
  have hrel : ∀ r ∈ literalRelatorSet,
      opLength Y (FreeGroup.lift u r) ≤ delta := by
    intro r hr
    exact hu r (Finset.mem_coe.mp hr)
  -- the induced map is `eps`-multiplicative on `F₀`
  have hmul : ∀ g ∈ F₀, ∀ h ∈ F₀,
      ‖((FreeGroup.lift u (rep (g * h)) : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ) -
          ((FreeGroup.lift u (rep g) : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ) *
            ((FreeGroup.lift u (rep h) : Matrix.unitaryGroup Y ℂ) :
              Matrix Y Y ℂ)‖
        ≤ eps := by
    intro g hg h hh
    obtain ⟨k, hkle, hkspec⟩ := hN g hg h hh
    refine (norm_defect_le u hrel hkspec).trans ?_
    have hstep : (k : ℝ) * delta ≤ (N : ℝ) * delta :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkle) hdnn
    exact hstep.trans hNbound
  -- compactness sends the mark into the ball of radius `1/2`
  have hmarkobs :
      ‖((FreeGroup.lift u (rep mark) : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ) - 1‖ < 1 / 2 :=
    hobs Y (fun g ↦ FreeGroup.lift u (rep g)) hmul
  have hfinal := norm_le_of_budget u hrel hM
  have hhalf : opLength Y (FreeGroup.lift u (rep mark)) < 1 / 2 := hmarkobs
  show ‖((FreeGroup.lift u markedWord : Matrix.unitaryGroup Y ℂ) :
      Matrix Y Y ℂ) - 1‖ < 1
  have hlt : opLength Y (FreeGroup.lift u markedWord) < 1 := by
    linarith [hfinal, hhalf, hMbound]
  exact hlt

/-! ## The sign form of the obstruction -/

/-- **No almost-satisfying unitary tuple can realize the central sign.**

The Clifford witness makes the marked word a nontrivial central involution of
`E`, and the printed sharpness discussion exhibits finite models of the
*cyclic comparison* group in which the corresponding word is the scalar `-1`.
For the literal group that is impossible even approximately: no eight unitary
matrices, of any size, that satisfy the forty-one printed relators to within
`δ` can send the printed marked word to `-1`.

Together with `Monsters/CyclicBaseLEFObstruction` -- which closes the *exact*
finite models -- this says that the sign obstruction is visible already at
finite stage, on a hypothesis that a reader can check on a tuple of
matrices. -/
theorem literal_relator_no_negative_mark :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (Y : FiniteModel), Nonempty Y →
        ∀ u : Generator → Matrix.unitaryGroup Y ℂ,
          (∀ r ∈ relators,
            ‖((FreeGroup.lift u r : Matrix.unitaryGroup Y ℂ) :
                Matrix Y Y ℂ) - 1‖ ≤ delta) →
          ((FreeGroup.lift u markedWord : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ) ≠ -1 := by
  obtain ⟨delta, hdelta, hobs⟩ := literal_relator_uniform_obstruction
  refine ⟨delta, hdelta, ?_⟩
  intro Y hY u hu hneg
  obtain ⟨i⟩ := hY
  have hlt := hobs Y u hu
  rw [hneg] at hlt
  have hentry : Complex.normSq (((-1 : Matrix Y Y ℂ) - 1) i i) = 4 := by
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply_eq,
      show (-(1 : ℂ) - 1 = -2) from by ring, Complex.normSq_apply]
    norm_num
  have hle := normSq_entry_le_sq_l2_opNorm Y ((-1 : Matrix Y Y ℂ) - 1) i i
  rw [hentry] at hle
  have hnn : (0 : ℝ) ≤ ‖(-1 : Matrix Y Y ℂ) - 1‖ := norm_nonneg _
  nlinarith [hlt, hle, hnn]

end

end LiteralRelatorObstruction
end GroupApproximation
