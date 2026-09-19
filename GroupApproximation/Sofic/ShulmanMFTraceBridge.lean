import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Sofic.MFTraceCoronaBridge
import GroupApproximation.Sofic.MFTraceRecognition
import GroupApproximation.Sofic.OperatorMFLocalNormalization

/-!
# From Shulman's MF trace to the finite-test-set MF regular character

`Sofic.MFTraceRecognition` proves the analytic half of the recognition
theorem: a group whose regular character satisfies the *finite-test-set*
condition `IsMFRegularCharacter` is operator MF.  That predicate quantifies
over finite subsets of the group; Shulman's MF-trace condition
(`Analysis.ShulmanTraceClasses`) is asymptotic and quantifies over every
element of the algebra.  This file supplies the missing entry step, which is
short by design: restrict the maps `φₙ` to the canonical group unitaries,
and read off one sufficiently late index.

The bookkeeping is the whole content.  For a finite test set `F` and accuracy
`ε`, the five limit clauses of `MFTraceModel` contribute finitely many
eventual conditions — one for each pair in `F ×ˢ F`, one for each `g ∈ F`,
one at the identity — and `Filter.Eventually.exists` picks a single index `n`
meeting all of them.  Three points deserve naming.

* The pointwise bound `supₙ ‖φₙ(a)‖ < ∞` is what supplies the function
  `B : G → ℝ` that `IsMFRegularCharacter` demands *before* the test set is
  known: `B g` is the bound at `a = u g`, chosen once and used at every `F`
  and every `ε`.
* The matrix sizes are not assumed positive.  They do not have to be: the
  trace clause at `a = 1` forces it, because an empty model has normalized
  trace `0` while `τ 1 = 1`.  Running the accuracy below `1/2` is enough.
* Multiplicativity and `⋆`-compatibility of the model are used on the algebra
  side, where `u (g * y) = u g * u y` and `u g⁻¹ = star (u g)` turn the
  clauses at `(u g, u y)` and at `star (u g)` into the group-indexed clauses
  that `RegularCharacterModel` states.

The consequence is then immediate: composing with the recognition theorem and
with `isOperatorMF_iff_isNormApproximable_one` gives *if the canonical trace
is an MF trace then the group is operator MF*, which is the direction the
non-MF program consumes in contrapositive form.

The canonical trace of the reduced group C⋆-algebra is discharged here
concretely, so the headline is available with no undischarged premise for
that algebra.
-/

namespace GroupApproximation
namespace ShulmanTrace

open Filter Matrix MFTraceRecognition ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-! ## The bridge -/

/-- **Entry step.**  If a trace `τ` on a complex `⋆`-algebra `A` is an MF
trace in Shulman's sense, and `u : G → A` is a group-unitary family whose
`τ`-values are the canonical ones (`1` at the identity, `0` elsewhere), then
the regular character of `G` satisfies the finite-test-set condition
`IsMFRegularCharacter`.

No unitarity of `u` is used beyond the two algebraic identities: `u` is
multiplicative and sends inversion to the adjoint. -/
theorem isMFRegularCharacter_of_isMFTrace {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] {τ : A → ℂ} (u : G → A)
    (hmul : ∀ g y : G, u (g * y) = u g * u y)
    (hstar : ∀ g : G, u g⁻¹ = star (u g))
    (hτone : τ (u 1) = 1)
    (hτne : ∀ g : G, g ≠ 1 → τ (u g) = 0)
    (h : IsMFTrace τ) : IsMFRegularCharacter G := by
  classical
  obtain ⟨M⟩ := h
  choose B hB using fun g : G ↦ M.bounded (u g)
  refine ⟨B, ?_⟩
  intro F ε hε
  obtain ⟨δ, hδ0, hδε, hδhalf⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _⟩
  -- The finitely many eventual conditions contributed by the test set.
  have hEmul : ∀ᶠ n in atTop, ∀ q ∈ F ×ˢ F,
      ‖M.map n (u (q.1 * q.2)) - M.map n (u q.1) * M.map n (u q.2)‖ ≤ δ := by
    rw [eventually_all_finset]
    intro q _
    have ht := M.tendsto_mul (u q.1) (u q.2)
    rw [← hmul q.1 q.2] at ht
    exact eventually_le_of_tendsto_zero ht hδ0
  have hEstar : ∀ᶠ n in atTop, ∀ g ∈ F,
      ‖M.map n (u g⁻¹) - (M.map n (u g))ᴴ‖ ≤ δ := by
    rw [eventually_all_finset]
    intro g _
    have ht := M.tendsto_star (u g)
    rw [← hstar g] at ht
    exact eventually_le_of_tendsto_zero ht hδ0
  have hEtr : ∀ᶠ n in atTop, ∀ g ∈ F,
      ‖τ (u g) - normTrace (M.space n) (M.map n (u g))‖ ≤ δ := by
    rw [eventually_all_finset]
    intro g _
    exact eventually_le_of_tendsto_zero (M.tendsto_trace (u g)) hδ0
  have hEone : ∀ᶠ n in atTop,
      ‖τ (u 1) - normTrace (M.space n) (M.map n (u 1))‖ ≤ δ :=
    eventually_le_of_tendsto_zero (M.tendsto_trace (u 1)) hδ0
  obtain ⟨n, hmuln, hstarn, htrn, honen⟩ :=
    (hEmul.and (hEstar.and (hEtr.and hEone))).exists
  have hone1 : ‖(1 : ℂ) - normTrace (M.space n) (M.map n (u 1))‖ ≤ δ := by
    rwa [hτone] at honen
  -- The trace clause at the identity forces a nonempty model.
  have hcard : 0 < Fintype.card (M.space n) := by
    by_contra hc
    have hc0 : Fintype.card (M.space n) = 0 := Nat.le_zero.mp (Nat.not_lt.mp hc)
    have hz : normTrace (M.space n) (M.map n (u 1)) = 0 := by
      rw [normTrace, hc0]
      simp
    rw [hz, sub_zero, norm_one] at hone1
    linarith [hδhalf]
  refine ⟨{
    carrier := M.space n
    nonempty := hcard
    map := fun g ↦ M.map n (u g)
    bounded := fun g _ ↦ hB g n
    multiplicative := ?_
    star_compatible := ?_
    trace_correct_one := ?_
    trace_correct_ne := ?_ }⟩
  · intro g hg y hy
    exact (hmuln (g, y) (Finset.mem_product.mpr ⟨hg, hy⟩)).trans hδε
  · intro g hg
    exact (hstarn g hg).trans hδε
  · intro _
    have h1 : ‖normTrace (M.space n) (M.map n (u 1)) - 1‖ ≤ δ := by
      rw [norm_sub_rev]
      exact hone1
    exact h1.trans hδε
  · intro g hg hgne
    have h1 := htrn g hg
    rw [hτne g hgne, zero_sub, norm_neg] at h1
    exact h1.trans hδε

/-- The same entry step, packaged for a homomorphism into the unitary group.
The adjoint identity `u g⁻¹ = star (u g)` is recovered from unitarity. -/
theorem isMFRegularCharacter_of_isMFTrace_unitaryHom {A : Type*} [Ring A]
    [StarRing A] [Algebra ℂ A] {τ : A → ℂ} (u : G →* unitary A)
    (hτone : τ ((u 1 : unitary A) : A) = 1)
    (hτne : ∀ g : G, g ≠ 1 → τ ((u g : unitary A) : A) = 0)
    (h : IsMFTrace τ) : IsMFRegularCharacter G := by
  have hmulA : ∀ g y : G,
      ((u (g * y) : unitary A) : A) = ((u g : unitary A) : A) * ((u y : unitary A) : A) :=
    fun g y ↦ congrArg (fun U : unitary A ↦ (U : A)) (map_mul u g y)
  have honeA : ((u (1 : G) : unitary A) : A) = 1 :=
    congrArg (fun U : unitary A ↦ (U : A)) (map_one u)
  have hstarA : ∀ g : G,
      ((u g⁻¹ : unitary A) : A) = star ((u g : unitary A) : A) := by
    intro g
    have hba : ((u g⁻¹ : unitary A) : A) * ((u g : unitary A) : A) = 1 := by
      rw [← hmulA, inv_mul_cancel, honeA]
    have hsa : ((u g : unitary A) : A) * star ((u g : unitary A) : A) = 1 :=
      Unitary.mul_star_self_of_mem (u g).2
    calc ((u g⁻¹ : unitary A) : A)
        = ((u g⁻¹ : unitary A) : A) *
            (((u g : unitary A) : A) * star ((u g : unitary A) : A)) := by
          rw [hsa, mul_one]
      _ = (((u g⁻¹ : unitary A) : A) * ((u g : unitary A) : A)) *
            star ((u g : unitary A) : A) := by rw [mul_assoc]
      _ = star ((u g : unitary A) : A) := by rw [hba, one_mul]
  exact isMFRegularCharacter_of_isMFTrace (fun g ↦ ((u g : unitary A) : A))
    hmulA hstarA hτone hτne h

/-! ## The reusable headline -/

/-- **An MF trace with the canonical generator values makes the group
operator-norm approximable at separation `1`.** -/
theorem isNormApproximable_of_isMFTrace {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] {τ : A → ℂ} (u : G → A)
    (hmul : ∀ g y : G, u (g * y) = u g * u y)
    (hstar : ∀ g : G, u g⁻¹ = star (u g))
    (hτone : τ (u 1) = 1)
    (hτne : ∀ g : G, g ≠ 1 → τ (u g) = 0)
    (h : IsMFTrace τ) : IsNormApproximable G 1 :=
  isNormApproximable_of_isMFRegularCharacter G
    (isMFRegularCharacter_of_isMFTrace u hmul hstar hτone hτne h)

/-- **The composed headline.**  If the canonical trace of a unital complex
`⋆`-algebra containing `G` as its group unitaries is an MF trace, then `G` is
operator MF. -/
theorem isOperatorMF_of_isMFTrace [Countable G] {A : Type*} [Ring A]
    [StarRing A] [Algebra ℂ A] {τ : A → ℂ} (u : G → A)
    (hmul : ∀ g y : G, u (g * y) = u g * u y)
    (hstar : ∀ g : G, u g⁻¹ = star (u g))
    (hτone : τ (u 1) = 1)
    (hτne : ∀ g : G, g ≠ 1 → τ (u g) = 0)
    (h : IsMFTrace τ) : IsOperatorMF G :=
  OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (isNormApproximable_of_isMFTrace u hmul hstar hτone hτne h)

/-! ## The canonical trace of the reduced group C⋆-algebra

The canonical coefficient functional of `Analysis.ReducedGroupCStarTrace` is
the canonical trace, and its values on the left regular unitaries are the
canonical ones.  That discharges the two generator hypotheses above for a
concrete algebra. -/

variable (G) in
/-- The canonical trace is `1` at the identity unitary. -/
theorem canonicalCoefficientAtOne_reducedLeftRegular_one :
    canonicalCoefficientAtOne G (reducedLeftRegular G 1) = 1 := by
  rw [reducedLeftRegular_one]
  change ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = 1
  simp [deltaOne]

variable (G) in
/-- The canonical trace vanishes on every nonidentity left regular unitary. -/
theorem canonicalCoefficientAtOne_reducedLeftRegular_ne (g : G) (hg : g ≠ 1) :
    canonicalCoefficientAtOne G (reducedLeftRegular G g) = 0 := by
  have hginv : ¬ (g⁻¹ = 1) := fun hc ↦ hg (inv_eq_one.mp hc)
  change ((reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G)
    (deltaOne G)) 1 = 0
  simp [deltaOne, hginv]

/-- **The headline with nothing left to discharge, for the reduced algebra.**
If the canonical trace of `C⋆_r(G)` is an MF trace in Shulman's sense, then
`G` is operator MF. -/
theorem isOperatorMF_of_isMFTrace_canonicalReduced [Countable G]
    (h : IsMFTrace (fun T : ReducedGroupCStar G ↦ canonicalCoefficientAtOne G T)) :
    IsOperatorMF G :=
  isOperatorMF_of_isMFTrace (reducedLeftRegular G) (reducedLeftRegular_mul G)
    (fun g ↦ (star_reducedLeftRegular G g).symm)
    (canonicalCoefficientAtOne_reducedLeftRegular_one G)
    (fun g hg ↦ canonicalCoefficientAtOne_reducedLeftRegular_ne G g hg) h

/-! ## The canonical trace of the full group C⋆-algebra

This is the statement the non-MF program consumes, in contrapositive form:
the group is the witness, the trace is the canonical trace of `C⋆(G)`, and
`Analysis.MaximalGroupCStarTrace` has already proved the generator formula
`τ(u_g) = 1` at the identity and `0` elsewhere.  Nothing is left over. -/

/-- **The headline, with nothing left to discharge.**  If the canonical trace
of the full group C⋆-algebra `C⋆(G)` is an MF trace in Shulman's sense, then
`G` is operator MF.

Contrapositive: a group that is not operator MF has a canonical trace that is
not an MF trace — which, against a soficity hypothesis supplying
hyperlinearity of the same trace, separates the two trace classes.

**The proof is the corona argument of `Sofic/MFTraceCoronaBridge.lean`**, not
the local recognition route that the rest of this file develops.  Dividing the
bounded matrix sequences by the operator-norm-null ones turns the asymptotic
homomorphism of an `MFTraceModel` into an exact one, so the approximation is
discharged once by the quotient instead of being tracked through a schedule of
accuracies.  In particular this theorem does **not** depend on
`IsMFRegularCharacter`, on `IsNormApproximable`, or on the corner-and-polar
argument of `Sofic/MFTraceRecognition.lean` — which stays in the tree, proves
a different quantitative statement, and is still what the other theorems above
use. -/
theorem isOperatorMF_of_isMFTrace_canonicalMaximal
    (h : IsMFTrace (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) :
    IsOperatorMF G := by
  obtain ⟨M⟩ := h
  obtain ⟨M', hcard⟩ := M.exists_shift (canonicalMaximalTrace_one G)
  obtain ⟨rho, hrho⟩ := exists_injective_coronaUnitaryHom G M' hcard
  exact ⟨M'.space, hcard, rho, hrho⟩

end ShulmanTrace
end GroupApproximation
