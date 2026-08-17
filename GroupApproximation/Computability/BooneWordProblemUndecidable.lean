import GroupApproximation.Computability.BooneWordAgreement
import GroupApproximation.Computability.UniformWordProblemUndecidable
import GroupApproximation.Computability.AdianRabinVariantTransform

/-!
# `D4'`, closed: the uniform word problem, and with it MF recognition

`UniformWordProblemUndecidable` wrote the join ahead of its fourth input, so
that supplying the word map would close `D4'` by instantiation rather than by
another argument.  This file supplies it, and instantiates.

Three of the four pieces arrive verbatim: the undecidable source in
configuration form, the code `finalGroupCode mm hM` presenting `G_M`, and
`computable_rawComm`.  The fourth, `wordProblem_rawComm_iff`, stops one step
short of what the join wants.  It reads the code's word problem on the halting
word as triviality of the *halting element*, `commElt P q = 1`, and says nothing
about the machine; Simpson's Theorem 8 says the rest, but it is a statement
about `FinalGroup mm hM` rather than about the presented stage.

The two groups are the same group and are not the same term.  `commElt` lives in
`finalStage (machineTower mm hM) (machineTowerPres mm hM).tsub`, whose associated
subgroup is the *presentation's* `tsub`, while `FinalGroup` uses `towerTSub`.
The subgroup occurs in the **type** of the HNN extension, so the agreement
`machineTowerPres_tsub` cannot be rewritten and has to be substituted --- which
is why the bridge is stated with the subgroup as a variable.  With `T` a local,
the equality is `subst`-able, and after the substitution the two types agree up
to unfolding `machineTower`, so Theorem 8 applies on the nose.  Going instead
through `finalGroupCodeEquiv` would ask for the image of `k` and of `t(α,β)`
under a four-fold composite; only their triviality is at stake, and this route
never forms the composite.

What closes here is `D4'` itself, `¬ComputablePred wordProblemPred`: the uniform
word problem on presentation codes is undecidable, unconditionally --- no
hypothesis, and no literature input, the undecidable source at the bottom being
Mathlib's `ComputablePred.halting_problem`.  The join threads a **single**
machine through both halves, which is the point of its shape: the words are
attached to the configurations of one machine, and two existentials could
otherwise pick two.

With `D4'` discharged, the second theorem is one application.  The Adian--Rabin
reduction had already reduced operator-MF recognition to exactly this predicate
and to nothing else, so MF recognition is undecidable with no hypothesis left
standing.
-/

namespace GroupApproximation
namespace Computability

open BooneGroup BooneTowerPresentation BooneWords AdianRabinWordProblem

/-- **Simpson's Theorem 8, at a variable associated subgroup.**  The subgroup
sits in the type of the HNN extension, so the presented stage's `tsub` can be
identified with the tower's `⟨t⟩'` only by substitution, and quantifying over
`T` is what lets `machineTowerPres_tsub` reach it.

Everything in the statement is spelled at the tower itself --- `tower
(machineIdentifications mm hM)`, raw `HNNExtension`, no `machineTower` and no
`finalStage` --- because `subst` re-typechecks the motive at *reducible*
transparency: a `Subgroup (machineTower mm hM).Carrier` binder makes the
substituted motive carry `(machineTower mm hM).group` against
`(tower …).group`, defeq but not syntactically equal, and the `subst` fails
(observed; and the same disease at one level down is why the operands are
`HNNExtension.of ((tower …).ι …)` rather than `(finalStage …).ι …`, whose
`.Carrier` projection instance search will not unfold).  The consumer below
supplies the presented stage's data through plain unification, which runs at
default transparency and unfolds all of it.  After the `subst` the ambient
type is literally `FinalGroup mm hM`'s unfolding, and the statement is
`conj_k_finalTw_eq_iff` with the commutator collected. -/
theorem commElt_eq_one_iff_halts_of_tsub_eq (mm : ModularMachine)
    (hM : (mm.size : ℤ) ≠ 0)
    {T : Subgroup (tower (machineIdentifications mm hM)).Carrier}
    (hT : T = towerTSub (machineIdentifications mm hM)) (q : ℕ × ℕ) :
    ((HNNExtension.t)⁻¹ *
          HNNExtension.of
            ((tower (machineIdentifications mm hM)).ι (Base.tw ((q.1 : ℤ), (q.2 : ℤ)))) *
          HNNExtension.t *
          (HNNExtension.of
            ((tower (machineIdentifications mm hM)).ι (Base.tw ((q.1 : ℤ), (q.2 : ℤ)))))⁻¹
        : HNNExtension (tower (machineIdentifications mm hM)).Carrier T T
            (MulEquiv.refl _)) = 1
      ↔ mm.Halts q := by
  subst hT
  rw [mul_inv_eq_one]
  exact conj_k_finalTw_eq_iff mm hM q

/-- **The halting element is trivial exactly when the configuration halts.**
The bridge between the presentation side, which knows `commElt`, and the group
side, which knows `G_M`. -/
theorem commElt_eq_one_iff_halts (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0)
    (q : ℕ × ℕ) :
    commElt (machineTowerPres mm hM) q = 1 ↔ mm.Halts q :=
  commElt_eq_one_iff_halts_of_tsub_eq mm hM (machineTowerPres_tsub mm hM) q

/-- **The join's hypothesis, discharged.**  A computable map sending each
configuration of the machine to a word that dies in the coded group exactly when
that configuration halts.  The map is `rawComm`, its computability is
`computable_rawComm`, and the agreement is the code-level reading of the halting
word composed with the bridge above. -/
theorem exists_boone_words (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0) :
    ∃ w : ℕ × ℕ → List (ℕ × Bool), Computable w ∧
      ∀ p : ℕ × ℕ, WordProblem (finalGroupCode mm hM) (w p) ↔ mm.Halts p :=
  ⟨rawComm (machineTowerPres mm hM), computable_rawComm (machineTowerPres mm hM),
    fun q => (wordProblem_rawComm_iff (machineTowerPres mm hM) q).trans
      (commElt_eq_one_iff_halts mm hM q)⟩

/-- **`D4'`.**  The uniform word problem on presentation codes is undecidable.

Unconditional: no hypothesis and no literature input.  Every step between
Mathlib's `ComputablePred.halting_problem` and this statement is in this
repository. -/
theorem not_computablePred_wordProblemPred :
    ¬ ComputablePred AdianRabinWordProblem.wordProblemPred :=
  not_computablePred_wordProblemPred_of_boone_words exists_boone_words

/-- **Operator-MF recognition is undecidable.**  The Adian--Rabin reduction had
already discharged every group-theoretic input and left exactly one hypothesis,
a statement about computability rather than about groups; `D4'` is that
statement. -/
theorem operatorMF_recognition_not_computable :
    ¬ ComputablePred
      (MarkovMFConsequences.operatorMFProperty PresentationCodes.semantics) :=
  AdianRabinVariantTransform.operatorMF_recognition_undecidable_of_wordProblem
    not_computablePred_wordProblemPred

end Computability
end GroupApproximation
