import GroupApproximation.Computability.RawTransformPrimrec
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Meta.AxiomGuard

/-!
# Radical membership on a retracting free factor, at the level of codes

Manuscript `non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`:

> "Set `U = E*A`.  This group is finitely presented and non-MF, since the free
> factor `E` embeds in it.  Let `π_A : E*A → A` be the canonical retraction.
> Since `A` is MF, Proposition `prop:univquot` gives `Res_MF(A) = {1}`.
> Functoriality then gives `Res_MF(U) ≤ ker π_A`.  For every `a ∈ A` it follows
> that `i_A(a) ∈ Res_MF(U) ⟺ a = 1` in `A`. [...] The inclusion of words in the
> `A` factor is computable, so a radical-membership algorithm for `U` would
> decide the word problem of `A`."

This file proves every one of these sentences for an arbitrary presentation
code `c` (the group `A`) and the repository's fixed finitely presented non-MF
code `PresentationCodes.negativeCode` (the group `E`).  The free product is the
code `CoprodCode.coprodCode c negativeCode`, which lists `A` as the *left*
factor; this is `A*E ≅ E*A`, and nothing below depends on the order.

The radical is the literal natural-dimension corona radical
`manuscriptCoronaMFResidual`, and `radicalWordAt_iff_actual` identifies it with
`actualCoronaMFResidual`.

What this file does **not** supply is the input group: a finitely presented MF
group with undecidable word problem.  The manuscript takes Kharlampovich's
solvable group and gets MF from Tikuisis--White--Winter.  Neither is in the
repository, so the fixed-group theorem is not closed here.  Its generic part,
`radicalMembership_undecidable_of_mfFactor`, is a theorem about the concrete
properties of `c` it assumes, and it is audited as a conditional statement.

* `leftSplit` -- the code presents the free product of the two factors;
* `leftFactorInclusion`, `leftFactorRetraction` -- `i_A` and `π_A`;
* `radical_le_ker_retraction` -- `Res_MF(U) ≤ ker π_A`;
* `leftFactorInclusion_mem_radical_iff` -- `i_A(a) ∈ Res_MF(U) ⟺ a = 1`;
* `wordProblem_manyOneReduces_radical` -- the computable word inclusion is a
  many-one reduction;
* `radicalMembership_undecidable_of_mfFactor` -- the generic theorem;
* `notesFixedRadicalMembershipClauses` -- the closed package of all of these.
-/

namespace GroupApproximation.Full.NN03

open PresentationCodes PresentationCodeList CoprodCode PresentedGroupRelabel
open RabinConstructionSource AdianRabinWordProblem

/-- Coded groups are countable: every element is named by a list of letters. -/
theorem codeCountable (c : PresentationCode) : Countable (Carrier c) := by
  refine Function.Surjective.countable
    (f := fun l : List (Fin (genCount c) × Bool) ↦
      (PresentedGroup.mk (relatorSet c) (FreeGroup.mk l) : Carrier c)) ?_
  intro x
  obtain ⟨g, rfl⟩ := PresentedGroup.mk_surjective (relatorSet c) x
  obtain ⟨l, rfl⟩ := Quot.exists_rep g
  exact ⟨l, rfl⟩

attribute [local instance] codeCountable

/-! ## The radical-membership predicate -/

/-- **Radical membership of a raw word** (`thm:fixed-radical-membership`): the
word `v`, read in the group presented by `c`, lies in the literal corona MF
radical `Res_MF`. -/
def RadicalWordAt (c : PresentationCode) (v : List (ℕ × Bool)) : Prop :=
  (PresentedGroup.mk (relatorSet c) (wordOf c v) : Carrier c) ∈
    manuscriptCoronaMFResidual (Carrier c)

/-- The natural-dimension radical and the actual corona radical agree. -/
theorem radicalWordAt_iff_actual (c : PresentationCode) (v : List (ℕ × Bool)) :
    RadicalWordAt c v ↔
      (PresentedGroup.mk (relatorSet c) (wordOf c v) : Carrier c) ∈
        actualCoronaMFResidual (Carrier c) := by
  rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  rfl

/-! ## The free product and its left factor -/

/-- **The free-product code presents the free product of the two coded
groups** (`thm:fixed-radical-membership`, `U = E*A`). -/
noncomputable def leftSplit (c d : PresentationCode) :
    Carrier (coprodCode c d) ≃*
      Monoid.Coprod (PresentedGroup {x | x ∈ relatorListOf c})
        (PresentedGroup {x | x ∈ relatorListOf d}) :=
  ((carrierEquivList (coprodCode c d)).trans (presCongrSet (relSet_coprodCode c d))).trans
    ((congrEquiv (finSumFinEquiv (m := genCount c) (n := genCount d))
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})).symm.trans
      (coprodEquiv {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d}))

/-- **A normalized left-factor word lands in the left factor.** -/
theorem leftSplit_mk (c d : PresentationCode) (v : List (ℕ × Bool)) :
    leftSplit c d
        (PresentedGroup.mk (relatorSet (coprodCode c d))
          (wordOf (coprodCode c d) (normWord c v))) =
      Monoid.Coprod.inl (N := PresentedGroup {x | x ∈ relatorListOf d})
        (PresentedGroup.mk {x | x ∈ relatorListOf c} (wordOf c v)) := by
  have hlist : carrierEquivList (coprodCode c d)
      (PresentedGroup.mk (relatorSet (coprodCode c d))
        (wordOf (coprodCode c d) (normWord c v))) =
      PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c d)}
        (wordOf (coprodCode c d) (normWord c v)) :=
    presCongrSet_mk (coe_relatorFinset (coprodCode c d)) _
  have hrel : presCongrSet (relSet_coprodCode c d)
      (PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c d)}
        (wordOf (coprodCode c d) (normWord c v))) =
      relabelHom (finSumFinEquiv (m := genCount c) (n := genCount d))
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
        (PresentedGroup.mk
          (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
          (FreeGroup.map Sum.inl (wordOf c v))) := by
    rw [presCongrSet_mk, relabelHom_mk, wordOf_coprodCode c d v]
  have hsymm : relabelHomSymm (finSumFinEquiv (m := genCount c) (n := genCount d))
      (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
      (relabelHom (finSumFinEquiv (m := genCount c) (n := genCount d))
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
        (PresentedGroup.mk
          (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
          (FreeGroup.map Sum.inl (wordOf c v)))) =
      PresentedGroup.mk
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
        (FreeGroup.map Sum.inl (wordOf c v)) :=
    DFunLike.congr_fun
      (relabel_symm_comp (finSumFinEquiv (m := genCount c) (n := genCount d))
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})) _
  change coprodEquiv {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d}
      (relabelHomSymm (finSumFinEquiv (m := genCount c) (n := genCount d))
        (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d})
        (presCongrSet (relSet_coprodCode c d)
          (carrierEquivList (coprodCode c d)
            (PresentedGroup.mk (relatorSet (coprodCode c d))
              (wordOf (coprodCode c d) (normWord c v)))))) = _
  rw [hlist, hrel, hsymm, coprodEquiv_mk_map_inl]

/-- Folding the free product onto its left factor. -/
def leftFold (c d : PresentationCode) :
    Monoid.Coprod (PresentedGroup {x | x ∈ relatorListOf c})
        (PresentedGroup {x | x ∈ relatorListOf d}) →*
      PresentedGroup {x | x ∈ relatorListOf c} :=
  Monoid.Coprod.lift (MonoidHom.id _) 1

/-- **The canonical retraction `π_A : U → A`** (`thm:fixed-radical-membership`). -/
noncomputable def leftFactorRetraction (c d : PresentationCode) :
    Carrier (coprodCode c d) →* Carrier c :=
  (carrierEquivList c).symm.toMonoidHom.comp
    ((leftFold c d).comp (leftSplit c d).toMonoidHom)

/-- **The factor inclusion `i_A : A → U`** (`thm:fixed-radical-membership`). -/
noncomputable def leftFactorInclusion (c d : PresentationCode) :
    Carrier c →* Carrier (coprodCode c d) :=
  (leftSplit c d).symm.toMonoidHom.comp
    ((Monoid.Coprod.inl (N := PresentedGroup {x | x ∈ relatorListOf d})).comp
      (carrierEquivList c).toMonoidHom)

/-- `π_A ∘ i_A = id`. -/
theorem leftFactorRetraction_inclusion (c d : PresentationCode) (a : Carrier c) :
    leftFactorRetraction c d (leftFactorInclusion c d a) = a := by
  change (carrierEquivList c).symm
      (leftFold c d (leftSplit c d ((leftSplit c d).symm
        (Monoid.Coprod.inl (N := PresentedGroup {x | x ∈ relatorListOf d})
          (carrierEquivList c a))))) = a
  rw [MulEquiv.apply_symm_apply, leftFold, Monoid.Coprod.lift_apply_inl,
    MonoidHom.id_apply, MulEquiv.symm_apply_apply]

theorem leftFactorInclusion_injective (c d : PresentationCode) :
    Function.Injective (leftFactorInclusion c d) :=
  Function.LeftInverse.injective (leftFactorRetraction_inclusion c d)

/-- **The inclusion of words in the `A` factor**: `i_A` sends the word `v` of
`c` to the normalized word `normWord c v` of the free-product code. -/
theorem leftFactorInclusion_mk (c d : PresentationCode) (v : List (ℕ × Bool)) :
    leftFactorInclusion c d (PresentedGroup.mk (relatorSet c) (wordOf c v)) =
      PresentedGroup.mk (relatorSet (coprodCode c d))
        (wordOf (coprodCode c d) (normWord c v)) := by
  have hc : carrierEquivList c (PresentedGroup.mk (relatorSet c) (wordOf c v)) =
      PresentedGroup.mk {x | x ∈ relatorListOf c} (wordOf c v) :=
    presCongrSet_mk (coe_relatorFinset c) _
  change (leftSplit c d).symm
      (Monoid.Coprod.inl (N := PresentedGroup {x | x ∈ relatorListOf d})
        (carrierEquivList c (PresentedGroup.mk (relatorSet c) (wordOf c v)))) = _
  rw [hc, MulEquiv.symm_apply_eq, leftSplit_mk]

/-- **The inclusion of words is computable**: it is letter-wise reduction
modulo the left alphabet size. -/
theorem computable_normWord (c : PresentationCode) : Computable (normWord c) :=
  (RawTransformPrimrec.primrec_normWord.comp (Primrec.const c) Primrec.id).to_comp

/-! ## The forbidden factor, finite presentation, non-MF -/

/-- The right factor `E` included in the free-product code. -/
noncomputable def forbiddenInclusion (c d : PresentationCode) :
    Carrier d →* Carrier (coprodCode c d) :=
  (coprodCodeEquiv c d).symm.toMonoidHom.comp
    ((inclRight {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d}).comp
      (carrierEquivList d).toMonoidHom)

theorem forbiddenInclusion_injective (c d : PresentationCode) :
    Function.Injective (forbiddenInclusion c d) :=
  (coprodCodeEquiv c d).symm.injective.comp
    ((inclRight_injective {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d}).comp
      (carrierEquivList d).injective)

/-- **`U` is non-MF, since the free factor `E` embeds in it**
(`thm:fixed-radical-membership`). -/
theorem not_isOperatorMF_coprodCode (c d : PresentationCode)
    (hd : ¬ IsOperatorMF (Carrier d)) : ¬ IsOperatorMF (Carrier (coprodCode c d)) :=
  fun h ↦ hd (h.comap (forbiddenInclusion c d) (forbiddenInclusion_injective c d))

/-- **The fixed group `U`**, for the input code `c`: the free product of `c`
with the manuscript's finitely presented non-MF group `E`. -/
noncomputable abbrev fixedRadicalCode (c : PresentationCode) : PresentationCode :=
  coprodCode c negativeCode

/-- **`U` is finitely presented and non-MF** (`thm:fixed-radical-membership`),
for every input code. -/
theorem fixedRadicalCode_fp_not_isOperatorMF (c : PresentationCode) :
    Group.IsFinitelyPresented (Carrier (fixedRadicalCode c)) ∧
      ¬ IsOperatorMF (Carrier (fixedRadicalCode c)) :=
  ⟨inferInstance, not_isOperatorMF_coprodCode c negativeCode not_isOperatorMF_negativeCode⟩

/-! ## The retraction detects the radical -/

/-- **`Res_MF(U) ≤ ker π_A`** (`thm:fixed-radical-membership`): if `A` is MF
its radical is trivial (`prop:univquot`), and radicals map into radicals. -/
theorem radical_le_ker_retraction (c d : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) :
    manuscriptCoronaMFResidual (Carrier (coprodCode c d)) ≤
      (leftFactorRetraction c d).ker := by
  intro x hx
  have hbot : actualCoronaMFResidual (Carrier c) = ⊥ :=
    (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot (G := Carrier c)).mp
      ((isCDEOperatorMF_iff_isOperatorMF (Carrier c)).mpr hMF)
  have hx' : x ∈ actualCoronaMFResidual (Carrier (coprodCode c d)) := by
    rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact hx
  have himg : leftFactorRetraction c d x ∈ actualCoronaMFResidual (Carrier c) :=
    map_actualCoronaMFResidual_le (leftFactorRetraction c d)
      (Subgroup.mem_map_of_mem (leftFactorRetraction c d) hx')
  rw [hbot] at himg
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp himg)

/-- **`i_A(a) ∈ Res_MF(U) ⟺ a = 1`** (`thm:fixed-radical-membership`): "the
forward implication follows by applying `π_A`, and the reverse implication is
trivial." -/
theorem leftFactorInclusion_mem_radical_iff (c d : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) (a : Carrier c) :
    leftFactorInclusion c d a ∈ manuscriptCoronaMFResidual (Carrier (coprodCode c d)) ↔
      a = 1 := by
  constructor
  · intro ha
    have h := radical_le_ker_retraction c d hMF ha
    rw [MonoidHom.mem_ker, leftFactorRetraction_inclusion] at h
    exact h
  · rintro rfl
    rw [map_one]
    exact Subgroup.one_mem _

/-- **Radical membership of an included word is the word problem of `A`.** -/
theorem radicalWordAt_coprodCode_iff (c d : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) (v : List (ℕ × Bool)) :
    RadicalWordAt (coprodCode c d) (normWord c v) ↔ WordProblem c v := by
  have h := leftFactorInclusion_mem_radical_iff c d hMF
    (PresentedGroup.mk (relatorSet c) (wordOf c v))
  rw [leftFactorInclusion_mk] at h
  exact h

/-! ## The reduction -/

/-- **The word problem of an MF `A` many-one reduces to radical membership in
`U`** (`thm:fixed-radical-membership`): "the inclusion of words in the `A`
factor is computable". -/
theorem wordProblem_manyOneReduces_radical (c : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) :
    WordProblem c ≤₀ RadicalWordAt (fixedRadicalCode c) :=
  ⟨normWord c, computable_normWord c,
    fun v ↦ (radicalWordAt_coprodCode_iff c negativeCode hMF v).symm⟩

/-- **The generic part of `thm:fixed-radical-membership`.**  For an MF finitely
presented group `A` with undecidable word problem, membership in the MF radical
of the finitely presented non-MF group `U = A*E` is undecidable: "a
radical-membership algorithm for `U` would decide the word problem of `A`."

The two hypotheses are the concrete properties of the input code.  Producing a
code satisfying both is the Kharlampovich + Tikuisis--White--Winter input of the
printed proof, which is not in the repository. -/
theorem radicalMembership_undecidable_of_mfFactor (c : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) (hWP : ¬ ComputablePred (WordProblem c)) :
    ¬ ComputablePred (RadicalWordAt (fixedRadicalCode c)) := fun h ↦
  hWP (ComputablePred.computable_of_manyOneReducible
    (wordProblem_manyOneReduces_radical c hMF) h)

/-- **All clauses of `thm:fixed-radical-membership` that do not need the input
group**, as one closed proposition: `U` is finitely presented and non-MF for
every code; for MF input the factor inclusion detects the radical exactly, the
word problem many-one reduces to radical membership, and undecidability
transfers. -/
theorem notesFixedRadicalMembershipClauses :
    (∀ c : PresentationCode,
        Group.IsFinitelyPresented (Carrier (fixedRadicalCode c)) ∧
          ¬ IsOperatorMF (Carrier (fixedRadicalCode c))) ∧
      (∀ c : PresentationCode, IsOperatorMF (Carrier c) →
        (∀ a : Carrier c,
          leftFactorInclusion c negativeCode a ∈
              manuscriptCoronaMFResidual (Carrier (fixedRadicalCode c)) ↔ a = 1) ∧
          WordProblem c ≤₀ RadicalWordAt (fixedRadicalCode c) ∧
          (¬ ComputablePred (WordProblem c) →
            ¬ ComputablePred (RadicalWordAt (fixedRadicalCode c)))) :=
  ⟨fixedRadicalCode_fp_not_isOperatorMF, fun c hMF ↦
    ⟨leftFactorInclusion_mem_radical_iff c negativeCode hMF,
      wordProblem_manyOneReduces_radical c hMF,
      radicalMembership_undecidable_of_mfFactor c hMF⟩⟩

#audit_axioms GroupApproximation.Full.NN03.leftSplit_mk
#audit_axioms GroupApproximation.Full.NN03.leftFactorInclusion_mk
#audit_axioms GroupApproximation.Full.NN03.fixedRadicalCode_fp_not_isOperatorMF
#audit_axioms GroupApproximation.Full.NN03.radical_le_ker_retraction
#audit_axioms GroupApproximation.Full.NN03.leftFactorInclusion_mem_radical_iff
#audit_axioms GroupApproximation.Full.NN03.wordProblem_manyOneReduces_radical
#audit_axioms GroupApproximation.Full.NN03.radicalMembership_undecidable_of_mfFactor
#audit_closed_axioms GroupApproximation.Full.NN03.notesFixedRadicalMembershipClauses

end GroupApproximation.Full.NN03
