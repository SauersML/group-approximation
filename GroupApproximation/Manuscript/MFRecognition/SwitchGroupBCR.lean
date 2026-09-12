import GroupApproximation.Manuscript.MFRecognition.SwitchGroupBCRRelators

/-!
# `mf_recognition_complexity.tex`, `lem:switch`: the group `C_e`

> **Lemma (`lem:switch`).**  There is an algorithm that computes from `e` a
> recursive presentation, on a computable set of generators, of a group `C_e`
> such that `C_e` is trivial if `e ∈ INF` and `H` embeds in `C_e` if
> `e ∈ FIN`.

> *Proof.*  Apply the construction of Bilanovic--Chubb--Roven
> [BCR, Theorem 3.1] to the trivial group and `H`.  Let `⟨Y | T⟩` be the
> recursive presentation of `H` from `lem:seed`.  Take generators `y_{i,ℓ}` for
> `i ≥ 1` and `ℓ ∈ Y`, one copy `Y_i` of `Y` for each `i`, and as relators all
> words of `T` rewritten in each copy `Y_i`, together with every generator
> `y_{i,ℓ}` for which `i ≤ |W_e|`.  The last family is recursively enumerable
> uniformly in `e`: enumerate `W_e`, and whenever its `i`-th element appears,
> enumerate all of `Y_i`.  The group presented is the free product of the copies
> `H_i ≅ H`, `i ≥ 1`, with the first `|W_e|` copies killed.  If `W_e` is
> infinite every copy is killed and `C_e` is trivial; if `W_e` is finite, `C_e`
> is the free product of the remaining copies and contains `H`.

Here `H` is the manuscript's own group, `EL₁₂(L_{F₂}(1,2))`, fixed by
`Manuscript.MFRecognition.LeavittSeedPresentation`.  The alphabet, the relators
and the uniform enumerability clause are in
`Manuscript.MFRecognition.SwitchGroupBCRRelators`, which also fixes the
dictionary `W_e = codeDomain e`, `INF = InfiniteDomain`, `FIN = FiniteDomain`,
and `Killed e i` for the printed `i + 1 ≤ |W_e|`.

Everything in this file is proved.  The lane's one cited input is
`LeavittSeedPresentation.DiamondLemmaWordProblem`, the decidability half of
`lem:seed`; it is a leading hypothesis of every declaration that uses it, so it
is visible in the statement of `manuscriptSwitch`.

## The free-product clause

The printed sentence "the group presented is the free product of the copies
`H_i ≅ H` with the first `|W_e|` copies killed" is rendered by three proved
statements: `copyHom_eq_one_of_killed` (a killed copy is trivial),
`copyHom_injective` (a surviving copy embeds --- the free-product retraction
onto one factor, which is exactly what the printed proof uses), and
`iSup_range_copyHom_eq_top` (the copies generate).

## The output syntax

The compiler emits a `Nat.Partrec.Code`, read by
`Computability.EnumeratedPresentationCodes`.  That is the code type consumed by
`Computability.HereditaryPropertySwitchCompleteness`, so `manuscriptSwitch`
plugs into the bridge lanes without translation.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace LeavittSwitch

open Nat.Partrec
open Higman
open CodeDovetailStageEvents
open SecondLevelIndexSets

noncomputable section

/-! ## The group `C_e` -/

/-- **`lem:switch`, the relator set.** -/
def switchRelators (hDiamond : DiamondLemmaWordProblem) (c : Code) :
    Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (rawSwitchRelator hDiamond c address)

/-- **`lem:switch`.**  The group `C_e`: the free product of the copies `H_i`
with the first `|W_e|` copies killed, presented on the generators `y_{i,ℓ}`. -/
abbrev BCRGroup (hDiamond : DiamondLemmaWordProblem) (c : Code) : Type :=
  PresentedGroup (switchRelators hDiamond c)

theorem one_mem_switchRelators (hDiamond : DiamondLemmaWordProblem) (c : Code) :
    (1 : FreeGroup ℕ) ∈ switchRelators hDiamond c := by
  refine ⟨Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0)), ?_⟩
  show freeEval
    (rawSwitchRelator hDiamond c (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0)))) = 1
  have e1 : addrFamily (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))) = 1 :=
    addrFamily_pair _ _
  have e2 : addrCopy (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))) = 0 :=
    addrCopy_pair _ _ _ _
  have e4 : addrSnd (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))) = 0 :=
    addrSnd_pair _ _ _ _
  have hfam : ¬ addrFamily (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))) % 2 = 0 := by
    omega
  have hlt : ¬ addrCopy (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))) <
      eventCount c (addrSnd (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0)))) := by
    rw [e2, e4, eventCount_zero]
    omega
  calc freeEval
        (rawSwitchRelator hDiamond c (Nat.pair 1 (Nat.pair 0 (Nat.pair 0 0))))
      = freeEval ([] : RawWord) := by
        rw [rawSwitchRelator_kill_nil hDiamond c _ hfam hlt]
    _ = 1 := rfl

/-- **`lem:switch`.**  "All words of `T` rewritten in each copy `Y_i`" are
relators. -/
theorem copy_mem_switchRelators (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i : ℕ) (w : RawWord) (hw : evalRaw seedGen w = 1) :
    freeEval (copyRaw i w) ∈ switchRelators hDiamond c := by
  obtain ⟨m, hm⟩ :=
    (seedSearch_spec hDiamond w).1 ((mem_seedRelators w).2 hw)
  refine ⟨Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m)), ?_⟩
  show freeEval (rawSwitchRelator hDiamond c
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m)))) =
    freeEval (copyRaw i w)
  have e1 : addrFamily
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) = 0 :=
    addrFamily_pair _ _
  have e2 : addrCopy
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) = i :=
    addrCopy_pair _ _ _ _
  have e3 : addrFst
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) =
      Encodable.encode w := addrFst_pair _ _ _ _
  have e4 : addrSnd
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) = m :=
    addrSnd_pair _ _ _ _
  have hdec : EnumeratedPresentationCodes.decodeRawWord
      (addrFst (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))))
      = w := by
    rw [e3]
    simp [EnumeratedPresentationCodes.decodeRawWord, Encodable.encodek]
  have hfam : addrFamily
      (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) % 2 = 0 := by
    omega
  have hsr : seedSearch hDiamond (EnumeratedPresentationCodes.decodeRawWord
      (addrFst (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m)))))
      (addrSnd (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))))
      = true := by
    rw [hdec, e4]
    exact hm
  have hraw := rawSwitchRelator_copy hDiamond c
    (Nat.pair 0 (Nat.pair i (Nat.pair (Encodable.encode w) m))) hfam hsr
  rw [e2, hdec] at hraw
  rw [hraw]

/-- **`lem:switch`.**  "Together with every generator `y_{i,ℓ}` for which
`i ≤ |W_e|`." -/
theorem kill_mem_switchRelators (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i n : ℕ) (hi : Killed c i) :
    FreeGroup.of (Nat.pair i n) ∈ switchRelators hDiamond c := by
  obtain ⟨s, hstage⟩ := hi
  refine ⟨Nat.pair 1 (Nat.pair i (Nat.pair n s)), ?_⟩
  show freeEval
      (rawSwitchRelator hDiamond c (Nat.pair 1 (Nat.pair i (Nat.pair n s)))) =
    FreeGroup.of (Nat.pair i n)
  have e1 : addrFamily (Nat.pair 1 (Nat.pair i (Nat.pair n s))) = 1 :=
    addrFamily_pair _ _
  have e2 : addrCopy (Nat.pair 1 (Nat.pair i (Nat.pair n s))) = i :=
    addrCopy_pair _ _ _ _
  have e3 : addrFst (Nat.pair 1 (Nat.pair i (Nat.pair n s))) = n :=
    addrFst_pair _ _ _ _
  have e4 : addrSnd (Nat.pair 1 (Nat.pair i (Nat.pair n s))) = s :=
    addrSnd_pair _ _ _ _
  have hfam : ¬ addrFamily (Nat.pair 1 (Nat.pair i (Nat.pair n s))) % 2 = 0 := by
    omega
  have hlt : addrCopy (Nat.pair 1 (Nat.pair i (Nat.pair n s))) <
      eventCount c (addrSnd (Nat.pair 1 (Nat.pair i (Nat.pair n s)))) := by
    rw [e2, e4]
    exact hstage
  have hraw := rawSwitchRelator_kill hDiamond c
    (Nat.pair 1 (Nat.pair i (Nat.pair n s))) hfam hlt
  rw [e2, e3] at hraw
  rw [hraw, freeEval_killRaw]

/-- **The universal property of `C_e`.**  A family of images of the generators
`y_{i,ℓ}` that kills the copied relators of `T` and the killed generators kills
every relator of `C_e`. -/
theorem lift_eq_one_of_mem_switchRelators (hDiamond : DiamondLemmaWordProblem)
    {G : Type} [Group G] (c : Code) (f : ℕ → G)
    (hcopy : ∀ (i : ℕ) (w : RawWord), evalRaw seedGen w = 1 →
      evalRaw (fun n => f (Nat.pair i n)) w = 1)
    (hkill : ∀ i n : ℕ, Killed c i → f (Nat.pair i n) = 1) :
    ∀ r ∈ switchRelators hDiamond c, FreeGroup.lift f r = 1 := by
  rintro _ ⟨address, rfl⟩
  show FreeGroup.lift f (freeEval (rawSwitchRelator hDiamond c address)) = 1
  rw [Higman.lift_freeEval]
  by_cases hfam : addrFamily address % 2 = 0
  · by_cases hsr : seedSearch hDiamond
        (EnumeratedPresentationCodes.decodeRawWord (addrFst address))
        (addrSnd address) = true
    · have hword : evalRaw seedGen
          (EnumeratedPresentationCodes.decodeRawWord (addrFst address)) = 1 :=
        (mem_seedRelators _).1 ((seedSearch_spec hDiamond _).2 ⟨_, hsr⟩)
      rw [rawSwitchRelator_copy hDiamond c address hfam hsr, evalRaw_copyRaw]
      exact hcopy (addrCopy address) _ hword
    · simp only [rawSwitchRelator_copy_nil hDiamond c address hfam hsr,
        Higman.evalRaw_nil]
  · by_cases hlt : addrCopy address < eventCount c (addrSnd address)
    · rw [rawSwitchRelator_kill hDiamond c address hfam hlt, evalRaw_killRaw]
      exact hkill (addrCopy address) (addrFst address) ⟨addrSnd address, hlt⟩
    · simp only [rawSwitchRelator_kill_nil hDiamond c address hfam hlt,
        Higman.evalRaw_nil]

/-! ## The copies of `H` -/

theorem evalRaw_pairGen (hDiamond : DiamondLemmaWordProblem) (c : Code) (i : ℕ)
    (w : RawWord) :
    evalRaw
        (fun n => (PresentedGroup.of (Nat.pair i n) : BCRGroup hDiamond c)) w =
      PresentedGroup.mk (switchRelators hDiamond c) (freeEval (copyRaw i w)) := by
  rw [← Higman.evalRaw_presentedGroup_of (switchRelators hDiamond c)
    (copyRaw i w), evalRaw_copyRaw]

/-- **`lem:switch`.**  The copy `Y_i` of the presentation `⟨Y | T⟩` inside
`C_e`. -/
def seedCopyHom (hDiamond : DiamondLemmaWordProblem) (c : Code) (i : ℕ) :
    PresentedGroup seedRelators →* BCRGroup hDiamond c :=
  PresentedGroup.toGroup
    (f := fun n => (PresentedGroup.of (Nat.pair i n) : BCRGroup hDiamond c))
    (by
      intro r hr
      obtain ⟨w, rfl⟩ := freeEval_surjective r
      have hw : evalRaw seedGen w = 1 := (mem_seedRelators w).1 hr
      rw [Higman.lift_freeEval, evalRaw_pairGen]
      exact PresentedGroup.mk_eq_one_iff.2
        (Subgroup.subset_normalClosure
          (copy_mem_switchRelators hDiamond c i w hw)))

@[simp] theorem seedCopyHom_of (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i n : ℕ) :
    seedCopyHom hDiamond c i (PresentedGroup.of n) =
      (PresentedGroup.of (Nat.pair i n) : BCRGroup hDiamond c) :=
  PresentedGroup.toGroup.of _

/-- **`lem:switch`.**  The copy `H_i ≅ H` inside `C_e`. -/
def copyHom (hDiamond : DiamondLemmaWordProblem) (c : Code) (i : ℕ) :
    H →* BCRGroup hDiamond c :=
  (seedCopyHom hDiamond c i).comp seedEquiv.symm.toMonoidHom

theorem copyHom_seedEquiv (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i : ℕ) (x : PresentedGroup seedRelators) :
    copyHom hDiamond c i (seedEquiv x) = seedCopyHom hDiamond c i x := by
  show seedCopyHom hDiamond c i (seedEquiv.symm (seedEquiv x)) =
    seedCopyHom hDiamond c i x
  rw [MulEquiv.symm_apply_apply]

/-! ## The killed copies are trivial -/

theorem of_eq_one_of_killed (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i n : ℕ) (hi : Killed c i) :
    (PresentedGroup.of (Nat.pair i n) : BCRGroup hDiamond c) = 1 :=
  PresentedGroup.one_of_mem (kill_mem_switchRelators hDiamond c i n hi)

theorem seedCopyHom_eq_one_of_killed (hDiamond : DiamondLemmaWordProblem)
    (c : Code) (i : ℕ) (hi : Killed c i) :
    seedCopyHom hDiamond c i = 1 := by
  apply PresentedGroup.ext
  intro n
  rw [seedCopyHom_of, MonoidHom.one_apply]
  exact of_eq_one_of_killed hDiamond c i n hi

/-- **`lem:switch`.**  "With the first `|W_e|` copies killed." -/
theorem copyHom_eq_one_of_killed (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (i : ℕ) (hi : Killed c i) (x : H) :
    copyHom hDiamond c i x = 1 := by
  show seedCopyHom hDiamond c i (seedEquiv.symm x) = 1
  rw [seedCopyHom_eq_one_of_killed hDiamond c i hi, MonoidHom.one_apply]

/-! ## The surviving copies embed

This is the free-product retraction the printed proof uses: collapse every copy
but one. -/

/-- Collapse every copy but the copy `i₀`. -/
def collapseGen (i₀ : ℕ) (m : ℕ) : PresentedGroup seedRelators :=
  if (Nat.unpair m).1 = i₀ then PresentedGroup.of (Nat.unpair m).2 else 1

theorem collapseGen_pair (i₀ i n : ℕ) :
    collapseGen i₀ (Nat.pair i n) =
      if i = i₀ then (PresentedGroup.of n : PresentedGroup seedRelators)
      else 1 := by
  simp [collapseGen]

/-- **`lem:switch`.**  The retraction of `C_e` onto a surviving copy. -/
def collapseHom (hDiamond : DiamondLemmaWordProblem) (c : Code) {i₀ : ℕ}
    (hi₀ : ¬ Killed c i₀) :
    BCRGroup hDiamond c →* PresentedGroup seedRelators :=
  PresentedGroup.toGroup (f := collapseGen i₀)
    (lift_eq_one_of_mem_switchRelators hDiamond c (collapseGen i₀)
      (by
        intro i w hw
        by_cases hii : i = i₀
        · have hfun : (fun n => collapseGen i₀ (Nat.pair i n)) =
              fun n => (PresentedGroup.of n : PresentedGroup seedRelators) := by
            funext n
            rw [collapseGen_pair, if_pos hii]
          rw [hfun, Higman.evalRaw_presentedGroup_of]
          exact PresentedGroup.mk_eq_one_iff.2
            (Subgroup.subset_normalClosure ((mem_seedRelators w).2 hw))
        · refine Higman.evalRaw_eq_one_of_letters _ w ?_
          intro p _
          show collapseGen i₀ (Nat.pair i p.1) = 1
          rw [collapseGen_pair, if_neg hii])
      (by
        intro i n hi
        have hne : i ≠ i₀ := by
          rintro rfl
          exact hi₀ hi
        rw [collapseGen_pair, if_neg hne]))

@[simp] theorem collapseHom_of (hDiamond : DiamondLemmaWordProblem) (c : Code)
    {i₀ : ℕ} (hi₀ : ¬ Killed c i₀) (m : ℕ) :
    collapseHom hDiamond c hi₀ (PresentedGroup.of m) = collapseGen i₀ m :=
  PresentedGroup.toGroup.of _

theorem collapseHom_comp_seedCopyHom (hDiamond : DiamondLemmaWordProblem)
    (c : Code) {i₀ : ℕ} (hi₀ : ¬ Killed c i₀) :
    (collapseHom hDiamond c hi₀).comp (seedCopyHom hDiamond c i₀) =
      MonoidHom.id (PresentedGroup seedRelators) := by
  apply PresentedGroup.ext
  intro n
  rw [MonoidHom.comp_apply, seedCopyHom_of, collapseHom_of, collapseGen_pair,
    if_pos rfl, MonoidHom.id_apply]

theorem seedCopyHom_injective (hDiamond : DiamondLemmaWordProblem) (c : Code)
    {i₀ : ℕ} (hi₀ : ¬ Killed c i₀) :
    Function.Injective (seedCopyHom hDiamond c i₀) := by
  have hleft : Function.LeftInverse (collapseHom hDiamond c hi₀)
      (seedCopyHom hDiamond c i₀) := by
    intro x
    exact congrArg
      (fun g : PresentedGroup seedRelators →* PresentedGroup seedRelators => g x)
      (collapseHom_comp_seedCopyHom hDiamond c hi₀)
  exact hleft.injective

/-- **`lem:switch`.**  "`C_e` is the free product of the remaining copies and
contains `H`": a surviving copy of `H` embeds in `C_e`. -/
theorem copyHom_injective (hDiamond : DiamondLemmaWordProblem) (c : Code)
    {i₀ : ℕ} (hi₀ : ¬ Killed c i₀) :
    Function.Injective (copyHom hDiamond c i₀) := by
  intro x y hxy
  have h : seedCopyHom hDiamond c i₀ (seedEquiv.symm x) =
      seedCopyHom hDiamond c i₀ (seedEquiv.symm y) := hxy
  exact seedEquiv.symm.injective (seedCopyHom_injective hDiamond c hi₀ h)

/-- The copies generate `C_e`. -/
theorem iSup_range_copyHom_eq_top (hDiamond : DiamondLemmaWordProblem)
    (c : Code) :
    (⨆ i : ℕ, (copyHom hDiamond c i).range) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (switchRelators hDiamond c),
    Subgroup.closure_le]
  rintro _ ⟨m, rfl⟩
  have hmem : (PresentedGroup.of m : BCRGroup hDiamond c) ∈
      (copyHom hDiamond c (Nat.unpair m).1).range := by
    refine ⟨seedEquiv (PresentedGroup.of (Nat.unpair m).2), ?_⟩
    rw [copyHom_seedEquiv, seedCopyHom_of, Nat.pair_unpair]
  have hle : (copyHom hDiamond c (Nat.unpair m).1).range ≤
      ⨆ i : ℕ, (copyHom hDiamond c i).range :=
    le_iSup (fun i : ℕ => (copyHom hDiamond c i).range) (Nat.unpair m).1
  exact hle hmem

/-! ## The two branches -/

/-- **`lem:switch`.**  "If `W_e` is infinite every copy is killed and `C_e` is
trivial." -/
theorem subsingleton_of_infiniteDomain (hDiamond : DiamondLemmaWordProblem)
    (c : Code) (hc : InfiniteDomain c) : Subsingleton (BCRGroup hDiamond c) := by
  have hgen : ∀ m : ℕ, (PresentedGroup.of m : BCRGroup hDiamond c) = 1 := by
    intro m
    have h := of_eq_one_of_killed hDiamond c (Nat.unpair m).1 (Nat.unpair m).2
      (killed_of_infiniteDomain c hc (Nat.unpair m).1)
    rwa [Nat.pair_unpair] at h
  have hle : Subgroup.closure
      (Set.range (PresentedGroup.of : ℕ → BCRGroup hDiamond c)) ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨m, rfl⟩
    exact Subgroup.mem_bot.mpr (hgen m)
  have hbot : (⊥ : Subgroup (BCRGroup hDiamond c)) = ⊤ := by
    apply le_antisymm bot_le
    rw [← PresentedGroup.closure_range_of (switchRelators hDiamond c)]
    exact hle
  constructor
  intro x y
  apply eq_of_mul_inv_eq_one
  apply Subgroup.mem_bot.mp
  rw [hbot]
  exact Subgroup.mem_top _

/-- A group with at most one element is the trivial group. -/
def equivPUnitOfSubsingleton (G : Type) [Group G] [Subsingleton G] :
    G ≃* PUnit.{1} where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 1
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  map_mul' := fun _ _ => rfl

/-- **`lem:switch`.**  "`H` embeds in `C_e` if `e ∈ FIN`." -/
theorem exists_injective_of_finiteDomain (hDiamond : DiamondLemmaWordProblem)
    (c : Code) (hc : FiniteDomain c) :
    ∃ f : H →* BCRGroup hDiamond c, Function.Injective f := by
  obtain ⟨i₀, hi₀⟩ := exists_not_killed_of_finiteDomain c hc
  exact ⟨copyHom hDiamond c i₀, copyHom_injective hDiamond c hi₀⟩

/-! ## The compiler `e ↦ C_e` -/

/-- Total decoding of a source program. -/
def decodeSourceCode (n : ℕ) : Code :=
  (Encodable.decode (α := Code) n).getD Code.zero

theorem primrec_decodeSourceCode : Primrec decodeSourceCode :=
  Primrec.option_getD.comp (@Primrec.decode Code _) (Primrec.const Code.zero)

/-- The uncurried partial function named by one universal enumerator program. -/
def encodedEnumerator (hDiamond : DiamondLemmaWordProblem) (input : ℕ) :
    Part ℕ :=
  Part.some (Encodable.encode
    (rawSwitchRelator hDiamond (decodeSourceCode (Nat.unpair input).1)
      (Nat.unpair input).2))

theorem encodedEnumerator_partrec (hDiamond : DiamondLemmaWordProblem) :
    Nat.Partrec (encodedEnumerator hDiamond) := by
  have hcode : Primrec fun input : ℕ => decodeSourceCode (Nat.unpair input).1 :=
    primrec_decodeSourceCode.comp (Primrec.fst.comp Primrec.unpair)
  have haddr : Primrec fun input : ℕ => (Nat.unpair input).2 :=
    Primrec.snd.comp Primrec.unpair
  have hvalue : Primrec fun input : ℕ => Encodable.encode
      (rawSwitchRelator hDiamond (decodeSourceCode (Nat.unpair input).1)
        (Nat.unpair input).2) :=
    Primrec.encode.comp
      ((primrec_rawSwitchRelator hDiamond).comp (Primrec.pair hcode haddr))
  exact Nat.Partrec.of_primrec (Primrec.nat_iff.mp hvalue)

/-- One fixed program for the encoded `(source, address)` enumerator. -/
def universalEnumeratorCode (hDiamond : DiamondLemmaWordProblem) : Code :=
  (Code.exists_code.mp (encodedEnumerator_partrec hDiamond)).choose

theorem eval_universalEnumeratorCode (hDiamond : DiamondLemmaWordProblem) :
    Code.eval (universalEnumeratorCode hDiamond) = encodedEnumerator hDiamond :=
  (Code.exists_code.mp (encodedEnumerator_partrec hDiamond)).choose_spec

/-- **`lem:switch`, the algorithm.**  The map sending `e` to a recursive
presentation of `C_e`. -/
def bcrCode (hDiamond : DiamondLemmaWordProblem) (c : Code) : Code :=
  Code.curry (universalEnumeratorCode hDiamond) (Encodable.encode c)

/-- **`lem:switch`.**  "There is an algorithm that computes from `e` a recursive
presentation ... of a group `C_e`." -/
theorem computable_bcrCode (hDiamond : DiamondLemmaWordProblem) :
    Computable (bcrCode hDiamond) :=
  (Code.primrec₂_curry.comp
    (Primrec.const (universalEnumeratorCode hDiamond)) Primrec.encode).to_comp

theorem eval_bcrCode (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) :
    Code.eval (bcrCode hDiamond c) address =
      Part.some (Encodable.encode (rawSwitchRelator hDiamond c address)) := by
  rw [bcrCode, Code.eval_curry, eval_universalEnumeratorCode]
  simp [encodedEnumerator, decodeSourceCode]

/-- Reading the compiled program through the standard enumerated-presentation
syntax recovers exactly the relator set of `C_e`. -/
theorem standard_relatorSet_eq (hDiamond : DiamondLemmaWordProblem) (c : Code) :
    EnumeratedPresentationCodes.relatorSet (bcrCode hDiamond c) =
      switchRelators hDiamond c := by
  ext x
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    show freeEval (EnumeratedPresentationCodes.rawRelator (bcrCode hDiamond c)
      encodedAddress) ∈ switchRelators hDiamond c
    cases heval : Code.evaln (Nat.unpair encodedAddress).2 (bcrCode hDiamond c)
        (Nat.unpair encodedAddress).1 with
    | none =>
        have hzero : EnumeratedPresentationCodes.rawRelator (bcrCode hDiamond c)
            encodedAddress = [] := by
          simp [EnumeratedPresentationCodes.rawRelator, heval]
        rw [hzero]
        exact one_mem_switchRelators hDiamond c
    | some y =>
        have hsound : y ∈ Code.eval (bcrCode hDiamond c)
            (Nat.unpair encodedAddress).1 := Code.evaln_sound heval
        rw [eval_bcrCode] at hsound
        have hy : y = Encodable.encode
            (rawSwitchRelator hDiamond c (Nat.unpair encodedAddress).1) := by
          simpa using hsound
        refine ⟨(Nat.unpair encodedAddress).1, ?_⟩
        simp [EnumeratedPresentationCodes.rawRelator,
          EnumeratedPresentationCodes.decodeRawWord, heval, hy]
  · rintro ⟨address, rfl⟩
    show freeEval (rawSwitchRelator hDiamond c address) ∈
      EnumeratedPresentationCodes.relatorSet (bcrCode hDiamond c)
    have hmem : Encodable.encode (rawSwitchRelator hDiamond c address) ∈
        Code.eval (bcrCode hDiamond c) address := by
      rw [eval_bcrCode]
      exact Part.mem_some _
    obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hmem
    have hstage' : Code.evaln stage (bcrCode hDiamond c) address =
        some (Encodable.encode (rawSwitchRelator hDiamond c address)) := hstage
    refine ⟨Nat.pair address stage, ?_⟩
    simp [EnumeratedPresentationCodes.rawRelator,
      EnumeratedPresentationCodes.decodeRawWord, hstage']

/-- The carrier emitted by the compiler. -/
abbrev CompiledCarrier (hDiamond : DiamondLemmaWordProblem) (c : Code) : Type :=
  EnumeratedPresentationCodes.Carrier (bcrCode hDiamond c)

/-- The compiled carrier is the group `C_e`. -/
def compiledEquiv (hDiamond : DiamondLemmaWordProblem) (c : Code) :
    CompiledCarrier hDiamond c ≃* BCRGroup hDiamond c := by
  have hnormal :
      Subgroup.normalClosure
          (EnumeratedPresentationCodes.relatorSet (bcrCode hDiamond c)) =
        Subgroup.normalClosure (switchRelators hDiamond c) := by
    rw [standard_relatorSet_eq]
  change (FreeGroup ℕ ⧸ Subgroup.normalClosure
      (EnumeratedPresentationCodes.relatorSet (bcrCode hDiamond c))) ≃*
    (FreeGroup ℕ ⧸ Subgroup.normalClosure (switchRelators hDiamond c))
  exact QuotientGroup.quotientMulEquivOfEq hnormal

/-! ## The lemma -/

/-- **The statement of `lem:switch`.**  There is an algorithm that computes from
`e` a recursive presentation, on a computable set of generators, of a group
`C_e` such that `C_e` is trivial if `e ∈ INF` and `H` embeds in `C_e` if
`e ∈ FIN`.

The hypothesis is the decidability half of `lem:seed`; see
`DiamondLemmaWordProblem`. -/
def PrintedSwitchLemma (hDiamond : DiamondLemmaWordProblem) : Prop :=
  Computable (bcrCode hDiamond) ∧
    ∀ c : Code,
      Nonempty (Higman.RecursivePresentation (CompiledCarrier hDiamond c)) ∧
        (InfiniteDomain c →
          Nonempty (CompiledCarrier hDiamond c ≃* PUnit.{1})) ∧
        (FiniteDomain c →
          ∃ f : H →* CompiledCarrier hDiamond c, Function.Injective f)

/-- **`lem:switch`**, by the printed Bilanovic--Chubb--Roven construction. -/
theorem manuscriptSwitch (hDiamond : DiamondLemmaWordProblem) :
    PrintedSwitchLemma hDiamond := by
  refine ⟨computable_bcrCode hDiamond, fun c => ⟨?_, ?_, ?_⟩⟩
  · exact ⟨EnumeratedPresentationCodes.recursivePresentation (bcrCode hDiamond c)⟩
  · intro hc
    letI : Subsingleton (BCRGroup hDiamond c) :=
      subsingleton_of_infiniteDomain hDiamond c hc
    letI : Subsingleton (CompiledCarrier hDiamond c) :=
      ⟨fun x y => (compiledEquiv hDiamond c).injective
        (Subsingleton.elim (compiledEquiv hDiamond c x)
          (compiledEquiv hDiamond c y))⟩
    exact ⟨equivPUnitOfSubsingleton (CompiledCarrier hDiamond c)⟩
  · intro hc
    obtain ⟨f, hf⟩ := exists_injective_of_finiteDomain hDiamond c hc
    refine ⟨((compiledEquiv hDiamond c).symm.toMonoidHom).comp f, ?_⟩
    intro x y hxy
    have h : (compiledEquiv hDiamond c).symm (f x) =
        (compiledEquiv hDiamond c).symm (f y) := hxy
    exact hf ((compiledEquiv hDiamond c).symm.injective h)

end

end LeavittSwitch
end MFRecognition
end Manuscript
end GroupApproximation
