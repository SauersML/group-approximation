import GroupApproximation.Computability.CodeDovetailStageEvents
import GroupApproximation.Computability.SecondLevelIndexSets
import GroupApproximation.Manuscript.MFRecognition.LeavittSeedPresentation

/-!
# `mf_recognition_complexity.tex`, `lem:switch`: the relators of `C_e`

The first half of `lem:switch` at the manuscript's own group `H`: the alphabet
`y_{i,ℓ}` of the Bilanovic--Chubb--Roven presentation, its relators, and the
clause

> The last family is recursively enumerable uniformly in `e`: enumerate `W_e`,
> and whenever its `i`-th element appears, enumerate all of `Y_i`.

`Manuscript.MFRecognition.SwitchGroupBCR` builds the group `C_e` on top of this
file and proves the two branches.  Everything here is proved.  The lane's one
cited input is `LeavittSeedPresentation.DiamondLemmaWordProblem`, which reaches
this file only through `seedSearch`, and is carried as a leading hypothesis by
the declarations that use it.

## The dictionary

`W_e` is `SecondLevelIndexSets.codeDomain e`, `INF` is
`SecondLevelIndexSets.InfiniteDomain` and `FIN` is
`SecondLevelIndexSets.FiniteDomain`; these are the repository's `Pi^0_2`- and
`Sigma^0_2`-complete index sets.

"Enumerate `W_e`, and whenever its `i`-th element appears" is the repository's
dovetail stream `CodeDovetailStageEvents.dovetailEvent`: each element of `W_e`
emits exactly one event, at its least halting stage, so the number of events at
addresses below a bound --- `eventCount` --- is the number of elements of `W_e`
seen so far.  `Killed e i`, that is `∃ s, i < eventCount e s`, is therefore
literally "the `i`-th element of `W_e` appears"; copies are indexed from `0`, so
the copy with index `i` is the printed copy `y_{i+1,·}`, and `Killed e i` is the
printed condition `i + 1 ≤ |W_e|`.

The generator `y_{i,ℓ}` is the standard alphabet letter `Nat.pair i ℓ`, where
`ℓ` indexes the generating family of `lem:seed`.
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

/-! ## Counting the elements of `W_e` that have appeared -/

/-- The number of dovetail events at addresses below `s`: the number of
elements of `W_e` that the enumeration has produced by stage `s`. -/
def eventCount (c : Code) (s : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun t ih => ih + (if dovetailEvent c t = true then 1 else 0)) s

@[simp] theorem eventCount_zero (c : Code) : eventCount c 0 = 0 := rfl

@[simp] theorem eventCount_succ (c : Code) (s : ℕ) :
    eventCount c (s + 1) =
      eventCount c s + (if dovetailEvent c s = true then 1 else 0) := rfl

theorem primrec_eventCount :
    Primrec fun z : Code × ℕ => eventCount z.1 z.2 := by
  have hb : Primrec fun x : (Code × ℕ) × (ℕ × ℕ) =>
      dovetailEvent x.1.1 x.2.1 :=
    primrec_dovetailEvent.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂ fun (z : Code × ℕ) (p : ℕ × ℕ) =>
      p.2 + (if dovetailEvent z.1 p.1 = true then 1 else 0) :=
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp hb (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))).to₂
  exact (Primrec.nat_rec' (h := fun (z : Code × ℕ) (p : ℕ × ℕ) =>
      p.2 + (if dovetailEvent z.1 p.1 = true then 1 else 0))
    Primrec.snd (Primrec.const 0) hstep).of_eq fun _ => rfl

theorem eventCount_le_succ (c : Code) (s : ℕ) :
    eventCount c s ≤ eventCount c (s + 1) := by
  rw [eventCount_succ]
  exact Nat.le_add_right _ _

theorem eventCount_mono (c : Code) {s t : ℕ} (h : s ≤ t) :
    eventCount c s ≤ eventCount c t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
      refine le_trans ih ?_
      have hidx : s + (d + 1) = s + d + 1 := by omega
      rw [hidx]
      exact eventCount_le_succ c (s + d)

/-! ## The killed copies

"Together with every generator `y_{i,ℓ}` for which `i ≤ |W_e|`.  The last family
is recursively enumerable uniformly in `e`: enumerate `W_e`, and whenever its
`i`-th element appears, enumerate all of `Y_i`." -/

/-- **`lem:switch`.**  Copy `i` is killed exactly when the `i`-th element of
`W_e` appears, that is, when at some stage the enumeration of `W_e` has produced
more than `i` elements.  With copies indexed from `0` this is the printed
condition `i + 1 ≤ |W_e|` on the printed copy `y_{i+1,·}`. -/
def Killed (c : Code) (i : ℕ) : Prop := ∃ s, i < eventCount c s

/-- **`lem:switch`, the infinite branch.**  "If `W_e` is infinite every copy is
killed." -/
theorem killed_of_infiniteDomain (c : Code) (hc : InfiniteDomain c) (i : ℕ) :
    Killed c i := by
  induction i with
  | zero =>
      obtain ⟨k, -, hk⟩ := infiniteDomain_infiniteEvents c hc 0
      have hk' : dovetailEvent c k = true := hk
      have hone : (if dovetailEvent c k = true then 1 else 0) = 1 := if_pos hk'
      refine ⟨k + 1, ?_⟩
      rw [eventCount_succ, hone]
      omega
  | succ i ih =>
      obtain ⟨s, hsi⟩ := ih
      obtain ⟨k, hsk, hk⟩ := infiniteDomain_infiniteEvents c hc s
      have hk' : dovetailEvent c k = true := hk
      have hone : (if dovetailEvent c k = true then 1 else 0) = 1 := if_pos hk'
      have hmono : eventCount c s ≤ eventCount c k := eventCount_mono c hsk
      refine ⟨k + 1, ?_⟩
      rw [eventCount_succ, hone]
      omega

/-- A finite domain gives a bound above every dovetail event address. -/
theorem exists_event_bound (c : Code) (hc : FiniteDomain c) :
    ∃ last : ℕ, ∀ k : ℕ, dovetailEvent c k = true → k ≤ last := by
  have hfin := finite_event_addresses_of_finiteDomain c hc
  by_cases hempty : {address | dovetailEvent c address = true} = ∅
  · refine ⟨0, fun k hk => ?_⟩
    have hmem : k ∈ {address | dovetailEvent c address = true} := hk
    rw [hempty] at hmem
    exact absurd hmem (Set.notMem_empty k)
  · obtain ⟨last, -, hmax⟩ :=
      Set.exists_max_image {address | dovetailEvent c address = true} id hfin
        (Set.nonempty_iff_ne_empty.mpr hempty)
    exact ⟨last, fun k hk => hmax k hk⟩

/-- **`lem:switch`, the finite branch.**  "If `W_e` is finite, `C_e` is the free
product of the remaining copies": some copy survives. -/
theorem exists_not_killed_of_finiteDomain (c : Code) (hc : FiniteDomain c) :
    ∃ i : ℕ, ¬ Killed c i := by
  obtain ⟨last, hlast⟩ := exists_event_bound c hc
  have htail : ∀ d : ℕ,
      eventCount c (last + 1 + d) = eventCount c (last + 1) := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
        have hfalse : ¬ dovetailEvent c (last + 1 + d) = true := by
          intro hne
          have hle := hlast (last + 1 + d) hne
          omega
        have hstep : eventCount c (last + 1 + d + 1) =
            eventCount c (last + 1 + d) := by
          simp [hfalse]
        have hidx : last + 1 + (d + 1) = last + 1 + d + 1 := by omega
        rw [hidx, hstep, ih]
  have hbound : ∀ s : ℕ, eventCount c s ≤ eventCount c (last + 1) := by
    intro s
    rcases le_or_gt s (last + 1) with h | h
    · exact eventCount_mono c h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
      rw [hd]
      exact le_of_eq (htail d)
  refine ⟨eventCount c (last + 1), ?_⟩
  rintro ⟨s, hlt⟩
  have hbs := hbound s
  omega

/-! ## The alphabet of the presentation

The generator `y_{i,ℓ}` is the standard alphabet letter `Nat.pair i ℓ`. -/

/-- Move a raw word into the copy `Y_i`. -/
def copyRaw (i : ℕ) (w : RawWord) : RawWord :=
  w.map fun p => (Nat.pair i p.1, p.2)

@[simp] theorem copyRaw_nil (i : ℕ) : copyRaw i ([] : RawWord) = [] := rfl

@[simp] theorem copyRaw_cons (i n : ℕ) (b : Bool) (w : RawWord) :
    copyRaw i ((n, b) :: w) = (Nat.pair i n, b) :: copyRaw i w := rfl

/-- The relator `y_{i,ℓ}` that kills one generator of the copy `Y_i`. -/
def killRaw (i n : ℕ) : RawWord := [(Nat.pair i n, true)]

theorem evalRaw_copyRaw {G : Type} [Group G] (f : ℕ → G) (i : ℕ) (w : RawWord) :
    evalRaw f (copyRaw i w) = evalRaw (fun n => f (Nat.pair i n)) w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      obtain ⟨n, b⟩ := p
      rw [copyRaw_cons, evalRaw_cons, evalRaw_cons, ih]

theorem evalRaw_killRaw {G : Type} [Group G] (f : ℕ → G) (i n : ℕ) :
    evalRaw f (killRaw i n) = f (Nat.pair i n) := by
  show evalRaw f [(Nat.pair i n, true)] = f (Nat.pair i n)
  simp

theorem freeEval_killRaw (i n : ℕ) :
    freeEval (killRaw i n) = FreeGroup.of (Nat.pair i n) :=
  evalRaw_killRaw FreeGroup.of i n

/-! ## The relator enumerator, uniformly in `e`

An address is read as `(family, (i, (u, v)))`.  The even families carry the
relators of `T` rewritten in the copy `Y_i`: `u` codes a raw word and `v` is the
witness that the word lies in `T`.  The odd families carry the killed
generators: `u` is the generator index `ℓ` and `v` the stage by which the `i`-th
element of `W_e` is required to have appeared. -/

/-- The family selector of an address. -/
def addrFamily (address : ℕ) : ℕ := (Nat.unpair address).1

/-- The copy index of an address. -/
def addrCopy (address : ℕ) : ℕ := (Nat.unpair (Nat.unpair address).2).1

/-- The first payload field of an address. -/
def addrFst (address : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair address).2).2).1

/-- The second payload field of an address. -/
def addrSnd (address : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair address).2).2).2

@[simp] theorem addrFamily_pair (a b : ℕ) : addrFamily (Nat.pair a b) = a := by
  simp [addrFamily]

@[simp] theorem addrCopy_pair (a i u v : ℕ) :
    addrCopy (Nat.pair a (Nat.pair i (Nat.pair u v))) = i := by
  simp [addrCopy]

@[simp] theorem addrFst_pair (a i u v : ℕ) :
    addrFst (Nat.pair a (Nat.pair i (Nat.pair u v))) = u := by
  simp [addrFst]

@[simp] theorem addrSnd_pair (a i u v : ℕ) :
    addrSnd (Nat.pair a (Nat.pair i (Nat.pair u v))) = v := by
  simp [addrSnd]

theorem primrec_addrFamily : Primrec addrFamily :=
  (Primrec.fst.comp Primrec.unpair).of_eq fun _ => rfl

theorem primrec_addrCopy : Primrec addrCopy :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).of_eq
    fun _ => rfl

theorem primrec_addrFst : Primrec addrFst :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).of_eq fun _ => rfl

theorem primrec_addrSnd : Primrec addrSnd :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).of_eq fun _ => rfl

/-- The pairing function is primitive recursive.  Proved from its definition, so
that the enumerator below needs nothing else about the alphabet coding. -/
theorem primrec_natPair : Primrec fun p : ℕ × ℕ => Nat.pair p.1 p.2 := by
  have h : Primrec fun p : ℕ × ℕ =>
      if p.1 < p.2 then p.2 * p.2 + p.1 else p.1 * p.1 + p.1 + p.2 :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.snd Primrec.snd)
        Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.fst Primrec.fst)
          Primrec.fst)
        Primrec.snd)
  exact h.of_eq fun _ => by simp only [Nat.pair]

theorem primrec_copyRaw : Primrec fun p : ℕ × RawWord => copyRaw p.1 p.2 := by
  have hletter : Primrec fun q : (ℕ × RawWord) × (ℕ × Bool) =>
      ((Nat.pair q.1.1 q.2.1 : ℕ), q.2.2) :=
    Primrec.pair
      (primrec_natPair.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map Primrec.snd hletter.to₂).of_eq fun _ => rfl

theorem primrec_killRaw : Primrec fun p : ℕ × ℕ => killRaw p.1 p.2 :=
  (Primrec.list_cons.comp (Primrec.pair primrec_natPair (Primrec.const true))
    (Primrec.const ([] : RawWord))).of_eq fun _ => rfl

/-- **`lem:switch`, the relators.**  "As relators all words of `T` rewritten in
each copy `Y_i`, together with every generator `y_{i,ℓ}` for which
`i ≤ |W_e|`."  Failures of the two searches contribute the empty word, whose
value is the identity relator. -/
def rawSwitchRelator (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) : RawWord :=
  if addrFamily address % 2 = 0 then
    (if seedSearch hDiamond
        (EnumeratedPresentationCodes.decodeRawWord (addrFst address))
        (addrSnd address) = true then
      copyRaw (addrCopy address)
        (EnumeratedPresentationCodes.decodeRawWord (addrFst address))
    else [])
  else
    (if addrCopy address < eventCount c (addrSnd address) then
      killRaw (addrCopy address) (addrFst address)
    else [])

theorem rawSwitchRelator_copy (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) (hfam : addrFamily address % 2 = 0)
    (hsr : seedSearch hDiamond
      (EnumeratedPresentationCodes.decodeRawWord (addrFst address))
      (addrSnd address) = true) :
    rawSwitchRelator hDiamond c address =
      copyRaw (addrCopy address)
        (EnumeratedPresentationCodes.decodeRawWord (addrFst address)) := by
  simp only [rawSwitchRelator, if_pos hfam, if_pos hsr]

theorem rawSwitchRelator_copy_nil (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) (hfam : addrFamily address % 2 = 0)
    (hsr : ¬ seedSearch hDiamond
      (EnumeratedPresentationCodes.decodeRawWord (addrFst address))
      (addrSnd address) = true) :
    rawSwitchRelator hDiamond c address = [] := by
  simp only [rawSwitchRelator, if_pos hfam, if_neg hsr]

theorem rawSwitchRelator_kill (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) (hfam : ¬ addrFamily address % 2 = 0)
    (hlt : addrCopy address < eventCount c (addrSnd address)) :
    rawSwitchRelator hDiamond c address =
      killRaw (addrCopy address) (addrFst address) := by
  simp only [rawSwitchRelator, if_neg hfam, if_pos hlt]

theorem rawSwitchRelator_kill_nil (hDiamond : DiamondLemmaWordProblem) (c : Code)
    (address : ℕ) (hfam : ¬ addrFamily address % 2 = 0)
    (hlt : ¬ addrCopy address < eventCount c (addrSnd address)) :
    rawSwitchRelator hDiamond c address = [] := by
  simp only [rawSwitchRelator, if_neg hfam, if_neg hlt]

/-- **`lem:switch`.**  "The last family is recursively enumerable uniformly in
`e`."  In fact the whole relator enumerator is primitive recursive uniformly in
`e`, since the seed search is. -/
theorem primrec_rawSwitchRelator (hDiamond : DiamondLemmaWordProblem) :
    Primrec fun z : Code × ℕ => rawSwitchRelator hDiamond z.1 z.2 := by
  have haddr : Primrec fun z : Code × ℕ => z.2 := Primrec.snd
  have hfam : Primrec fun z : Code × ℕ => addrFamily z.2 % 2 :=
    Primrec.nat_mod.comp (primrec_addrFamily.comp haddr) (Primrec.const 2)
  have hidx : Primrec fun z : Code × ℕ => addrCopy z.2 :=
    primrec_addrCopy.comp haddr
  have hfst : Primrec fun z : Code × ℕ => addrFst z.2 :=
    primrec_addrFst.comp haddr
  have hsnd : Primrec fun z : Code × ℕ => addrSnd z.2 :=
    primrec_addrSnd.comp haddr
  have hword : Primrec fun z : Code × ℕ =>
      EnumeratedPresentationCodes.decodeRawWord (addrFst z.2) :=
    EnumeratedPresentationCodes.primrec_decodeRawWord.comp hfst
  have hsearch : Primrec fun z : Code × ℕ =>
      seedSearch hDiamond
        (EnumeratedPresentationCodes.decodeRawWord (addrFst z.2))
        (addrSnd z.2) :=
    (primrec₂_seedSearch hDiamond).comp hword hsnd
  have hcopy : Primrec fun z : Code × ℕ =>
      copyRaw (addrCopy z.2)
        (EnumeratedPresentationCodes.decodeRawWord (addrFst z.2)) :=
    primrec_copyRaw.comp (Primrec.pair hidx hword)
  have hkill : Primrec fun z : Code × ℕ =>
      killRaw (addrCopy z.2) (addrFst z.2) :=
    primrec_killRaw.comp (Primrec.pair hidx hfst)
  have hcount : Primrec fun z : Code × ℕ => eventCount z.1 (addrSnd z.2) :=
    primrec_eventCount.comp (Primrec.pair Primrec.fst hsnd)
  have hbranchCopy : Primrec fun z : Code × ℕ =>
      (if seedSearch hDiamond
          (EnumeratedPresentationCodes.decodeRawWord (addrFst z.2))
          (addrSnd z.2) = true then
        copyRaw (addrCopy z.2)
          (EnumeratedPresentationCodes.decodeRawWord (addrFst z.2))
      else ([] : RawWord)) :=
    Primrec.ite (Primrec.eq.comp hsearch (Primrec.const true)) hcopy
      (Primrec.const [])
  have hbranchKill : Primrec fun z : Code × ℕ =>
      (if addrCopy z.2 < eventCount z.1 (addrSnd z.2) then
        killRaw (addrCopy z.2) (addrFst z.2)
      else ([] : RawWord)) :=
    Primrec.ite (Primrec.nat_lt.comp hidx hcount) hkill (Primrec.const [])
  exact (Primrec.ite (Primrec.eq.comp hfam (Primrec.const 0))
    hbranchCopy hbranchKill).of_eq fun _ => rfl

end

end LeavittSwitch
end MFRecognition
end Manuscript
end GroupApproximation
