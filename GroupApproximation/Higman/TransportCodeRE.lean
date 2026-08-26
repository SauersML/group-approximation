import GroupApproximation.Higman.TransportFive
import GroupApproximation.Higman.HigmanCodingDictionary
import GroupApproximation.Higman.IntPrimrec

/-!
# The recursively enumerable code set in Higman's Section 5

This file closes the purely computability-theoretic `Transport.CodeRE` leaf.
The point requiring care is that `seqOfList` is not injective: an arbitrary
list code must be compared with the canonical block code by summing all
entries at each coordinate mentioned by either list.
-/

namespace GroupApproximation
namespace Higman
namespace Transport

/-! ## 1. A primitive-recursive canonical list code -/

/-- One entry of the canonical list spelling of `codeSeq`.  Its coordinate is
computed in `Nat` and cast once, avoiding integer multiplication in the
computability proof. -/
def codeEntry (n k : ℕ) (x : ℕ × Bool) : ℤ × ℤ :=
  (((k * (n + 1) + x.1 % (n + 1) : ℕ) : ℤ),
    bif x.2 then (1 : ℤ) else (-1 : ℤ))

theorem codeEntry_eq (n k i : ℕ) (s : Bool) :
    codeEntry n k (i, s) =
      (pos n k i, if s then (1 : ℤ) else (-1 : ℤ)) := by
  apply Prod.ext
  · simp [codeEntry, pos]
  · cases s <;> rfl

/-- The canonical list code, starting at block `k`. -/
def codeListFrom (n : ℕ) : RawWord → ℕ → List (ℤ × ℤ)
  | [], _ => []
  | x :: v, k => codeEntry n k x :: codeListFrom n v (k + 1)

/-- The canonical list code starting at block zero. -/
def codeList (n : ℕ) (v : RawWord) : List (ℤ × ℤ) := codeListFrom n v 0

theorem seqOfList_cons (p : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    seqOfList (p :: l) = Finsupp.single p.1 p.2 + seqOfList l := by
  simp [seqOfList]

/-- The canonical list denotes exactly the recursively defined block code. -/
theorem seqOfList_codeListFrom (n : ℕ) :
    ∀ (v : RawWord) (k : ℕ),
      seqOfList (codeListFrom n v k) = codeSeq n v k := by
  intro v
  induction v with
  | nil =>
      intro k
      simp [codeListFrom, seqOfList]
  | cons x v ih =>
      obtain ⟨i, s⟩ := x
      intro k
      rw [codeListFrom, seqOfList_cons, codeEntry_eq, ih (k + 1)]
      rfl

theorem seqOfList_codeList (n : ℕ) (v : RawWord) :
    seqOfList (codeList n v) = codeSeq n v 0 := by
  exact seqOfList_codeListFrom n v 0

/-- The reverse-fold state used to certify primitive recursiveness of
`codeListFrom`. -/
def codeListFoldState (n : ℕ) (z : RawWord × ℕ) : ℕ × List (ℤ × ℤ) :=
  z.1.reverse.foldr
    (fun x acc => (acc.1 + 1, codeEntry n acc.1 x :: acc.2))
    (z.2, [])

private theorem codeListFoldState_aux (n : ℕ) (v : RawWord) (k : ℕ)
    (L : List (ℤ × ℤ)) :
    v.reverse.foldr
        (fun x acc => (acc.1 + 1, codeEntry n acc.1 x :: acc.2))
        (k, L)
      = (k + v.length, (codeListFrom n v k).reverse ++ L) := by
  induction v generalizing k L with
  | nil => simp [codeListFrom]
  | cons x v ih =>
      simp only [List.reverse_cons, List.foldr_append, List.foldr_cons,
        List.foldr_nil]
      rw [ih]
      simp [codeListFrom, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

theorem codeListFoldState_eq (n : ℕ) (v : RawWord) (k : ℕ) :
    codeListFoldState n (v, k) =
      (k + v.length, (codeListFrom n v k).reverse) := by
  simpa [codeListFoldState] using codeListFoldState_aux n v k []

theorem primrec_codeEntry (n : ℕ) :
    Primrec (fun z : ℕ × (ℕ × Bool) => codeEntry n z.1 z.2) := by
  have hcoordNat : Primrec fun z : ℕ × (ℕ × Bool) =>
      z.1 * (n + 1) + z.2.1 % (n + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const (n + 1)))
      (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.const (n + 1)))
  have hcoord : Primrec fun z : ℕ × (ℕ × Bool) =>
      ((z.1 * (n + 1) + z.2.1 % (n + 1) : ℕ) : ℤ) :=
    primrec_int_natCast.comp hcoordNat
  have hsign : Primrec fun z : ℕ × (ℕ × Bool) =>
      bif z.2.2 then (1 : ℤ) else (-1 : ℤ) :=
    Primrec.cond (Primrec.snd.comp Primrec.snd)
      (Primrec.const (1 : ℤ)) (Primrec.const (-1 : ℤ))
  exact Primrec.pair hcoord hsign

theorem primrec_codeListFoldState (n : ℕ) : Primrec (codeListFoldState n) := by
  have hlist : Primrec fun z : RawWord × ℕ => z.1.reverse :=
    Primrec.list_reverse.comp Primrec.fst
  have hbase : Primrec fun z : RawWord × ℕ =>
      (z.2, ([] : List (ℤ × ℤ))) :=
    Primrec.pair Primrec.snd (Primrec.const [])
  have hk : Primrec fun z : (RawWord × ℕ) ×
      ((ℕ × Bool) × (ℕ × List (ℤ × ℤ))) => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec fun z : (RawWord × ℕ) ×
      ((ℕ × Bool) × (ℕ × List (ℤ × ℤ))) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hL : Primrec fun z : (RawWord × ℕ) ×
      ((ℕ × Bool) × (ℕ × List (ℤ × ℤ))) => z.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hentry : Primrec fun z : (RawWord × ℕ) ×
      ((ℕ × Bool) × (ℕ × List (ℤ × ℤ))) => codeEntry n z.2.2.1 z.2.1 :=
    (primrec_codeEntry n).comp (Primrec.pair hk hx)
  have hstep : Primrec₂ fun (_ : RawWord × ℕ)
      (p : (ℕ × Bool) × (ℕ × List (ℤ × ℤ))) =>
        (p.2.1 + 1, codeEntry n p.2.1 p.1 :: p.2.2) :=
    Primrec.pair
      (Primrec.nat_add.comp hk (Primrec.const 1))
      (Primrec.list_cons.comp hentry hL)
  exact Primrec.list_foldr hlist hbase hstep

/-- The canonical code is primitive recursive for each fixed alphabet size. -/
theorem primrec_codeList (n : ℕ) : Primrec (codeList n) := by
  have hstate : Primrec fun v : RawWord => codeListFoldState n (v, 0) :=
    (primrec_codeListFoldState n).comp
      (Primrec.pair Primrec.id (Primrec.const 0))
  have hout : Primrec fun v : RawWord => (codeListFoldState n (v, 0)).2.reverse :=
    Primrec.list_reverse.comp (Primrec.snd.comp hstate)
  refine hout.of_eq fun v => ?_
  rw [codeListFoldState_eq]
  simp [codeList]

/-! ## 2. Equality of arbitrary list codes -/

/-- Compare the coordinate sums at every index mentioned by either code. -/
def sameSeqCode (l m : List (ℤ × ℤ)) : Bool :=
  (l ++ m).all fun p => decide (Seq.evalCode l p.1 = Seq.evalCode m p.1)

theorem sameSeqCode_eq_true_iff (l m : List (ℤ × ℤ)) :
    sameSeqCode l m = true ↔ seqOfList l = seqOfList m := by
  constructor
  · intro h
    change (l ++ m).all (fun p =>
      decide (Seq.evalCode l p.1 = Seq.evalCode m p.1)) = true at h
    apply Finsupp.ext
    intro j
    rw [Seq.seqOfList_apply, Seq.seqOfList_apply]
    by_cases hj : ∃ p ∈ l ++ m, p.1 = j
    · obtain ⟨p, hp, rfl⟩ := hj
      have hp' := (List.all_eq_true.mp h) p hp
      exact (decide_eq_true_iff.mp hp')
    · have hl : ∀ p ∈ l, p.1 ≠ j := by
        intro p hp heq
        exact hj ⟨p, List.mem_append_left m hp, heq⟩
      have hm : ∀ p ∈ m, p.1 ≠ j := by
        intro p hp heq
        exact hj ⟨p, List.mem_append_right l hp, heq⟩
      rw [Seq.evalCode_eq_zero_of_not_mem hl,
        Seq.evalCode_eq_zero_of_not_mem hm]
  · intro h
    change (l ++ m).all (fun p =>
      decide (Seq.evalCode l p.1 = Seq.evalCode m p.1)) = true
    apply List.all_eq_true.mpr
    intro p hp
    rw [decide_eq_true_iff]
    have hp' := congrArg (fun f : Seq.E => f p.1) h
    simpa only [Seq.seqOfList_apply] using hp'

theorem primrec_sameSeqCode : Primrec₂ sameSeqCode := by
  have hcodes : Primrec fun z : List (ℤ × ℤ) × List (ℤ × ℤ) => z.1 ++ z.2 :=
    Primrec.list_append.comp Primrec.fst Primrec.snd
  have hev := Seq.primrec_evalCode primrec2_int_add
  have htest : Primrec fun z :
      (List (ℤ × ℤ) × List (ℤ × ℤ)) × (ℤ × ℤ) =>
        decide (Seq.evalCode z.1.1 z.2.1 = Seq.evalCode z.1.2 z.2.1) :=
    (PrimrecRel.comp Primrec.eq
      (hev.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (hev.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))).decide
  have hmap : Primrec fun z : List (ℤ × ℤ) × List (ℤ × ℤ) =>
      (z.1 ++ z.2).map fun p =>
        decide (Seq.evalCode z.1 p.1 = Seq.evalCode z.2 p.1) :=
    Primrec.list_map hcodes htest
  have hfold := Primrec.list_foldr hmap (Primrec.const true)
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
  exact hfold.of_eq fun z => (Seq.list_all_eq_foldr _ _).symm

/-! ## 3. The search predicate and `CodeRE` -/

/-- The finite certificate checker: a word-membership search witness together
with equality of the arbitrary input code and the canonical block code. -/
def codeCheck (n : ℕ) (F : RawWord → ℕ → Bool)
    (l : List (ℤ × ℤ)) (q : RawWord × ℕ) : Bool :=
  F q.1 q.2 && sameSeqCode l (codeList n q.1)

theorem primrec_codeCheck (n : ℕ) {F : RawWord → ℕ → Bool}
    (hF : Primrec₂ F) : Primrec₂ (codeCheck n F) := by
  have hleft : Primrec fun z : List (ℤ × ℤ) × (RawWord × ℕ) =>
      F z.2.1 z.2.2 :=
    hF.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hright : Primrec fun z : List (ℤ × ℤ) × (RawWord × ℕ) =>
      sameSeqCode z.1 (codeList n z.2.1) :=
    primrec_sameSeqCode.comp Primrec.fst
      ((primrec_codeList n).comp (Primrec.fst.comp Primrec.snd))
  exact Primrec.and.comp hleft hright

theorem exists_codeCheck_iff (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1))))
    {F : RawWord → ℕ → Bool}
    (hFspec : ∀ v, rawToFree n v ∈ N ↔ ∃ t, F v t = true)
    (l : List (ℤ × ℤ)) :
    (∃ q : RawWord × ℕ, codeCheck n F l q = true) ↔
      seqOfList l ∈ codeSet n N := by
  constructor
  · rintro ⟨⟨v, t⟩, h⟩
    rw [codeCheck, Bool.and_eq_true] at h
    refine ⟨v, (hFspec v).mpr ⟨t, h.1⟩, ?_⟩
    exact (sameSeqCode_eq_true_iff _ _).mp h.2 |>.trans
      (seqOfList_codeList n v)
  · rintro ⟨v, hv, hseq⟩
    obtain ⟨t, ht⟩ := (hFspec v).mp hv
    refine ⟨(v, t), ?_⟩
    rw [codeCheck, Bool.and_eq_true]
    refine ⟨ht, (sameSeqCode_eq_true_iff _ _).mpr ?_⟩
    exact hseq.trans (seqOfList_codeList n v).symm

/-- **Higman's Section 5, computability leaf.**  Code sets of recursively
enumerable subgroups are recursively enumerable. -/
def codeRE : CodeRE where
  code_re := by
    intro n N hre
    obtain ⟨F, hF, hFspec⟩ := exists_primrec_of_rePred hre
    have hsearch : REPred fun l : List (ℤ × ℤ) =>
        ∃ q : RawWord × ℕ, codeCheck n F l q = true :=
      WordProblemRE.rePred_exists_eq_true (primrec_codeCheck n hF).to_comp
    exact hsearch.of_eq fun l => exists_codeCheck_iff n N hFspec l

end Transport
end Higman
end GroupApproximation
