import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.WordVec
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.PolyOps
import GroupApproximation.Computability.RawTransformPrimrec

/-!
# The polynomial encodings of entries and word vectors are primitive recursive

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding `thm:mf-arithmetic`:
the sentence `Φ(P,n,c)` is produced from `(P, n, c)` by an algorithm.  This file proves
the building blocks of `Encoding/Vars.lean`, `Encoding/CPoly.lean` and
`Encoding/WordVec.lean` primitive recursive: variable indices and blocks, the complex
operations on pairs of integer polynomials, finite sums, norm quadratic forms, the entries
of the matrix of a letter, and the action of a word on a vector of polynomials.  Each
operation taking a function argument gets a parametric statement over a context `α`.
The operations on `MvP` are those of `Computability/PolyOps.lean`.
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes

variable {α : Type*} [Primcodable α]

/-! ## Variables -/

/-- `varExp i` is the `i`-fold prepending of `0` to `[1]`. -/
theorem enc_varExp_eq_iterate : ∀ i : ℕ, varExp i = (List.cons 0)^[i] [1]
  | 0 => rfl
  | i + 1 => (congrArg (List.cons 0) (enc_varExp_eq_iterate i)).trans
      (Function.iterate_succ_apply' (List.cons 0) i [1]).symm

theorem enc_primrec_varExp : Primrec varExp :=
  (Primrec.nat_iterate (f := fun i : ℕ => i) (g := fun _ : ℕ => ([1] : List ℕ))
    (h := fun (_ : ℕ) (l : List ℕ) => 0 :: l) Primrec.id (Primrec.const [1])
    (Primrec.list_cons.comp (Primrec.const 0)
      (Primrec.snd (α := ℕ) (β := List ℕ))).to₂).of_eq fun i =>
    (enc_varExp_eq_iterate i).symm

theorem enc_primrec_mvVar : Primrec mvVar :=
  (Primrec.list_cons.comp (Primrec.pair (Primrec.const (1 : ℤ)) enc_primrec_varExp)
    (Primrec.const ([] : MvP))).of_eq fun _ => rfl

theorem enc_primrec_encIdx {tag a b c p : α → ℕ} (ht : Primrec tag) (ha : Primrec a)
    (hb : Primrec b) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => encIdx (tag x) (a x) (b x) (c x) (p x) :=
  (Primrec₂.natPair.comp ht (Primrec₂.natPair.comp ha (Primrec₂.natPair.comp hb
    (Primrec₂.natPair.comp hc hp)))).of_eq fun _ => rfl

theorem enc_primrec_encBlock (tag : ℕ) {A B C : α → ℕ} (hA : Primrec A) (hB : Primrec B)
    (hC : Primrec C) : Primrec fun x => encBlock tag (A x) (B x) (C x) := by
  have h4 : Primrec₂ fun (y : ((α × ℕ) × ℕ) × ℕ) (p : ℕ) => encIdx tag y.1.1.2 y.1.2 y.2 p :=
    enc_primrec_encIdx (Primrec.const tag)
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
      Primrec.snd
  have h3 : Primrec₂ fun (y : (α × ℕ) × ℕ) (c : ℕ) =>
      (List.range 2).map fun p => encIdx tag y.1.2 y.2 c p :=
    Primrec.list_map (Primrec.const (List.range 2)) h4
  have h2 : Primrec₂ fun (y : α × ℕ) (b : ℕ) =>
      (List.range (C y.1)).flatMap fun c => (List.range 2).map fun p => encIdx tag y.2 b c p :=
    Primrec.list_flatMap (Primrec.list_range.comp (hC.comp (Primrec.fst.comp Primrec.fst))) h3
  have h1 : Primrec₂ fun (x : α) (a : ℕ) =>
      (List.range (B x)).flatMap fun b => (List.range (C x)).flatMap fun c =>
        (List.range 2).map fun p => encIdx tag a b c p :=
    Primrec.list_flatMap (Primrec.list_range.comp (hB.comp Primrec.fst)) h2
  exact (Primrec.list_flatMap (Primrec.list_range.comp hA) h1).of_eq fun _ => rfl

/-! ## Complex polynomials -/

theorem enc_primrec_cpAdd : Primrec₂ cpAdd := by
  show Primrec fun q : CP × CP => cpAdd q.1 q.2
  exact (Primrec.pair
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

theorem enc_primrec_cpNeg : Primrec cpNeg :=
  (Primrec.pair (PR.primrec_mvNeg.comp Primrec.fst)
    (PR.primrec_mvNeg.comp Primrec.snd)).of_eq fun _ => rfl

theorem enc_primrec_cpConj : Primrec cpConj :=
  (Primrec.pair Primrec.fst (PR.primrec_mvNeg.comp Primrec.snd)).of_eq fun _ => rfl

theorem enc_primrec_cpMul : Primrec₂ cpMul := by
  show Primrec fun q : CP × CP => cpMul q.1 q.2
  exact (Primrec.pair
    (Primrec.list_append.comp
      (PR.primrec_mvMul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (PR.primrec_mvNeg.comp
        (PR.primrec_mvMul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))
    (Primrec.list_append.comp
      (PR.primrec_mvMul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (PR.primrec_mvMul.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)))).of_eq fun _ => rfl

theorem enc_primrec_cpSumRange {d : α → ℕ} {f : α → ℕ → CP} (hd : Primrec d)
    (hf : Primrec₂ f) : Primrec fun x => cpSumRange (d x) (f x) := by
  have h1 : Primrec₂ fun (x : α) (s : ℕ) => (f x s).1 := Primrec.fst.comp₂ hf
  have h2 : Primrec₂ fun (x : α) (s : ℕ) => (f x s).2 := Primrec.snd.comp₂ hf
  exact (Primrec.pair (Primrec.list_flatMap (Primrec.list_range.comp hd) h1)
    (Primrec.list_flatMap (Primrec.list_range.comp hd) h2)).of_eq fun _ => rfl

theorem enc_primrec_encNormSq {d : α → ℕ} {f : α → ℕ → CP} (hd : Primrec d)
    (hf : Primrec₂ f) : Primrec fun x => encNormSq (d x) (f x) := by
  have h1 : Primrec₂ fun (x : α) (r : ℕ) => (f x r).1 := Primrec.fst.comp₂ hf
  have h2 : Primrec₂ fun (x : α) (r : ℕ) => (f x r).2 := Primrec.snd.comp₂ hf
  have h : Primrec₂ fun (x : α) (r : ℕ) =>
      mvMul (f x r).1 (f x r).1 ++ mvMul (f x r).2 (f x r).2 :=
    Primrec.list_append.comp₂ (PR.primrec_mvMul.comp₂ h1 h1) (PR.primrec_mvMul.comp₂ h2 h2)
  exact (Primrec.list_flatMap (Primrec.list_range.comp hd) h).of_eq fun _ => rfl

/-! ## Letters and words acting on vectors -/

theorem enc_primrec_encGEntry {g r s : α → ℕ} (hg : Primrec g) (hr : Primrec r)
    (hs : Primrec s) : Primrec fun x => encGEntry (g x) (r x) (s x) :=
  (Primrec.pair
    (enc_primrec_mvVar.comp (enc_primrec_encIdx (Primrec.const 0) hg hr hs (Primrec.const 0)))
    (enc_primrec_mvVar.comp
      (enc_primrec_encIdx (Primrec.const 0) hg hr hs (Primrec.const 1)))).of_eq fun _ => rfl

theorem enc_primrec_encLetterEntry {P : α → PresentationCode} {a : α → ℕ × Bool}
    {r s : α → ℕ} (hP : Primrec P) (ha : Primrec a) (hr : Primrec r) (hs : Primrec s) :
    Primrec fun x => encLetterEntry (P x) (a x) (r x) (s x) := by
  have hi : Primrec fun x => (a x).1 % genCount (P x) :=
    Primrec.nat_mod.comp (Primrec.fst.comp ha) (RawTransformPrimrec.primrec_genCount.comp hP)
  exact (Primrec.cond (Primrec.snd.comp ha) (enc_primrec_encGEntry hi hr hs)
    (enc_primrec_cpConj.comp (enc_primrec_encGEntry hi hs hr))).of_eq fun _ => rfl

theorem enc_primrec_encApplyLetter {P : α → PresentationCode} {d : α → ℕ}
    {a : α → ℕ × Bool} {v : α → List CP} (hP : Primrec P) (hd : Primrec d) (ha : Primrec a)
    (hv : Primrec v) : Primrec fun x => encApplyLetter (P x) (d x) (a x) (v x) := by
  have hs : Primrec₂ fun (y : α × ℕ) (s : ℕ) =>
      cpMul (encLetterEntry (P y.1) (a y.1) y.2 s) ((v y.1).getD s cpZero) :=
    enc_primrec_cpMul.comp
      (enc_primrec_encLetterEntry (hP.comp (Primrec.fst.comp Primrec.fst))
        (ha.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD cpZero).comp (hv.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have hx : Primrec₂ fun (x : α) (y : ℕ) => cpSumRange (d x) fun s =>
      cpMul (encLetterEntry (P x) (a x) y s) ((v x).getD s cpZero) :=
    enc_primrec_cpSumRange (hd.comp Primrec.fst) hs
  exact (Primrec.list_map (Primrec.list_range.comp hd) hx).of_eq fun _ => rfl

theorem enc_primrec_encWordVec {P : α → PresentationCode} {d : α → ℕ}
    {w : α → List (ℕ × Bool)} {v : α → List CP} (hP : Primrec P) (hd : Primrec d)
    (hw : Primrec w) (hv : Primrec v) :
    Primrec fun x => encWordVec (P x) (d x) (w x) (v x) := by
  have h : Primrec₂ fun (x : α) (q : (ℕ × Bool) × List CP) =>
      encApplyLetter (P x) (d x) q.1 q.2 :=
    enc_primrec_encApplyLetter (hP.comp Primrec.fst) (hd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hw hv h).of_eq fun _ => rfl

theorem enc_primrec_encVecOf (tag : ℕ) {t d : α → ℕ} (ht : Primrec t) (hd : Primrec d) :
    Primrec fun x => encVecOf tag (t x) (d x) := by
  have h : Primrec₂ fun (x : α) (r : ℕ) =>
      (mvVar (encIdx tag (t x) r 0 0), mvVar (encIdx tag (t x) r 0 1)) :=
    Primrec.pair
      (enc_primrec_mvVar.comp (enc_primrec_encIdx (Primrec.const tag) (ht.comp Primrec.fst)
        Primrec.snd (Primrec.const 0) (Primrec.const 0)))
      (enc_primrec_mvVar.comp (enc_primrec_encIdx (Primrec.const tag) (ht.comp Primrec.fst)
        Primrec.snd (Primrec.const 0) (Primrec.const 1)))
  exact (Primrec.list_map (Primrec.list_range.comp hd) h).of_eq fun _ => rfl

end GroupApproximation.Full.NN11b
