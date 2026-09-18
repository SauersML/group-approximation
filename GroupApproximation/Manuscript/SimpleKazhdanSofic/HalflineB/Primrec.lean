import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Decide
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblemPrimrec
import Mathlib.Computability.Primrec.List
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): the table check is primitive recursive

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b), tex l.664–665 (sentence dfa561ecfaa5):

> So the word problem of G_Δ is Turing reducible to that of Δ.

## Proof route

* The oracle answers are a list `ans` of `0/1` values for the list `Q` of the codes of the words `w⁻¹ ++ w'` asked.
  `look (Q, ans) w w'` looks up the answer for `w⁻¹ w'` (`lookL`), and so stands for "`ξ_w = ξ_{w'}` in `Λ`".
* The Boolean folds `anyB`, `allB`, `parB`, the atoms, cylinders, coefficients and the table and matrix checks of
  `HalflineB.Decide` are primitive recursive in the answers (`primrec_atomB`, …, `primrec_matOk`).
* The table products and the matrix `hWordMat L w` of a word `w` are primitive recursive in `w`
  (`primrec_hMatMul`, `primrec_hWordMat`).
* So the queries `hostQ L n` (the codes of all pairs of words of the tables of the word coded by `n`) and the
  decision `hostD L n ans` are primitive recursive (`primrec_hostQ`, `primrec_hostD`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter
open Encodable

/-! ### Boolean folds -/

theorem primrec_anyB {α : Type*} [Primcodable α] {β : Type} [Primcodable β] {l : α → List β}
    {f : α → β → Bool} (hl : Primrec l) (hf : Primrec₂ f) : Primrec fun a => anyB (l a) (f a) := by
  have hh : Primrec₂ fun (a : α) (p : β × Bool) => f a p.1 || p.2 :=
    (Primrec.or.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hl (Primrec.const false) hh).of_eq fun _ => rfl

theorem primrec_allB {α : Type*} [Primcodable α] {β : Type} [Primcodable β] {l : α → List β}
    {f : α → β → Bool} (hl : Primrec l) (hf : Primrec₂ f) : Primrec fun a => allB (l a) (f a) := by
  have hh : Primrec₂ fun (a : α) (p : β × Bool) => f a p.1 && p.2 :=
    (Primrec.and.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hl (Primrec.const true) hh).of_eq fun _ => rfl

theorem primrec_bxor : Primrec₂ bxor :=
  Primrec.dom_bool₂ bxor

theorem primrec_parB {α : Type*} [Primcodable α] {β : Type} [Primcodable β] {l : α → List β}
    {f : α → β → Bool} (hl : Primrec l) (hf : Primrec₂ f) : Primrec fun a => parB (l a) (f a) := by
  have hh : Primrec₂ fun (a : α) (p : β × Bool) => bxor (f a p.1) p.2 :=
    (primrec_bxor.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hl (Primrec.const false) hh).of_eq fun _ => rfl

/-! ### Looking up the answers -/

/-- The answer recorded for the query `n`: whether some position `k` has `Q[k] = n` and `ans[k] = 1`. -/
def lookL (Q ans : List ℕ) (n : ℕ) : Bool :=
  anyB (List.range Q.length) fun k => decide (Q.getD k 0 = n) && decide (ans.getD k 0 = 1)

/-- The answer for "`ξ_x = ξ_y` in `Λ`": the recorded answer for the word `x⁻¹ y`. -/
def look {ι : Type} [Primcodable ι] (c : List ℕ × List ℕ) (x y : LW ι) : Bool :=
  lookL c.1 c.2 (encode (wordInv x ++ y))

theorem primrec_lookL {α : Type*} [Primcodable α] {Q ans : α → List ℕ} {n : α → ℕ} (hQ : Primrec Q)
    (hans : Primrec ans) (hn : Primrec n) : Primrec fun a => lookL (Q a) (ans a) (n a) := by
  have hf : Primrec₂ fun (a : α) (k : ℕ) => decide ((Q a).getD k 0 = n a) && decide ((ans a).getD k 0 = 1) :=
    (Primrec.and.comp
      ((Primrec.eq (α := ℕ)).decide.comp ((Primrec.list_getD 0).comp (hQ.comp Primrec.fst) Primrec.snd)
        (hn.comp Primrec.fst))
      ((Primrec.eq (α := ℕ)).decide.comp ((Primrec.list_getD 0).comp (hans.comp Primrec.fst) Primrec.snd)
        (Primrec.const 1))).to₂
  exact (primrec_anyB (Primrec.list_range.comp (Primrec.list_length.comp hQ)) hf).of_eq fun _ => rfl

theorem primrec_look {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] {c : α → List ℕ × List ℕ}
    {x y : α → LW ι} (hc : Primrec c) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => look (c a) (x a) (y a) :=
  (primrec_lookL (Primrec.fst.comp hc) (Primrec.snd.comp hc)
    (Primrec.encode.comp
      (Primrec.list_append.comp ((primrec_wordInv (ι := Option ι)).comp hx) hy))).of_eq fun _ => rfl

/-! ### Words and subsets -/

theorem liftD_eq_map {ι : Type} (v : List (ι × Bool)) : liftD v = v.map fun x => (some x.1, x.2) := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    obtain ⟨i, b⟩ := x
    simp only [liftD, List.map_cons, ih]

theorem primrec_liftD {ι : Type} [Primcodable ι] : Primrec (liftD : List (ι × Bool) → LW ι) :=
  (Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun v => (liftD_eq_map v).symm

theorem primrec_dW {ι : Type} [Primcodable ι] [Finite ι] : Primrec (dW : LW ι → LW ι) :=
  (primrec_liftD.comp (primrec_deltaWord (ι := ι))).of_eq fun _ => rfl

theorem primrec_subsets {β : Type} [Primcodable β] : Primrec (subsets : List β → List (List β)) := by
  have hh : Primrec₂ fun (_ : List β) (p : β × List (List β)) => p.2.flatMap fun B => [B, p.1 :: B] :=
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
          (Primrec.const ([] : List (List β))))).to₂).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([[]] : List (List β))) hh).of_eq fun _ => rfl

/-! ### Atoms, cylinders, coefficients and tables -/

theorem primrec_atomB {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] [Finite ι]
    {c : α → List ℕ × List ℕ} {B : α → List (LW ι)} {p : α → LW ι} (hc : Primrec c) (hB : Primrec B)
    (hp : Primrec p) : Primrec fun a => atomB (look (c a)) (B a) (p a) := by
  have h1 : Primrec₂ fun (a : α) (v : LW ι) => look (c a) (dW v) (dW (p a)) :=
    (primrec_look (hc.comp Primrec.fst) (primrec_dW.comp Primrec.snd)
      (primrec_dW.comp (hp.comp Primrec.fst))).to₂
  have h2 : Primrec₂ fun (a : α) (q : List (ι × Bool)) => look (c a) (liftD q) (dW (p a)) :=
    (primrec_look (hc.comp Primrec.fst) (primrec_liftD.comp Primrec.snd)
      (primrec_dW.comp (hp.comp Primrec.fst))).to₂
  exact (primrec_bxor.comp (primrec_anyB hB h1)
    (primrec_parB ((primrec_lampPrefixes (ι := ι)).comp hp) h2)).of_eq fun _ => rfl

theorem primrec_cylB {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] [Finite ι]
    {c : α → List ℕ × List ℕ} {B P : α → List (LW ι)} (hc : Primrec c) (hB : Primrec B) (hP : Primrec P) :
    Primrec fun a => cylB (look (c a)) (B a) (P a) :=
  (primrec_allB hP
    (primrec_atomB (hc.comp Primrec.fst) (hB.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_coeffB {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] [Finite ι]
    {c : α → List ℕ × List ℕ} {B : α → List (LW ι)} {T : α → HTable ι} {a0 : α → LW ι} (hc : Primrec c)
    (hB : Primrec B) (hT : Primrec T) (ha0 : Primrec a0) :
    Primrec fun a => coeffB (look (c a)) (B a) (T a) (a0 a) := by
  have hf : Primrec₂ fun (a : α) (m : HMono ι) => look (c a) m.1 (a0 a) && cylB (look (c a)) (B a) m.2 :=
    (Primrec.and.comp
      (primrec_look (hc.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (ha0.comp Primrec.fst))
      (primrec_cylB (hc.comp Primrec.fst) (hB.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  exact (primrec_parB hT hf).of_eq fun _ => rfl

theorem primrec_tabU {ι : Type} [Primcodable ι] : Primrec (tabU : HTable ι → List (LW ι)) :=
  (Primrec.list_flatMap Primrec.id (Primrec.snd.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_tabW {ι : Type} [Primcodable ι] [Finite ι] : Primrec (tabW : HTable ι → List (LW ι)) := by
  have h1 : Primrec fun T : HTable ι => T.map fun m => m.1 :=
    Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂
  have h2 : Primrec fun T : HTable ι => (tabU T).map dW :=
    Primrec.list_map primrec_tabU (primrec_dW.comp Primrec.snd).to₂
  have h3 : Primrec fun T : HTable ι => (tabU T).flatMap fun p => (lampPrefixes p).map liftD :=
    Primrec.list_flatMap primrec_tabU
      (Primrec.list_map ((primrec_lampPrefixes (ι := ι)).comp Primrec.snd)
        (primrec_liftD.comp Primrec.snd).to₂).to₂
  exact (Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3).of_eq fun _ => rfl

theorem primrec_tabOk {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] [Finite ι]
    {c : α → List ℕ × List ℕ} {T : α → HTable ι} (hc : Primrec c) (hT : Primrec T) :
    Primrec fun a => tabOk (look (c a)) (T a) := by
  have hinner : Primrec₂ fun (r : α × List (LW ι)) (m0 : HMono ι) =>
      !coeffB (look (c r.1)) r.2 (T r.1) m0.1 :=
    (Primrec.not.comp (primrec_coeffB (hc.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
      (hT.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))).to₂
  have houter : Primrec₂ fun (a : α) (B : List (LW ι)) =>
      allB (T a) fun m0 => !coeffB (look (c a)) B (T a) m0.1 :=
    (primrec_allB (hT.comp Primrec.fst) hinner).to₂
  exact (primrec_allB (primrec_subsets.comp (primrec_tabU.comp hT)) houter).of_eq fun _ => rfl

/-! ### Matrices of tables -/

theorem primrec_matTabs {ι : Type} [Primcodable ι] : Primrec (matTabs : HMat ι → List (HTable ι)) := by
  have hone : Primrec fun p : Fin 3 × Fin 3 => (hMatOne p.1 p.2 : HTable ι) :=
    Primrec.dom_finite _
  have hentry : Primrec fun r : (HMat ι × Fin 3) × Fin 3 => r.1.1 r.1.2 r.2 ++ hMatOne r.1.2 r.2 :=
    Primrec.list_append.comp
      (Primrec.fin_app.comp
        (Primrec.fin_app.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      (hone.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hrow : Primrec₂ fun (M : HMat ι) (i : Fin 3) => (List.finRange 3).map fun j => M i j ++ hMatOne i j :=
    (Primrec.list_map (Primrec.const (List.finRange 3)) hentry.to₂).to₂
  exact (Primrec.list_flatMap (Primrec.const (List.finRange 3)) hrow).of_eq fun _ => rfl

theorem primrec_matOk {α : Type*} [Primcodable α] {ι : Type} [Primcodable ι] [Finite ι]
    {c : α → List ℕ × List ℕ} {Ts : α → List (HTable ι)} (hc : Primrec c) (hTs : Primrec Ts) :
    Primrec fun a => matOk (look (c a)) (Ts a) :=
  (primrec_allB hTs (primrec_tabOk (hc.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_matW {ι : Type} [Primcodable ι] [Finite ι] : Primrec (matW : List (HTable ι) → List (LW ι)) :=
  (Primrec.list_flatMap Primrec.id (primrec_tabW.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_hMonoMul {ι : Type} [Primcodable ι] : Primrec₂ (hMonoMul : HMono ι → HMono ι → HMono ι) := by
  show Primrec fun a : HMono ι × HMono ι => hMonoMul a.1 a.2
  have hmap : Primrec fun a : HMono ι × HMono ι => a.2.2.map fun p => a.1.1 ++ p :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  exact (Primrec.pair
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) hmap)).of_eq fun _ => rfl

theorem primrec_hTabMul {ι : Type} [Primcodable ι] : Primrec₂ (hTabMul : HTable ι → HTable ι → HTable ι) := by
  show Primrec fun a : HTable ι × HTable ι => hTabMul a.1 a.2
  have hrow : Primrec₂ fun (a : HTable ι × HTable ι) (m : HMono ι) => a.2.map (hMonoMul m) :=
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (primrec_hMonoMul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.list_flatMap Primrec.fst hrow).of_eq fun _ => rfl

theorem primrec_hMatMul {ι : Type} [Primcodable ι] : Primrec₂ (hMatMul : HMat ι → HMat ι → HMat ι) := by
  have hM : ∀ k : Fin 3, Primrec fun q : ((HMat ι × HMat ι) × Fin 3) × Fin 3 => q.1.1.1 q.1.2 k := fun k =>
    Primrec.fin_app.comp
      (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
      (Primrec.const k)
  have hN : ∀ k : Fin 3, Primrec fun q : ((HMat ι × HMat ι) × Fin 3) × Fin 3 => q.1.1.2 k q.2 := fun k =>
    Primrec.fin_app.comp
      (Primrec.fin_app.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const k)) Primrec.snd
  have hentry : Primrec fun q : ((HMat ι × HMat ι) × Fin 3) × Fin 3 => hMatMul q.1.1.1 q.1.1.2 q.1.2 q.2 :=
    (Primrec.list_append.comp
      (Primrec.list_append.comp (primrec_hTabMul.comp (hM 0) (hN 0)) (primrec_hTabMul.comp (hM 1) (hN 1)))
      (primrec_hTabMul.comp (hM 2) (hN 2))).of_eq fun _ => rfl
  have h1 : Primrec₂ fun (r : (HMat ι × HMat ι) × Fin 3) (j : Fin 3) => hMatMul r.1.1 r.1.2 r.2 j :=
    hentry
  have h2 : Primrec₂ fun (a : HMat ι × HMat ι) (i : Fin 3) => hMatMul a.1 a.2 i :=
    Primrec.fin_curry.2 h1
  show Primrec fun a : HMat ι × HMat ι => hMatMul a.1 a.2
  exact Primrec.fin_curry.2 h2

theorem primrec_hWordMat {ι : Type} [Primcodable ι] {κ : Type} [Primcodable κ] [Finite κ]
    (L : κ × Bool → HMat ι) : Primrec (hWordMat L) := by
  have hh : Primrec₂ fun (_ : List (κ × Bool)) (p : (κ × Bool) × HMat ι) => hMatMul (L p.1) p.2 :=
    (primrec_hMatMul.comp ((Primrec.dom_finite L).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const (hMatOne : HMat ι)) hh).of_eq fun _ => rfl

/-! ### Queries and decision -/

/-- The codes of the words `a⁻¹ b` for all pairs `a, b` of a list of words. -/
def pairCodes {ι : Type} [Primcodable ι] (W : List (LW ι)) : List ℕ :=
  W.flatMap fun a => W.map fun b => encode (wordInv a ++ b)

/-- The queries for the word coded by `n`: all pairs of words of its tables. -/
def hostQ {ι : Type} [Primcodable ι] {κ : Type} [Primcodable κ] (L : κ × Bool → HMat ι) (n : ℕ) : List ℕ :=
  pairCodes (matW (matTabs (hWordMat L ((decode (α := List (κ × Bool)) n).getD []))))

/-- The decision for the word coded by `n` from the answers `ans` to `hostQ L n`. -/
def hostD {ι : Type} [Primcodable ι] {κ : Type} [Primcodable κ] (L : κ × Bool → HMat ι) (n : ℕ)
    (ans : List ℕ) : ℕ :=
  cond ((decode (α := List (κ × Bool)) n).isSome &&
    matOk (look (hostQ L n, ans)) (matTabs (hWordMat L ((decode (α := List (κ × Bool)) n).getD [])))) 1 0

theorem primrec_pairCodes {ι : Type} [Primcodable ι] : Primrec (pairCodes : List (LW ι) → List ℕ) := by
  have hrow : Primrec₂ fun (W : List (LW ι)) (a : LW ι) => W.map fun b => encode (wordInv a ++ b) :=
    (Primrec.list_map Primrec.fst
      (Primrec.encode.comp (Primrec.list_append.comp
        ((primrec_wordInv (ι := Option ι)).comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂).to₂
  exact (Primrec.list_flatMap Primrec.id hrow).of_eq fun _ => rfl

theorem primrec_hostQ {ι : Type} [Primcodable ι] [Finite ι] {κ : Type} [Primcodable κ] [Finite κ]
    (L : κ × Bool → HMat ι) : Primrec (hostQ L) := by
  have hw : Primrec fun n : ℕ => (decode (α := List (κ × Bool)) n).getD [] :=
    Primrec.option_getD.comp (Primrec.decode (α := List (κ × Bool))) (Primrec.const [])
  exact (primrec_pairCodes.comp (primrec_matW.comp (primrec_matTabs.comp ((primrec_hWordMat L).comp hw)))).of_eq
    fun _ => rfl

theorem primrec_hostD {ι : Type} [Primcodable ι] [Finite ι] {κ : Type} [Primcodable κ] [Finite κ]
    (L : κ × Bool → HMat ι) : Primrec₂ (hostD L) := by
  show Primrec fun a : ℕ × List ℕ => hostD L a.1 a.2
  have hw : Primrec fun a : ℕ × List ℕ => (decode (α := List (κ × Bool)) a.1).getD [] :=
    Primrec.option_getD.comp ((Primrec.decode (α := List (κ × Bool))).comp Primrec.fst) (Primrec.const [])
  have hc : Primrec fun a : ℕ × List ℕ => (decode (α := List (κ × Bool)) a.1).isSome &&
      matOk (look (hostQ L a.1, a.2)) (matTabs (hWordMat L ((decode (α := List (κ × Bool)) a.1).getD []))) :=
    Primrec.and.comp (Primrec.option_isSome.comp ((Primrec.decode (α := List (κ × Bool))).comp Primrec.fst))
      (primrec_matOk (Primrec.pair ((primrec_hostQ L).comp Primrec.fst) Primrec.snd)
        (primrec_matTabs.comp ((primrec_hWordMat L).comp hw)))
  exact (Primrec.cond hc (Primrec.const 1) (Primrec.const 0)).of_eq fun _ => rfl

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.primrec_hostQ
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.primrec_hostD
