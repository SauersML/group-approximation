import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Formula
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.PrimrecPoly
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.PrimrecWords
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.TreeOps

/-!
# The encoding `encodePrenex` is computable

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding `thm:mf-arithmetic`:
the prenex sentence `Φ(P, n, c)` is produced from `(P, n, c)` by an algorithm.  Every
definition of `Encoding/Formula.lean` is a composition of the primitive recursive
operations of `Encoding/PrimrecPoly.lean`, `Encoding/PrimrecWords.lean` and
`Computability/TreeOps.lean`, so `encodePrenex` is primitive recursive
(`primrec_encodePrenex`) and in particular computable (`computable_encodePrenex`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes

variable {α : Type*} [Primcodable α]

/-! ## The constant `-(2^n)^2` -/

/-- Powers of `2` by iterated doubling. -/
theorem enc_two_pow_eq (n : ℕ) : (2 : ℤ) ^ n = (fun z : ℤ => z + z)^[n] 1 := by
  induction n with
  | zero => exact Int.pow_zero _
  | succ n ih =>
    exact (Int.pow_succ (2 : ℤ) n).trans ((mul_two _).trans
      ((congrArg (fun z : ℤ => z + z) ih).trans
        (Function.iterate_succ_apply' (fun z : ℤ => z + z) n 1).symm))

theorem enc_primrec_two_pow : Primrec fun n : ℕ => (2 : ℤ) ^ n :=
  (Primrec.nat_iterate (f := fun n : ℕ => n) (g := fun _ : ℕ => (1 : ℤ))
    (h := fun (_ : ℕ) (z : ℤ) => z + z) Primrec.id (Primrec.const 1)
    (Higman.primrec2_int_add.comp (Primrec.snd (α := ℕ) (β := ℤ))
      (Primrec.snd (α := ℕ) (β := ℤ))).to₂).of_eq fun n => (enc_two_pow_eq n).symm

theorem enc_primrec_negSqTwoPow : Primrec fun n : ℕ => -((2 : ℤ) ^ n) ^ 2 :=
  (Higman.primrec_int_neg.comp (PR.primrec_int_mul.comp enc_primrec_two_pow
    enc_primrec_two_pow)).of_eq fun n =>
    congrArg (fun z : ℤ => -z) (pow_two ((2 : ℤ) ^ n)).symm

/-! ## Unitarity equations -/

theorem enc_primrec_encUnitEntry {d g p q : α → ℕ} (hd : Primrec d) (hg : Primrec g)
    (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => encUnitEntry (d x) (g x) (p x) (q x) := by
  have hl : Primrec₂ fun (x : α) (l : ℕ) =>
      cpMul (cpConj (encGEntry (g x) l (p x))) (encGEntry (g x) l (q x)) :=
    enc_primrec_cpMul.comp
      (enc_primrec_cpConj.comp
        (enc_primrec_encGEntry (hg.comp Primrec.fst) Primrec.snd (hp.comp Primrec.fst)))
      (enc_primrec_encGEntry (hg.comp Primrec.fst) Primrec.snd (hq.comp Primrec.fst))
  have he : Primrec fun x => if p x = q x then cpOfInt (-1) else cpZero :=
    Primrec.ite (Primrec.eq.comp hp hq) (Primrec.const (cpOfInt (-1))) (Primrec.const cpZero)
  exact (enc_primrec_cpAdd.comp (enc_primrec_cpSumRange hd hl) he).of_eq fun _ => rfl

theorem enc_primrec_encUnitEqs {k d : α → ℕ} (hk : Primrec k) (hd : Primrec d) :
    Primrec fun x => encUnitEqs (k x) (d x) := by
  have he : Primrec fun z : ((α × ℕ) × ℕ) × ℕ =>
      encUnitEntry (d z.1.1.1) z.1.1.2 z.1.2 z.2 :=
    enc_primrec_encUnitEntry (hd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
      Primrec.snd
  have h3 : Primrec₂ fun (y : (α × ℕ) × ℕ) (q : ℕ) =>
      [(encUnitEntry (d y.1.1) y.1.2 y.2 q).1, (encUnitEntry (d y.1.1) y.1.2 y.2 q).2] :=
    Primrec.list_cons.comp (Primrec.fst.comp he)
      (Primrec.list_cons.comp (Primrec.snd.comp he) (Primrec.const ([] : List MvP)))
  have h2 : Primrec₂ fun (y : α × ℕ) (p : ℕ) => (List.range (d y.1)).flatMap fun q =>
      [(encUnitEntry (d y.1) y.2 p q).1, (encUnitEntry (d y.1) y.2 p q).2] :=
    Primrec.list_flatMap (Primrec.list_range.comp (hd.comp (Primrec.fst.comp Primrec.fst))) h3
  have h1 : Primrec₂ fun (x : α) (g : ℕ) => (List.range (d x)).flatMap fun p =>
      (List.range (d x)).flatMap fun q =>
        [(encUnitEntry (d x) g p q).1, (encUnitEntry (d x) g p q).2] :=
    Primrec.list_flatMap (Primrec.list_range.comp (hd.comp Primrec.fst)) h2
  exact (Primrec.list_flatMap (Primrec.list_range.comp hk) h1).of_eq fun _ => rfl

/-! ## Vectors, displacements and the norm conditions -/

theorem enc_primrec_encVecCoord (tag : ℕ) {t d r : α → ℕ} (ht : Primrec t) (hd : Primrec d)
    (hr : Primrec r) : Primrec fun x => encVecCoord tag (t x) (d x) (r x) :=
  ((Primrec.list_getD cpZero).comp (enc_primrec_encVecOf tag ht hd) hr).of_eq fun _ => rfl

theorem enc_primrec_encUnitNormPoly {d t : α → ℕ} (hd : Primrec d) (ht : Primrec t) :
    Primrec fun x => encUnitNormPoly (d x) (t x) := by
  have hf : Primrec₂ fun (x : α) (r : ℕ) => encVecCoord 1 (t x) (d x) r :=
    enc_primrec_encVecCoord 1 (ht.comp Primrec.fst) (hd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_append.comp (enc_primrec_encNormSq hd hf)
    (Primrec.const (mvConst (-1)))).of_eq fun _ => rfl

theorem enc_primrec_encDisp (tag : ℕ) {P : α → PresentationCode} {d : α → ℕ}
    {w : α → List (ℕ × Bool)} {t r : α → ℕ} (hP : Primrec P) (hd : Primrec d)
    (hw : Primrec w) (ht : Primrec t) (hr : Primrec r) :
    Primrec fun x => encDisp (P x) (d x) (w x) tag (t x) (r x) :=
  (enc_primrec_cpAdd.comp
    ((Primrec.list_getD cpZero).comp
      (enc_primrec_encWordVec hP hd hw (enc_primrec_encVecOf tag ht hd)) hr)
    (enc_primrec_cpNeg.comp (enc_primrec_encVecCoord tag ht hd hr))).of_eq fun _ => rfl

theorem enc_primrec_encLowerPoly {P : α → PresentationCode} {d : α → ℕ}
    {w : α → List (ℕ × Bool)} {t : α → ℕ} (hP : Primrec P) (hd : Primrec d)
    (hw : Primrec w) (ht : Primrec t) :
    Primrec fun x => encLowerPoly (P x) (d x) (w x) (t x) := by
  have hf : Primrec₂ fun (x : α) (r : ℕ) => encDisp (P x) (d x) (w x) 1 (t x) r :=
    enc_primrec_encDisp 1 (hP.comp Primrec.fst) (hd.comp Primrec.fst) (hw.comp Primrec.fst)
      (ht.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_append.comp
    (PR.primrec_mvMul.comp (Primrec.const (mvConst 16)) (enc_primrec_encNormSq hd hf))
    (Primrec.const (mvConst (-1)))).of_eq fun _ => rfl

theorem enc_primrec_encUpperPoly {P : α → PresentationCode} {n d : α → ℕ}
    {w : α → List (ℕ × Bool)} {t : α → ℕ} (hP : Primrec P) (hn : Primrec n) (hd : Primrec d)
    (hw : Primrec w) (ht : Primrec t) :
    Primrec fun x => encUpperPoly (P x) (n x) (d x) (w x) (t x) := by
  have hf1 : Primrec₂ fun (x : α) (r : ℕ) => encVecCoord 2 (t x) (d x) r :=
    enc_primrec_encVecCoord 2 (ht.comp Primrec.fst) (hd.comp Primrec.fst) Primrec.snd
  have hf2 : Primrec₂ fun (x : α) (r : ℕ) => encDisp (P x) (d x) (w x) 2 (t x) r :=
    enc_primrec_encDisp 2 (hP.comp Primrec.fst) (hd.comp Primrec.fst) (hw.comp Primrec.fst)
      (ht.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_append.comp (enc_primrec_encNormSq hd hf1)
    (PR.primrec_mvMul.comp (PR.primrec_mvConst.comp (enc_primrec_negSqTwoPow.comp hn))
      (enc_primrec_encNormSq hd hf2))).of_eq fun _ => rfl

/-! ## The equations, the inequalities and the quantifier blocks -/

theorem enc_primrec_encEqs {P : α → PresentationCode} {d : α → ℕ}
    {S : α → List (List (ℕ × Bool))} (hP : Primrec P) (hd : Primrec d) (hS : Primrec S) :
    Primrec fun x => encEqs (P x) (d x) (S x) := by
  have h : Primrec₂ fun (x : α) (t : ℕ) => encUnitNormPoly (d x) t :=
    enc_primrec_encUnitNormPoly (hd.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_append.comp
    (enc_primrec_encUnitEqs (RawTransformPrimrec.primrec_genCount.comp hP) hd)
    (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hS)) h)).of_eq
    fun _ => rfl

theorem enc_primrec_encNonnegs {P : α → PresentationCode} {n d : α → ℕ}
    {S : α → List (List (ℕ × Bool))} (hP : Primrec P) (hn : Primrec n) (hd : Primrec d)
    (hS : Primrec S) : Primrec fun x => encNonnegs (P x) (n x) (d x) (S x) := by
  have hc : Primrec fun x => mvConst ((d x : ℤ) - 1) :=
    PR.primrec_mvConst.comp
      (Higman.primrec2_int_sub.comp (Higman.primrec_int_natCast.comp hd) (Primrec.const 1))
  have h1 : Primrec₂ fun (x : α) (t : ℕ) => encLowerPoly (P x) (d x) ((S x).getD t []) t :=
    enc_primrec_encLowerPoly (hP.comp Primrec.fst) (hd.comp Primrec.fst)
      ((Primrec.list_getD []).comp (hS.comp Primrec.fst) Primrec.snd) Primrec.snd
  have h2 : Primrec₂ fun (x : α) (t : ℕ) =>
      encUpperPoly (P x) (n x) (d x) ((P x).2.getD t []) t :=
    enc_primrec_encUpperPoly (hP.comp Primrec.fst) (hn.comp Primrec.fst) (hd.comp Primrec.fst)
      ((Primrec.list_getD []).comp (Primrec.snd.comp (hP.comp Primrec.fst)) Primrec.snd)
      Primrec.snd
  exact (Primrec.list_append.comp
    (Primrec.list_cons.comp hc
      (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hS)) h1))
    (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp hP)))
      h2)).of_eq fun _ => rfl

theorem enc_primrec_encExVars {P : α → PresentationCode} {d : α → ℕ}
    {S : α → List (List (ℕ × Bool))} (hP : Primrec P) (hd : Primrec d) (hS : Primrec S) :
    Primrec fun x => encExVars (P x) (d x) (S x) :=
  (Primrec.list_append.comp
    (enc_primrec_encBlock 0 (RawTransformPrimrec.primrec_genCount.comp hP) hd hd)
    (enc_primrec_encBlock 1 (Primrec.list_length.comp hS) hd (Primrec.const 1))).of_eq
    fun _ => rfl

theorem enc_primrec_encAllVars {P : α → PresentationCode} {d : α → ℕ} (hP : Primrec P)
    (hd : Primrec d) : Primrec fun x => encAllVars (P x) (d x) :=
  (enc_primrec_encBlock 2 (Primrec.list_length.comp (Primrec.snd.comp hP)) hd
    (Primrec.const 1)).of_eq fun _ => rfl

/-! ## The prenex sentence -/

theorem enc_primrec_encFormula {P : α → PresentationCode} {n d : α → ℕ}
    {S : α → List (List (ℕ × Bool))} (hP : Primrec P) (hn : Primrec n) (hd : Primrec d)
    (hS : Primrec S) : Primrec fun x => encFormula (P x) (n x) (d x) (S x) := by
  have hT : Primrec₂ fun (_ : α) (i : ℕ) => (true, i) :=
    Primrec.pair (Primrec.const true) Primrec.snd
  have hF : Primrec₂ fun (_ : α) (i : ℕ) => (false, i) :=
    Primrec.pair (Primrec.const false) Primrec.snd
  have hA : Primrec₂ fun (_ : α) (p : MvP) => ((false, p) : Atom) :=
    Primrec.pair (Primrec.const false) Primrec.snd
  have hpre : Primrec fun x => (encExVars (P x) (d x) (S x)).map (fun i => (true, i)) ++
      (encAllVars (P x) (d x)).map (fun i => (false, i)) :=
    Primrec.list_append.comp (Primrec.list_map (enc_primrec_encExVars hP hd hS) hT)
      (Primrec.list_map (enc_primrec_encAllVars hP hd) hF)
  have hmat : Primrec fun x => qfAnd [(encEqs (P x) (d x) (S x)).map fun p => ((false, p) : Atom)]
      (nonnegQF (encNonnegs (P x) (n x) (d x) (S x))) :=
    PR.primrec_qfAnd.comp
      (Primrec.list_cons.comp (Primrec.list_map (enc_primrec_encEqs hP hd hS) hA)
        (Primrec.const ([] : List (List Atom))))
      (PR.primrec_nonnegQF.comp (enc_primrec_encNonnegs hP hn hd hS))
  exact (Primrec.pair hpre hmat).of_eq fun _ => rfl

/-- `prop:mf-upper-bound`, printed sentence `9eae4d68673a`: the prenex sentence
`encodePrenex ((P, n), c)` is a primitive recursive function of `((P, n), c)`. -/
theorem primrec_encodePrenex : Primrec encodePrenex :=
  (enc_primrec_encFormula (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    enc_primrec_certDim enc_primrec_sWords).of_eq fun _ => rfl

/-- `prop:mf-upper-bound`, printed sentence `9eae4d68673a`, feeding `thm:mf-arithmetic`:
the prenex sentence `Φ(P, n, c)` is computed from `((P, n), c)` by an algorithm. -/
theorem computable_encodePrenex : Computable encodePrenex :=
  primrec_encodePrenex.to_comp

end GroupApproximation.Full.NN11b
