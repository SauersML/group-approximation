import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.PolyOps

/-!
# Formulas and guarded case trees are primitive recursive

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Quantifier elimination
(Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*, Ch. 2 and Ch. 10) branches on
the signs of parametric coefficients, and its intermediate results are guarded case trees
(`Tree.lean`).  This file proves the case-tree monad (`tpure`, `tbind`, `tmap`, `tseq`),
the formula operations (`qfAnd`, `qfNot`, `toQF`, `nonnegQF`), evaluation at the zero
assignment (`qfZ`) and the normalization of coefficient lists (`normUP`) primitive
recursive.  Operations taking a function argument get a parametric statement.
-/

namespace GroupApproximation.Full.NN11b.PR

section Trees

variable {δ : Type*} {α β : Type} [Primcodable δ] [Primcodable α] [Primcodable β]

theorem primrec_tpure : Primrec (@tpure α) :=
  (Primrec.list_cons.comp (Primrec.pair (Primrec.const ([] : List Atom)) Primrec.id)
    (Primrec.const ([] : List (List Atom × α)))).of_eq fun _ => rfl

theorem primrec_guardT : Primrec₂ (@guardT α) := by
  show Primrec fun p : List Atom × List (List Atom × α) => guardT p.1 p.2
  exact (Primrec.list_map (f := fun p : List Atom × List (List Atom × α) => p.2)
    (g := fun (p : List Atom × List (List Atom × α)) (l : List Atom × α) => (p.1 ++ l.1, l.2))
    Primrec.snd
    (Primrec.pair (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- `tbind` with a primitive recursive tree and a primitive recursive continuation. -/
theorem primrec_tbind {f : δ → List (List Atom × α)} {g : δ → α → List (List Atom × β)}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun d => tbind (f d) (g d) :=
  (Primrec.list_flatMap (f := f)
    (g := fun (d : δ) (l : List Atom × α) => guardT l.1 (g d l.2)) hf
    ((primrec_guardT (α := β)).comp (Primrec.fst.comp Primrec.snd)
      (hg.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun _ => rfl

/-- `tmap` with a primitive recursive function and a primitive recursive tree. -/
theorem primrec_tmap {f : δ → α → β} {t : δ → List (List Atom × α)} (hf : Primrec₂ f)
    (ht : Primrec t) : Primrec fun d => tmap (f d) (t d) :=
  (Primrec.list_map (f := t) (g := fun (d : δ) (l : List Atom × α) => (l.1, f d l.2)) ht
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun _ => rfl

theorem primrec_tseq_step :
    Primrec fun q : List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α) => tbind q.1 fun a => tmap (List.cons a) q.2.2 :=
  primrec_tbind
    (f := fun q : List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α) => q.1)
    (g := fun (q : List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α)) (a : α) => tmap (List.cons a) q.2.2)
    Primrec.fst
    (primrec_tmap
      (f := fun (p : (List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α)) × α) (l : List α) => p.2 :: l)
      (t := fun p : (List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α)) × α => p.1.2.2)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

theorem primrec_tseq : Primrec (@tseq α) :=
  listRec₁ (F := @tseq α) (c := tpure ([] : List α))
    (h := fun q : List (List Atom × α) × List (List (List Atom × α)) ×
        List (List Atom × List α) => tbind q.1 fun a => tmap (List.cons a) q.2.2)
    primrec_tseq_step rfl (fun _ _ => rfl)

end Trees

/-! ## Formulas -/

theorem primrec_toQF : Primrec toQF :=
  listRec₁ (F := toQF) (c := ([] : List (List Atom)))
    (h := fun q : (List Atom × Bool) × List (List Atom × Bool) × List (List Atom) =>
      bif q.1.2 then q.1.1 :: q.2.2 else q.2.2)
    (Primrec.cond (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
    rfl (fun b _ => by rcases b with ⟨_, _ | _⟩ <;> rfl)

theorem primrec_qfAnd : Primrec₂ qfAnd := by
  show Primrec fun p : List (List Atom) × List (List Atom) => qfAnd p.1 p.2
  exact (Primrec.list_flatMap (f := fun p : List (List Atom) × List (List Atom) => p.1)
    (g := fun (p : List (List Atom) × List (List Atom)) (c : List Atom) =>
      p.2.map fun d => c ++ d)
    Primrec.fst
    (Primrec.list_map
      (f := fun q : (List (List Atom) × List (List Atom)) × List Atom => q.1.2)
      (g := fun (q : (List (List Atom) × List (List Atom)) × List Atom) (d : List Atom) =>
        q.2 ++ d)
      (Primrec.snd.comp Primrec.fst)
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).of_eq
    fun _ => rfl

theorem primrec_negAtom : Primrec negAtom :=
  (Primrec.list_cons.comp
    (Primrec.list_cons.comp (Primrec.pair (Primrec.not.comp Primrec.fst) Primrec.snd)
      (Primrec.const ([] : List Atom)))
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const true) (primrec_mvNeg.comp Primrec.snd))
        (Primrec.const ([] : List Atom)))
      (Primrec.const ([] : List (List Atom))))).of_eq fun a => by
    rcases a with ⟨_ | _, _⟩ <;> rfl

theorem primrec_qfNot : Primrec qfNot :=
  listRec₁ (F := qfNot) (c := ([[]] : List (List Atom)))
    (h := fun q : List Atom × List (List Atom) × List (List Atom) =>
      qfAnd (q.1.flatMap negAtom) q.2.2)
    (primrec_qfAnd.comp
      (Primrec.list_flatMap
        (f := fun q : List Atom × List (List Atom) × List (List Atom) => q.1)
        (g := fun (_ : List Atom × List (List Atom) × List (List Atom)) (a : Atom) => negAtom a)
        Primrec.fst (primrec_negAtom.comp Primrec.snd).to₂)
      (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

theorem primrec_nonnegQF : Primrec nonnegQF :=
  listRec₁ (F := nonnegQF) (c := ([[]] : List (List Atom)))
    (h := fun q : MvP × List MvP × List (List Atom) =>
      qfAnd [[(true, q.1)], [(false, q.1)]] q.2.2)
    (primrec_qfAnd.comp
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.pair (Primrec.const true) Primrec.fst)
          (Primrec.const ([] : List Atom)))
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.pair (Primrec.const false) Primrec.fst)
            (Primrec.const ([] : List Atom)))
          (Primrec.const ([] : List (List Atom)))))
      (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

/-! ## Evaluation at the zero assignment -/

theorem primrec_monoZ : Primrec monoZ :=
  listRec₁ (F := monoZ) (c := (1 : ℤ))
    (h := fun q : ℕ × List ℕ × ℤ => (if q.1 = 0 then (1 : ℤ) else 0) * q.2.2)
    (primrec_int_mul.comp
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const (0 : ℕ)))
        (Primrec.const (1 : ℤ)) (Primrec.const (0 : ℤ)))
      (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

theorem primrec_mvZ : Primrec mvZ :=
  listRec₁ (F := mvZ) (c := (0 : ℤ))
    (h := fun q : (ℤ × List ℕ) × MvP × ℤ => q.1.1 * monoZ q.1.2 + q.2.2)
    (Higman.primrec2_int_add.comp
      (primrec_int_mul.comp (Primrec.fst.comp Primrec.fst)
        (primrec_monoZ.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

theorem primrec_atomZ : Primrec atomZ :=
  (Primrec.cond Primrec.fst
    (primrec2_int_decide_lt.comp (Primrec.const (0 : ℤ)) (primrec_mvZ.comp Primrec.snd))
    ((Primrec.eq (α := ℤ)).decide.comp (primrec_mvZ.comp Primrec.snd)
      (Primrec.const (0 : ℤ)))).of_eq fun a => by
    rcases a with ⟨_ | _, _⟩ <;> rfl

theorem primrec_qfZ : Primrec qfZ :=
  (primrec_list_any (f := fun f : List (List Atom) => f)
    (p := fun (_ : List (List Atom)) (c : List Atom) => c.all atomZ) Primrec.id
    (primrec_list_all (f := fun q : List (List Atom) × List Atom => q.2)
      (p := fun (_ : List (List Atom) × List Atom) (a : Atom) => atomZ a) Primrec.snd
      (primrec_atomZ.comp Primrec.snd).to₂).to₂).of_eq fun _ => rfl

/-! ## Normalization of coefficient lists -/

section Norm

variable {δ : Type*} {α : Type} [Primcodable δ] [Primcodable α]

theorem primrec_branch3 {c : δ → MvP} {t1 t2 t3 : δ → List (List Atom × α)} (hc : Primrec c)
    (h1 : Primrec t1) (h2 : Primrec t2) (h3 : Primrec t3) :
    Primrec fun d => branch3 (c d) (t1 d) (t2 d) (t3 d) :=
  (Primrec.list_append.comp
    (Primrec.list_append.comp
      ((primrec_guardT (α := α)).comp
        (Primrec.list_cons.comp (Primrec.pair (Primrec.const true) hc)
          (Primrec.const ([] : List Atom))) h1)
      ((primrec_guardT (α := α)).comp
        (Primrec.list_cons.comp (Primrec.pair (Primrec.const true) (primrec_mvNeg.comp hc))
          (Primrec.const ([] : List Atom))) h2))
    ((primrec_guardT (α := α)).comp
      (Primrec.list_cons.comp (Primrec.pair (Primrec.const false) hc)
        (Primrec.const ([] : List Atom))) h3)).of_eq fun _ => rfl

end Norm

theorem primrec_normRev_step :
    Primrec fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) =>
      branch3 q.1 (tpure (some (q.2.1.reverse, q.1, true)))
        (tpure (some (q.2.1.reverse, q.1, false))) q.2.2 :=
  primrec_branch3
    (c := fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) => q.1)
    (t1 := fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) =>
      tpure (some (q.2.1.reverse, q.1, true)))
    (t2 := fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) =>
      tpure (some (q.2.1.reverse, q.1, false)))
    (t3 := fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) =>
      q.2.2)
    Primrec.fst
    ((primrec_tpure (α := Option (List MvP × MvP × Bool))).comp (Primrec.option_some.comp
      (Primrec.pair (Primrec.list_reverse.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair Primrec.fst (Primrec.const true)))))
    ((primrec_tpure (α := Option (List MvP × MvP × Bool))).comp (Primrec.option_some.comp
      (Primrec.pair (Primrec.list_reverse.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair Primrec.fst (Primrec.const false)))))
    (Primrec.snd.comp Primrec.snd)

theorem primrec_normRev : Primrec normRev :=
  listRec₁ (F := normRev) (c := tpure (none : Option (List MvP × MvP × Bool)))
    (h := fun q : MvP × List MvP × List (List Atom × Option (List MvP × MvP × Bool)) =>
      branch3 q.1 (tpure (some (q.2.1.reverse, q.1, true)))
        (tpure (some (q.2.1.reverse, q.1, false))) q.2.2)
    primrec_normRev_step rfl (fun _ _ => rfl)

theorem primrec_normUP : Primrec normUP :=
  (primrec_normRev.comp Primrec.list_reverse).of_eq fun _ => rfl

end GroupApproximation.Full.NN11b.PR
