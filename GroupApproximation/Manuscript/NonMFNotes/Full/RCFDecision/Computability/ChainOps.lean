import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.TreeOps

/-!
# Parametric Sturm chains are primitive recursive

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  The Tarski queries of the
decision procedure (Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*, Ch. 2 and
Ch. 10) are computed from generalized signed remainder sequences with parametric
coefficients.  This file proves the pseudo-remainder loop `premLoop`, one chain step
`chainStep`, its iterates `chainIter`, the value `leafVal` of a finished chain, and the
Tarski query tree `taqTree` primitive recursive.

`premLoop` recurses on its fuel while changing the dividend, so it is rewritten as an
iterate of a self-map `premIter` of the dividend which is the identity once the dividend
is shorter than the divisor.  `changes` reads a list against its tail (`changesZ`).
-/

namespace GroupApproximation.Full.NN11b.PR

theorem primrec_bsgn : Primrec bsgn :=
  Primrec.dom_bool bsgn

/-! ## Pseudo-remainder -/

theorem primrec_premStep :
    Primrec fun q : MvP × List MvP × MvP × List MvP => premStep q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  (primrec_upAdd.comp
    (primrec_upSmul.comp (primrec_mvMul.comp Primrec.fst Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (primrec_upSmul.comp
      (primrec_mvNeg.comp
        (primrec_mvMul.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.list_append.comp
        (primrec_replicate.comp
          (Primrec.nat_sub.comp
            (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.const ([] : MvP)))
        (Primrec.fst.comp Primrec.snd)))).of_eq fun _ => rfl

/-- One step of the pseudo-remainder loop as a self-map of the dividend (top coefficient
first); it fixes dividends shorter than the divisor. -/
def premIter (bl : MvP) (b : List MvP) : List MvP → List MvP
  | [] => []
  | an :: w => if w.length < b.length then an :: w else (premStep bl b an w.reverse).reverse

/-- The pseudo-remainder loop is an iterate of `premIter`. -/
theorem premLoop_eq (bl : MvP) (b : List MvP) (t : ℕ) :
    ∀ v : List MvP, premLoop bl b t v = (premIter bl b)^[t] v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    cases v with
    | nil => exact (Function.iterate_fixed (f := premIter bl b) (x := []) rfl t).symm
    | cons an w =>
      by_cases h : w.length < b.length
      · have hf : premIter bl b (an :: w) = an :: w := if_pos h
        show premLoop bl b (t + 1) (an :: w) = (premIter bl b)^[t] (premIter bl b (an :: w))
        rw [hf, Function.iterate_fixed hf t]
        exact if_pos h
      · have hf : premIter bl b (an :: w) = (premStep bl b an w.reverse).reverse := if_neg h
        show premLoop bl b (t + 1) (an :: w) = (premIter bl b)^[t] (premIter bl b (an :: w))
        rw [hf, ← ih]
        exact if_neg h

theorem primrec_premIter :
    Primrec fun q : (MvP × List MvP) × List MvP => premIter q.1.1 q.1.2 q.2 :=
  (Primrec.list_casesOn (f := fun q : (MvP × List MvP) × List MvP => q.2)
    (g := fun _ : (MvP × List MvP) × List MvP => ([] : List MvP))
    (h := fun (q : (MvP × List MvP) × List MvP) (p : MvP × List MvP) =>
      if p.2.length < q.1.2.length then p.1 :: p.2
      else (premStep q.1.1 q.1.2 p.1 p.2.reverse).reverse)
    Primrec.snd (Primrec.const ([] : List MvP))
    (Primrec.ite
      (c := fun r : ((MvP × List MvP) × List MvP) × MvP × List MvP =>
        r.2.2.length < r.1.1.2.length)
      (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.list_reverse.comp (primrec_premStep.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd)))))))).to₂).of_eq
    fun q => by rcases q with ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

theorem primrec_premLoop :
    Primrec fun q : MvP × List MvP × ℕ × List MvP => premLoop q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  (Primrec.nat_iterate (f := fun q : MvP × List MvP × ℕ × List MvP => q.2.2.1)
    (g := fun q : MvP × List MvP × ℕ × List MvP => q.2.2.2)
    (h := fun (q : MvP × List MvP × ℕ × List MvP) (w : List MvP) => premIter q.1 q.2.1 w)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (primrec_premIter.comp
      (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)).to₂).of_eq fun q =>
    (premLoop_eq q.1 q.2.1 q.2.2.1 q.2.2.2).symm

/-! ## Chain steps -/

theorem primrec_chainNext :
    Primrec fun q : (List MvP × List MvP × MvP × List (ℤ × ℤ)) × Option NForm =>
      chainNext q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 :=
  (Primrec.option_casesOn
    (o := fun q : (List MvP × List MvP × MvP × List (ℤ × ℤ)) × Option NForm => q.2)
    (f := fun q : (List MvP × List MvP × MvP × List (ℤ × ℤ)) × Option NForm =>
      ((true, q.1) : St))
    (g := fun (q : (List MvP × List MvP × MvP × List (ℤ × ℤ)) × Option NForm) (n : NForm) =>
      ((false, q.1.2.2.1 :: q.1.2.1.reverse, n.1, n.2.1,
        q.1.2.2.2 ++ [(bsgn n.2.2, bsgn n.2.2 * (-1) ^ n.1.length)]) : St))
    Primrec.snd (Primrec.pair (Primrec.const true) Primrec.fst)
    (Primrec.pair (Primrec.const false)
      (Primrec.pair
        (Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.list_reverse.comp
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.list_append.comp
              (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
              (Primrec.list_cons.comp
                (Primrec.pair (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
                  (primrec_int_mul.comp
                    (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
                    (primrec_neg_one_pow.comp
                      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))))
                (Primrec.const ([] : List (ℤ × ℤ)))))))).to₂).of_eq fun q => by
    rcases q with ⟨⟨_, _, _, _⟩, _ | ⟨_, _, _⟩⟩ <;> rfl

theorem primrec_chainStep_cons :
    Primrec fun r : St × (MvP × List MvP) =>
      tmap (chainNext r.1.2.1 (r.2.1 :: r.2.2) r.1.2.2.2.1 r.1.2.2.2.2)
        (normUP (upNeg (premLoop r.1.2.2.2.1 (r.2.1 :: r.2.2) r.1.2.1.length r.1.2.1).reverse)) :=
  primrec_tmap (δ := St × (MvP × List MvP)) (α := Option NForm) (β := St)
    (f := fun (r : St × (MvP × List MvP)) (o : Option NForm) =>
      chainNext r.1.2.1 (r.2.1 :: r.2.2) r.1.2.2.2.1 r.1.2.2.2.2 o)
    (t := fun r : St × (MvP × List MvP) =>
      normUP (upNeg (premLoop r.1.2.2.2.1 (r.2.1 :: r.2.2) r.1.2.1.length r.1.2.1).reverse))
    (primrec_chainNext.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
            (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))))
      Primrec.snd)).to₂
    (primrec_normUP.comp (primrec_upNeg.comp (Primrec.list_reverse.comp (primrec_premLoop.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
          (Primrec.pair (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))))))

theorem primrec_chainStep : Primrec chainStep :=
  (Primrec.cond (Primrec.fst (α := Bool) (β := List MvP × List MvP × MvP × List (ℤ × ℤ)))
    ((primrec_tpure (α := St)).comp (Primrec.pair (Primrec.const true) Primrec.snd))
    (Primrec.list_casesOn (f := fun st : St => st.2.2.1)
      (g := fun st : St => tpure ((true, st.2) : St))
      (h := fun (st : St) (cb : MvP × List MvP) =>
        tmap (chainNext st.2.1 (cb.1 :: cb.2) st.2.2.2.1 st.2.2.2.2)
          (normUP (upNeg (premLoop st.2.2.2.1 (cb.1 :: cb.2) st.2.1.length st.2.1).reverse)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      ((primrec_tpure (α := St)).comp (Primrec.pair (Primrec.const true) Primrec.snd))
      primrec_chainStep_cons.to₂)).of_eq fun st => by
    rcases st with ⟨_ | _, _, _ | ⟨_, _⟩, _, _⟩ <;> rfl

theorem primrec_chainIter : Primrec₂ chainIter := by
  show Primrec fun p : ℕ × List (List Atom × St) => chainIter p.1 p.2
  exact (Primrec.nat_iterate (f := fun p : ℕ × List (List Atom × St) => p.1)
    (g := fun p : ℕ × List (List Atom × St) => p.2)
    (h := fun (_ : ℕ × List (List Atom × St)) (s : List (List Atom × St)) => tbind s chainStep)
    Primrec.fst Primrec.snd
    (primrec_tbind (δ := (ℕ × List (List Atom × St)) × List (List Atom × St)) (α := St)
      (β := St)
      (f := fun r : (ℕ × List (List Atom × St)) × List (List Atom × St) => r.2)
      (g := fun (_ : (ℕ × List (List Atom × St)) × List (List Atom × St)) (st : St) =>
        chainStep st)
      Primrec.snd (primrec_chainStep.comp Primrec.snd).to₂).to₂).of_eq fun _ => rfl

/-! ## Chain values -/

/-- Sign changes of a list read against a second list (its tail, in `changes_eq`). -/
def changesZ : List ℤ → List ℤ → ℕ
  | a :: xs, b :: ys => (if a * b < 0 then 1 else 0) + changesZ xs ys
  | _, _ => 0

theorem changes_eq (l : List ℤ) : changes l = changesZ l l.tail := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b m => exact congrArg (fun k : ℕ => (if a * b < 0 then 1 else 0) + k) ih

theorem primrec_changesZ : Primrec₂ changesZ :=
  zipRec₀ (F := changesZ) (c := (0 : ℕ))
    (H := fun q : ℤ × ℤ × ℕ => (if q.1 * q.2.1 < 0 then 1 else 0) + q.2.2)
    (Primrec.nat_add.comp
      (Primrec.ite (c := fun q : ℤ × ℤ × ℕ => q.1 * q.2.1 < 0)
        (primrecRel_int_lt.comp
          (primrec_int_mul.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.const (0 : ℤ)))
        (Primrec.const (1 : ℕ)) (Primrec.const (0 : ℕ)))
      (Primrec.snd.comp Primrec.snd))
    (fun ys => by cases ys <;> rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem primrec_changes : Primrec changes :=
  (primrec_changesZ.comp Primrec.id Primrec.list_tail).of_eq fun l => (changes_eq l).symm

theorem primrec_leafVal : Primrec leafVal :=
  (Higman.primrec2_int_sub.comp
    (Higman.primrec_int_natCast.comp (primrec_changes.comp
      (Primrec.list_map (f := fun st : St => st.2.2.2.2)
        (g := fun (_ : St) (p : ℤ × ℤ) => p.2)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd).to₂)))
    (Higman.primrec_int_natCast.comp (primrec_changes.comp
      (Primrec.list_map (f := fun st : St => st.2.2.2.2)
        (g := fun (_ : St) (p : ℤ × ℤ) => p.1)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.snd).to₂)))).of_eq fun _ => rfl

theorem primrec_chainStart :
    Primrec fun q : NForm × NForm => chainStart q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2 :=
  (primrec_chainIter.comp
    (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    ((primrec_tpure (α := St)).comp
      (Primrec.pair (Primrec.const false)
        (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.list_reverse.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair (Primrec.fst.comp Primrec.snd)
            (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
              (Primrec.list_cons.comp
                (Primrec.pair (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
                  (primrec_int_mul.comp
                    (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
                    (primrec_neg_one_pow.comp
                      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))))
                (Primrec.list_cons.comp
                  (Primrec.pair
                    (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
                    (primrec_int_mul.comp
                      (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
                      (primrec_neg_one_pow.comp
                        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))))
                  (Primrec.const ([] : List (ℤ × ℤ)))))))))).of_eq fun _ => rfl

/-! ## Tarski queries -/

theorem primrec_taqTree : Primrec₂ taqTree := by
  show Primrec fun p : List MvP × List MvP => taqTree p.1 p.2
  refine (primrec_tbind (δ := List MvP × List MvP) (α := Option NForm) (β := ℤ)
    (f := fun p : List MvP × List MvP => normUP p.1)
    (g := fun (p : List MvP × List MvP) (o0 : Option NForm) => o0.elim (tpure 0) fun n0 =>
      tbind (normUP p.2) fun o1 => o1.elim (tpure 0) fun n1 =>
        tmap leafVal (chainStart n0.1 n0.2.1 n0.2.2 n1.1 n1.2.1 n1.2.2))
    (primrec_normUP.comp Primrec.fst) ?_).of_eq fun _ => rfl
  refine (primrec_option_elim
    (o := fun r : (List MvP × List MvP) × Option NForm => r.2)
    (d := fun _ : (List MvP × List MvP) × Option NForm => tpure (0 : ℤ))
    (g := fun (r : (List MvP × List MvP) × Option NForm) (n0 : NForm) =>
      tbind (normUP r.1.2) fun o1 => o1.elim (tpure 0) fun n1 =>
        tmap leafVal (chainStart n0.1 n0.2.1 n0.2.2 n1.1 n1.2.1 n1.2.2))
    Primrec.snd (Primrec.const _) ?_).to₂
  refine (primrec_tbind (α := Option NForm) (β := ℤ)
    (f := fun s : ((List MvP × List MvP) × Option NForm) × NForm => normUP s.1.1.2)
    (g := fun (s : ((List MvP × List MvP) × Option NForm) × NForm) (o1 : Option NForm) =>
      o1.elim (tpure 0) fun n1 =>
        tmap leafVal (chainStart s.2.1 s.2.2.1 s.2.2.2 n1.1 n1.2.1 n1.2.2))
    (primrec_normUP.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) ?_).to₂
  refine (primrec_option_elim
    (o := fun u : (((List MvP × List MvP) × Option NForm) × NForm) × Option NForm => u.2)
    (d := fun _ : (((List MvP × List MvP) × Option NForm) × NForm) × Option NForm =>
      tpure (0 : ℤ))
    (g := fun (u : (((List MvP × List MvP) × Option NForm) × NForm) × Option NForm)
      (n1 : NForm) => tmap leafVal (chainStart u.1.2.1 u.1.2.2.1 u.1.2.2.2 n1.1 n1.2.1 n1.2.2))
    Primrec.snd (Primrec.const _) ?_).to₂
  exact (primrec_tmap (α := St) (β := ℤ)
    (f := fun (_ : ((((List MvP × List MvP) × Option NForm) × NForm) × Option NForm) × NForm)
      (st : St) => leafVal st)
    (t := fun w : ((((List MvP × List MvP) × Option NForm) × NForm) × Option NForm) × NForm =>
      chainStart w.1.1.2.1 w.1.1.2.2.1 w.1.1.2.2.2 w.2.1 w.2.2.1 w.2.2.2)
    (primrec_leafVal.comp Primrec.snd).to₂
    (primrec_chainStart.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))).to₂

end GroupApproximation.Full.NN11b.PR
