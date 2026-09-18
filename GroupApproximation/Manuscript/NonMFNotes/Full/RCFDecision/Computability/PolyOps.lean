import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Algo
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.IntOps
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.ListOps

/-!
# The polynomial operations of the decision procedure are primitive recursive

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  The symbolic procedure
(Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*, Ch. 2 and Ch. 10) works with
integer polynomials as monomial lists (`Poly.lean`) and with univariate polynomials
over them as coefficient lists (`UPoly.lean`).  Every operation there is a structural
recursion, and this file proves each one primitive recursive from its defining equations.
-/

namespace GroupApproximation.Full.NN11b.PR

/-! ## Multivariate polynomials -/

theorem primrec_mvNeg : Primrec mvNeg :=
  listRec₁ (F := mvNeg) (c := ([] : MvP))
    (h := fun q : (ℤ × List ℕ) × MvP × MvP => (-q.1.1, q.1.2) :: q.2.2)
    (Primrec.list_cons.comp
      (Primrec.pair (Higman.primrec_int_neg.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    rfl (fun _ _ => rfl)

theorem primrec_addExp : Primrec₂ addExp :=
  zipLong (F := addExp) (op := fun x y : ℕ => x + y) Primrec.nat_add (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem primrec_mvMulMono :
    Primrec₂ fun (ce : ℤ × List ℕ) (p : MvP) => mvMulMono ce.1 ce.2 p :=
  listRec₂ (F := fun (ce : ℤ × List ℕ) (p : MvP) => mvMulMono ce.1 ce.2 p)
    (g := fun _ : ℤ × List ℕ => ([] : MvP))
    (h := fun (ce : ℤ × List ℕ) (q : (ℤ × List ℕ) × MvP × MvP) =>
      (ce.1 * q.1.1, addExp ce.2 q.1.2) :: q.2.2)
    (Primrec.const ([] : MvP))
    (Primrec.list_cons.comp
      (Primrec.pair
        (primrec_int_mul.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (primrec_addExp.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem primrec_mvMul_swap : Primrec₂ fun (q p : MvP) => mvMul p q :=
  listRec₂ (F := fun (q p : MvP) => mvMul p q) (g := fun _ : MvP => ([] : MvP))
    (h := fun (q : MvP) (r : (ℤ × List ℕ) × MvP × MvP) => mvMulMono r.1.1 r.1.2 q ++ r.2.2)
    (Primrec.const ([] : MvP))
    (Primrec.list_append.comp (primrec_mvMulMono.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem primrec_mvMul : Primrec₂ mvMul := by
  show Primrec fun p : MvP × MvP => mvMul p.1 p.2
  exact primrec_mvMul_swap.comp Primrec.snd Primrec.fst

theorem primrec_mvConst : Primrec mvConst :=
  (Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const ([] : List ℕ)))
    (Primrec.const ([] : MvP))).of_eq fun _ => rfl

/-! ## Coefficient lists -/

theorem primrec_upAdd : Primrec₂ upAdd :=
  zipLong (F := upAdd) (op := fun a b : MvP => a ++ b) Primrec.list_append (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem primrec_upNeg : Primrec upNeg :=
  listRec₁ (F := upNeg) (c := ([] : List MvP))
    (h := fun q : MvP × List MvP × List MvP => mvNeg q.1 :: q.2.2)
    (Primrec.list_cons.comp (primrec_mvNeg.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

theorem primrec_upSmul : Primrec₂ upSmul :=
  listRec₂ (F := upSmul) (g := fun _ : MvP => ([] : List MvP))
    (h := fun (c : MvP) (q : MvP × List MvP × List MvP) => mvMul c q.1 :: q.2.2)
    (Primrec.const ([] : List MvP))
    (Primrec.list_cons.comp (primrec_mvMul.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem primrec_upMul_swap : Primrec₂ fun (v u : List MvP) => upMul u v :=
  listRec₂ (F := fun (v u : List MvP) => upMul u v) (g := fun _ : List MvP => ([] : List MvP))
    (h := fun (v : List MvP) (q : MvP × List MvP × List MvP) =>
      upAdd (upSmul q.1 v) ([] :: q.2.2))
    (Primrec.const ([] : List MvP))
    (primrec_upAdd.comp (primrec_upSmul.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.list_cons.comp (Primrec.const ([] : MvP))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem primrec_upMul : Primrec₂ upMul := by
  show Primrec fun p : List MvP × List MvP => upMul p.1 p.2
  exact primrec_upMul_swap.comp Primrec.snd Primrec.fst

/-- One step of `upDerivAux` as a left fold: the state is the current multiplier and the
reversed output. -/
def derivStep (s : ℕ × List MvP) (c : MvP) : ℕ × List MvP :=
  (s.1 + 1, mvMul (mvConst (s.1 : ℤ)) c :: s.2)

theorem foldl_derivStep (u : List MvP) : ∀ (k : ℕ) (acc : List MvP),
    (u.foldl derivStep (k, acc)).2 = (upDerivAux k u).reverse ++ acc := by
  induction u with
  | nil => intro k acc; rfl
  | cons c u ih =>
    intro k acc
    refine (ih (k + 1) (mvMul (mvConst (k : ℤ)) c :: acc)).trans ?_
    have e : upDerivAux k (c :: u) = mvMul (mvConst (k : ℤ)) c :: upDerivAux (k + 1) u := rfl
    rw [e, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem upDerivAux_eq (k : ℕ) (u : List MvP) :
    upDerivAux k u = (u.foldl derivStep (k, ([] : List MvP))).2.reverse := by
  rw [foldl_derivStep u k [], List.append_nil, List.reverse_reverse]

theorem primrec_derivStep : Primrec₂ derivStep := by
  show Primrec fun p : (ℕ × List MvP) × MvP => derivStep p.1 p.2
  exact (Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
    (Primrec.list_cons.comp
      (primrec_mvMul.comp
        (primrec_mvConst.comp (Higman.primrec_int_natCast.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
      (Primrec.snd.comp Primrec.fst))).of_eq fun _ => rfl

theorem primrec_upDerivAux : Primrec₂ upDerivAux := by
  show Primrec fun p : ℕ × List MvP => upDerivAux p.1 p.2
  exact (Primrec.list_reverse.comp (Primrec.snd.comp
    (Primrec.list_foldl (f := fun p : ℕ × List MvP => p.2)
      (g := fun p : ℕ × List MvP => (p.1, ([] : List MvP)))
      (h := fun (_ : ℕ × List MvP) (q : (ℕ × List MvP) × MvP) => derivStep q.1 q.2)
      Primrec.snd (Primrec.pair Primrec.fst (Primrec.const ([] : List MvP)))
      (primrec_derivStep.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂))).of_eq
    fun p => (upDerivAux_eq p.1 p.2).symm

theorem primrec_upDeriv : Primrec upDeriv :=
  (primrec_upDerivAux.comp (Primrec.const 1) Primrec.list_tail).of_eq fun u => by
    rcases u with _ | ⟨_, _⟩ <;> rfl

/-! ## Viewing a polynomial in one variable, powers and products -/

theorem primrec_monoUP : Primrec fun p : ℕ × ℤ × List ℕ => monoUP p.1 p.2.1 p.2.2 :=
  (Primrec.list_append.comp
    (primrec_replicate.comp
      ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.const ([] : MvP)))
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.list_set.comp (Primrec.snd.comp Primrec.snd)
            (Primrec.pair Primrec.fst (Primrec.const (0 : ℕ)))))
        (Primrec.const ([] : MvP)))
      (Primrec.const ([] : List MvP)))).of_eq fun _ => rfl

theorem primrec_coeffX : Primrec₂ coeffX :=
  listRec₂ (F := coeffX) (g := fun _ : ℕ => ([] : List MvP))
    (h := fun (i : ℕ) (q : (ℤ × List ℕ) × MvP × List MvP) => upAdd (monoUP i q.1.1 q.1.2) q.2.2)
    (Primrec.const ([] : List MvP))
    (primrec_upAdd.comp
      (primrec_monoUP.comp (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem primrec_upPow : Primrec₂ upPow := by
  refine (Primrec.nat_rec (f := fun _ : List MvP => upOne)
    (g := fun (u : List MvP) (q : ℕ × List MvP) => upMul u q.2) (Primrec.const upOne)
    (primrec_upMul.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun u k => ?_
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (upMul u) ih

theorem primrec_prodPowUP : Primrec₂ prodPowUP :=
  zipRec₀ (F := prodPowUP) (c := upOne)
    (H := fun q : List MvP × ℕ × List MvP => upMul (upPow q.1 q.2.1) q.2.2)
    (primrec_upMul.comp (primrec_upPow.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
    (fun ys => by cases ys <;> rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem primrec_prodUP : Primrec prodUP :=
  listRec₁ (F := prodUP) (c := upOne)
    (h := fun q : List MvP × List (List MvP) × List MvP => upMul q.1 q.2.2)
    (primrec_upMul.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    rfl (fun _ _ => rfl)

end GroupApproximation.Full.NN11b.PR
