import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.BKROps
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SystemDefs
import Mathlib.Computability.Partrec

/-!
# The decision procedure for prenex sentences is computable

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Quantifier elimination over the
real closed field (Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*, Ch. 2 and
Ch. 10), as implemented by `elimEx`, `elimAll` and `decidePrenex`, is primitive
recursive, and so is the translation `systemPrenex` of a polynomial system into an
existential sentence.  Hence both are `Computable`.
-/

namespace GroupApproximation.Full.NN11b.PR

/-! ## Quantifier elimination -/

theorem primrec_elimEx : Primrec₂ elimEx := by
  show Primrec fun p : ℕ × List (List Atom) => elimEx p.1 p.2
  exact (Primrec.list_flatMap (f := fun p : ℕ × List (List Atom) => p.2)
    (g := fun (p : ℕ × List (List Atom)) (c : List Atom) => toQF (conjTree p.1 c))
    Primrec.snd
    (primrec_toQF.comp
      (primrec_conjTree.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    fun _ => rfl

/-- The one-step recursion body of `elimAll`. -/
theorem primrec_elimAll_step :
    Primrec fun r : List (List Atom) × (Bool × ℕ) × List (Bool × ℕ) × List (List Atom) =>
      bif r.2.1.1 then elimEx r.2.1.2 r.2.2.2
      else qfNot (elimEx r.2.1.2 (qfNot r.2.2.2)) :=
  Primrec.cond (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (primrec_elimEx.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (primrec_qfNot.comp
      (primrec_elimEx.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (primrec_qfNot.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem primrec_elimAll_swap :
    Primrec₂ fun (f : List (List Atom)) (qs : List (Bool × ℕ)) => elimAll qs f :=
  listRec₂ (F := fun (f : List (List Atom)) (qs : List (Bool × ℕ)) => elimAll qs f)
    (g := fun f : List (List Atom) => f)
    (h := fun (_ : List (List Atom)) (q : (Bool × ℕ) × List (Bool × ℕ) × List (List Atom)) =>
      bif q.1.1 then elimEx q.1.2 q.2.2 else qfNot (elimEx q.1.2 (qfNot q.2.2)))
    Primrec.id primrec_elimAll_step.to₂ (fun _ => rfl)
    (fun _ q _ => by rcases q with ⟨_ | _, _⟩ <;> rfl)

theorem primrec_elimAll :
    Primrec fun φ : List (Bool × ℕ) × List (List Atom) => elimAll φ.1 φ.2 :=
  (primrec_elimAll_swap.comp Primrec.snd Primrec.fst).of_eq fun _ => rfl

theorem primrec_decidePrenex : Primrec decidePrenex :=
  (primrec_qfZ.comp primrec_elimAll).of_eq fun _ => rfl

/-! ## Polynomial systems -/

theorem primrec_varBound : Primrec varBound := by
  have hl : Primrec fun l : List MvP => l.flatMap fun p => p.map fun m => m.2.length :=
    Primrec.list_flatMap (f := fun l : List MvP => l)
      (g := fun (_ : List MvP) (p : MvP) => p.map fun m => m.2.length) Primrec.id
      (Primrec.list_map (f := fun r : List MvP × MvP => r.2)
        (g := fun (_ : List MvP × MvP) (m : ℤ × List ℕ) => m.2.length) Primrec.snd
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)).to₂).to₂
  have hm : Primrec fun r : List MvP × ℕ × ℕ => max r.2.1 r.2.2 :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr
    (f := fun l : List MvP => l.flatMap fun p => p.map fun m => m.2.length)
    (g := fun _ : List MvP => (0 : ℕ)) (h := fun (_ : List MvP) (q : ℕ × ℕ) => max q.1 q.2)
    hl (Primrec.const (0 : ℕ)) hm.to₂).of_eq fun _ => rfl

theorem primrec_systemPrenex : Primrec systemPrenex := by
  have h1 : Primrec fun S : List MvP × List MvP =>
      (List.range (varBound (S.1 ++ S.2))).map fun i => (true, i) :=
    Primrec.list_map (f := fun S : List MvP × List MvP => List.range (varBound (S.1 ++ S.2)))
      (g := fun (_ : List MvP × List MvP) (i : ℕ) => (true, i))
      (Primrec.list_range.comp
        (primrec_varBound.comp (Primrec.list_append.comp Primrec.fst Primrec.snd)))
      (Primrec.pair (Primrec.const true) Primrec.snd).to₂
  have h2 : Primrec fun S : List MvP × List MvP => S.1.map fun p => ((false, p) : Atom) :=
    Primrec.list_map (f := fun S : List MvP × List MvP => S.1)
      (g := fun (_ : List MvP × List MvP) (p : MvP) => ((false, p) : Atom)) Primrec.fst
      (Primrec.pair (Primrec.const false) Primrec.snd).to₂
  exact (Primrec.pair h1
    (primrec_qfAnd.comp
      (Primrec.list_cons.comp h2 (Primrec.const ([] : List (List Atom))))
      (primrec_nonnegQF.comp Primrec.snd))).of_eq fun _ => rfl

end GroupApproximation.Full.NN11b.PR

namespace GroupApproximation.Full.NN11b

/-- The decision procedure for prenex sentences over the real closed field is computable
(`thm:mf-arithmetic`, `non_mf_group_notes.tex`, step "Fixed-dimensional feasibility is
decidable over the real closed field"; Basu--Pollack--Roy Ch. 2, Ch. 10). -/
theorem computable_decidePrenex : Computable decidePrenex :=
  PR.primrec_decidePrenex.to_comp

/-- The translation of a polynomial system into an existential prenex sentence is
computable (`thm:mf-arithmetic`, `non_mf_group_notes.tex`). -/
theorem computable_systemPrenex : Computable systemPrenex :=
  PR.primrec_systemPrenex.to_comp

end GroupApproximation.Full.NN11b
