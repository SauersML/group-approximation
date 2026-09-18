import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Computability.ChainOps

/-!
# The Ben-Or--Kozen--Reif step is primitive recursive

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Eliminating one existential
quantifier from a conjunction of atoms (Basu--Pollack--Roy, *Algorithms in Real Algebraic
Geometry*, Ch. 2 and Ch. 10) combines Tarski queries with the Ben-Or--Kozen--Reif weights.
This file proves the exponent vectors `expVecs`, the weights `weight1`, `weight`,
`weightedSum`, the sum `bkrTree`, the atom normalization `atomTree`, `collectAtoms`,
`conjDecide` and the elimination step `conjTree` primitive recursive.
-/

namespace GroupApproximation.Full.NN11b.PR

/-! ## Weights -/

/-- `expVecs` as an iterate. -/
theorem expVecs_eq (m : ℕ) :
    expVecs m
      = (fun l : List (List ℕ) => l.flatMap fun e => [0 :: e, 1 :: e, 2 :: e])^[m] [[]] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact (congrArg (fun l : List (List ℕ) => l.flatMap fun e => [0 :: e, 1 :: e, 2 :: e])
      ih).trans (Function.iterate_succ_apply'
        (fun l : List (List ℕ) => l.flatMap fun e => [0 :: e, 1 :: e, 2 :: e]) m [[]]).symm

theorem primrec_expVecs : Primrec expVecs :=
  (Primrec.nat_iterate (f := fun m : ℕ => m) (g := fun _ : ℕ => ([[]] : List (List ℕ)))
    (h := fun (_ : ℕ) (l : List (List ℕ)) => l.flatMap fun e => [0 :: e, 1 :: e, 2 :: e])
    Primrec.id (Primrec.const ([[]] : List (List ℕ)))
    (Primrec.list_flatMap (f := fun r : ℕ × List (List ℕ) => r.2)
      (g := fun (_ : ℕ × List (List ℕ)) (e : List ℕ) => [0 :: e, 1 :: e, 2 :: e])
      Primrec.snd
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const (0 : ℕ)) Primrec.snd)
        (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const (1 : ℕ)) Primrec.snd)
          (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const (2 : ℕ)) Primrec.snd)
            (Primrec.const ([] : List (List ℕ)))))).to₂).to₂).of_eq fun m =>
    (expVecs_eq m).symm

theorem primrec_weight1 : Primrec₂ weight1 := by
  show Primrec fun p : ℤ × ℕ => weight1 p.1 p.2
  have hs0 : PrimrecPred fun p : ℤ × ℕ => p.1 = 0 :=
    Primrec.eq.comp Primrec.fst (Primrec.const (0 : ℤ))
  have hs1 : PrimrecPred fun p : ℤ × ℕ => p.1 = 1 :=
    Primrec.eq.comp Primrec.fst (Primrec.const (1 : ℤ))
  have hk0 : PrimrecPred fun p : ℤ × ℕ => p.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const (0 : ℕ))
  have hk1 : PrimrecPred fun p : ℤ × ℕ => p.2 = 1 :=
    Primrec.eq.comp Primrec.snd (Primrec.const (1 : ℕ))
  exact (Primrec.ite hs0
    (Primrec.ite hk0 (Primrec.const (2 : ℤ))
      (Primrec.ite hk1 (Primrec.const (0 : ℤ)) (Primrec.const (-2 : ℤ))))
    (Primrec.ite hs1
      (Primrec.ite hk0 (Primrec.const (0 : ℤ)) (Primrec.const (1 : ℤ)))
      (Primrec.ite hk0 (Primrec.const (0 : ℤ))
        (Primrec.ite hk1 (Primrec.const (-1 : ℤ)) (Primrec.const (1 : ℤ)))))).of_eq
    fun _ => rfl

theorem primrec_weight : Primrec₂ weight :=
  zipRec₀ (F := weight) (c := (1 : ℤ))
    (H := fun q : ℤ × ℕ × ℤ => weight1 q.1 q.2.1 * q.2.2)
    (primrec_int_mul.comp (primrec_weight1.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
    (fun ys => by cases ys <;> rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem primrec_weightedSum :
    Primrec fun p : List ℤ × List (List ℕ) × List ℤ => weightedSum p.1 p.2.1 p.2.2 :=
  zipRec (F := weightedSum) (c := fun _ : List ℤ => (0 : ℤ))
    (H := fun (σ : List ℤ) (q : List ℕ × ℤ × ℤ) => weight σ q.1 * q.2.1 + q.2.2)
    (Primrec.const (0 : ℤ))
    (Higman.primrec2_int_add.comp
      (primrec_int_mul.comp (primrec_weight.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
    (fun _ ys => by cases ys <;> rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

theorem primrec_bkrTree :
    Primrec fun p : List MvP × List (List MvP) × List ℤ => bkrTree p.1 p.2.1 p.2.2 :=
  (primrec_tmap (δ := List MvP × List (List MvP) × List ℤ) (α := List ℤ) (β := ℤ)
    (f := fun (p : List MvP × List (List MvP) × List ℤ) (zs : List ℤ) =>
      weightedSum p.2.2 (expVecs p.2.1.length) zs)
    (t := fun p : List MvP × List (List MvP) × List ℤ =>
      tseq ((expVecs p.2.1.length).map fun e => taqTree p.1 (upMul (upDeriv p.1) (prodPowUP p.2.1 e))))
    (primrec_weightedSum.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (primrec_expVecs.comp
            (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
          Primrec.snd))).to₂
    ((primrec_tseq (α := ℤ)).comp
      (Primrec.list_map (f := fun p : List MvP × List (List MvP) × List ℤ =>
          expVecs p.2.1.length)
        (g := fun (p : List MvP × List (List MvP) × List ℤ) (e : List ℕ) =>
          taqTree p.1 (upMul (upDeriv p.1) (prodPowUP p.2.1 e)))
        (primrec_expVecs.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
        (primrec_taqTree.comp (Primrec.fst.comp Primrec.fst)
          (primrec_upMul.comp (primrec_upDeriv.comp (Primrec.fst.comp Primrec.fst))
            (primrec_prodPowUP.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
              Primrec.snd))).to₂))).of_eq fun _ => rfl

/-! ## Atoms -/

theorem primrec_atomTree : Primrec₂ atomTree := by
  show Primrec fun p : ℕ × Atom => atomTree p.1 p.2
  exact (primrec_normUP.comp (primrec_coeffX.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).of_eq
    fun _ => rfl

theorem primrec_collectAtoms_step :
    Primrec fun q : Atom × Option NForm × Option (List (ℤ × NForm)) =>
      q.2.1.elim (bif q.1.1 then none else q.2.2) fun n =>
        q.2.2.map (List.cons (bif q.1.1 then 1 else 0, n)) :=
  primrec_option_elim
    (o := fun q : Atom × Option NForm × Option (List (ℤ × NForm)) => q.2.1)
    (d := fun q : Atom × Option NForm × Option (List (ℤ × NForm)) =>
      bif q.1.1 then none else q.2.2)
    (g := fun (q : Atom × Option NForm × Option (List (ℤ × NForm))) (n : NForm) =>
      q.2.2.map (List.cons (bif q.1.1 then 1 else 0, n)))
    (Primrec.fst.comp Primrec.snd)
    (Primrec.cond (Primrec.fst.comp Primrec.fst)
      (Primrec.const (none : Option (List (ℤ × NForm)))) (Primrec.snd.comp Primrec.snd))
    (Primrec.option_map
      (f := fun r : (Atom × Option NForm × Option (List (ℤ × NForm))) × NForm => r.1.2.2)
      (g := fun (r : (Atom × Option NForm × Option (List (ℤ × NForm))) × NForm)
        (l : List (ℤ × NForm)) => (bif r.1.1.1 then 1 else 0, r.2) :: l)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp
        (Primrec.pair
          (Primrec.cond (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.const (1 : ℤ)) (Primrec.const (0 : ℤ)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd).to₂).to₂

theorem primrec_collectAtoms : Primrec₂ collectAtoms :=
  zipRec₀ (F := collectAtoms) (c := some ([] : List (ℤ × NForm)))
    (H := fun q : Atom × Option NForm × Option (List (ℤ × NForm)) =>
      q.2.1.elim (bif q.1.1 then none else q.2.2) fun n =>
        q.2.2.map (List.cons (bif q.1.1 then 1 else 0, n)))
    primrec_collectAtoms_step
    (fun ys => by rcases ys with _ | ⟨_ | _, _⟩ <;> rfl)
    (fun x _ => by rcases x with ⟨_ | _, _⟩ <;> rfl)
    (fun x _ y _ => by rcases x with ⟨_ | _, _⟩ <;> rcases y with _ | _ <;> rfl)

/-! ## Deciding a conjunction -/

theorem primrec_conjDecide_else :
    Primrec fun d : List (ℤ × NForm) =>
      tmap (fun z : ℤ × ℤ => decide (0 < z.1) || decide (0 < z.2))
        (tbind (bkrTree (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))
            (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)) fun z1 =>
          tmap (Prod.mk z1) (bkrTree (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
            (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst))) := by
  have hus : Primrec fun d : List (ℤ × NForm) => d.map fun x => x.2.1 ++ [x.2.2.1] :=
    Primrec.list_map (f := fun d : List (ℤ × NForm) => d)
      (g := fun (_ : List (ℤ × NForm)) (x : ℤ × NForm) => x.2.1 ++ [x.2.2.1]) Primrec.id
      (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.const ([] : List MvP)))).to₂
  have hσ : Primrec fun d : List (ℤ × NForm) => d.map Prod.fst :=
    (Primrec.list_map (f := fun d : List (ℤ × NForm) => d)
      (g := fun (_ : List (ℤ × NForm)) (x : ℤ × NForm) => x.1) Primrec.id
      (Primrec.fst.comp Primrec.snd).to₂).of_eq fun _ => rfl
  exact primrec_tmap (α := ℤ × ℤ) (β := Bool)
    (f := fun (_ : List (ℤ × NForm)) (z : ℤ × ℤ) => decide (0 < z.1) || decide (0 < z.2))
    (t := fun d : List (ℤ × NForm) =>
      tbind (bkrTree (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)) fun z1 =>
        tmap (Prod.mk z1) (bkrTree (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)))
    (Primrec.or.comp
      (primrec2_int_decide_lt.comp (Primrec.const (0 : ℤ)) (Primrec.fst.comp Primrec.snd))
      (primrec2_int_decide_lt.comp (Primrec.const (0 : ℤ)) (Primrec.snd.comp Primrec.snd))).to₂
    (primrec_tbind (α := ℤ) (β := ℤ × ℤ)
      (f := fun d : List (ℤ × NForm) =>
        bkrTree (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst))
      (g := fun (d : List (ℤ × NForm)) (z1 : ℤ) =>
        tmap (Prod.mk z1) (bkrTree (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)))
      (primrec_bkrTree.comp (Primrec.pair (primrec_prodUP.comp hus) (Primrec.pair hus hσ)))
      (primrec_tmap (α := ℤ) (β := ℤ × ℤ)
        (f := fun (s : List (ℤ × NForm) × ℤ) (z2 : ℤ) => (s.2, z2))
        (t := fun s : List (ℤ × NForm) × ℤ =>
          bkrTree (upDeriv (prodUP (s.1.map fun x => x.2.1 ++ [x.2.2.1])))
            (s.1.map fun x => x.2.1 ++ [x.2.2.1]) (s.1.map Prod.fst))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
        (primrec_bkrTree.comp
          (Primrec.pair (primrec_upDeriv.comp (primrec_prodUP.comp (hus.comp Primrec.fst)))
            (Primrec.pair (hus.comp Primrec.fst) (hσ.comp Primrec.fst))))).to₂)

theorem primrec_conjDecide : Primrec conjDecide := by
  have hσ : Primrec fun d : List (ℤ × NForm) => d.map Prod.fst :=
    (Primrec.list_map (f := fun d : List (ℤ × NForm) => d)
      (g := fun (_ : List (ℤ × NForm)) (x : ℤ × NForm) => x.1) Primrec.id
      (Primrec.fst.comp Primrec.snd).to₂).of_eq fun _ => rfl
  have hA : Primrec fun d : List (ℤ × NForm) => d.map fun x => bsgn x.2.2.2 :=
    Primrec.list_map (f := fun d : List (ℤ × NForm) => d)
      (g := fun (_ : List (ℤ × NForm)) (x : ℤ × NForm) => bsgn x.2.2.2) Primrec.id
      (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  have hB : Primrec fun d : List (ℤ × NForm) =>
      d.map fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length :=
    Primrec.list_map (f := fun d : List (ℤ × NForm) => d)
      (g := fun (_ : List (ℤ × NForm)) (x : ℤ × NForm) => bsgn x.2.2.2 * (-1) ^ x.2.1.length)
      Primrec.id
      (primrec_int_mul.comp
        (primrec_bsgn.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (primrec_neg_one_pow.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))).to₂
  have hc : PrimrecPred fun d : List (ℤ × NForm) =>
      d.map (fun x => bsgn x.2.2.2) = d.map Prod.fst ∨
        d.map (fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length) = d.map Prod.fst :=
    PrimrecPred.or (Primrec.eq.comp hA hσ) (Primrec.eq.comp hB hσ)
  exact (Primrec.ite hc (Primrec.const (tpure true)) primrec_conjDecide_else).of_eq fun _ => rfl

theorem primrec_conjTree : Primrec₂ conjTree := by
  show Primrec fun p : ℕ × List Atom => conjTree p.1 p.2
  exact (primrec_tbind (α := List (Option NForm)) (β := Bool)
    (f := fun p : ℕ × List Atom => tseq (p.2.map fun a => atomTree p.1 a))
    (g := fun (p : ℕ × List Atom) (os : List (Option NForm)) =>
      (collectAtoms p.2 os).elim (tpure false) fun l => conjDecide l)
    ((primrec_tseq (α := Option NForm)).comp
      (Primrec.list_map (f := fun p : ℕ × List Atom => p.2)
        (g := fun (p : ℕ × List Atom) (a : Atom) => atomTree p.1 a) Primrec.snd
        (primrec_atomTree.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂))
    (primrec_option_elim
      (o := fun r : (ℕ × List Atom) × List (Option NForm) => collectAtoms r.1.2 r.2)
      (d := fun _ : (ℕ × List Atom) × List (Option NForm) => tpure false)
      (g := fun (_ : (ℕ × List Atom) × List (Option NForm)) (l : List (ℤ × NForm)) =>
        conjDecide l)
      (primrec_collectAtoms.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const (tpure false)) (primrec_conjDecide.comp Primrec.snd).to₂).to₂).of_eq
    fun _ => rfl

end GroupApproximation.Full.NN11b.PR
