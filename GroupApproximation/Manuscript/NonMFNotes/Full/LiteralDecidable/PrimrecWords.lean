import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.PrimrecPoly
import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Encoding

/-!
# Primitive recursiveness of the constraint families (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

The families of complex polynomial constraints of `Encoding.lean` (unitarity of the
generators, word values, relator defects, the test word) are primitive recursive functions
of their parameters. Word values are handled by `Primrec.list_rec` (`recOn_wordCons`).
-/

namespace GroupApproximation.Full.NN02c

variable {α : Type*} [Primcodable α]

theorem primrec_scale : Primrec scale := by
  show Primrec fun n : ℕ => (fun x : ℕ => 2 * x)^[n] 1024
  have h2 : Primrec fun p : ℕ × ℕ => 2 * p.2 := Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  exact Primrec.nat_iterate (f := fun n : ℕ => n) (g := fun _ : ℕ => 1024)
    (h := fun (_ : ℕ) (x : ℕ) => 2 * x) Primrec.id (Primrec.const 1024) h2

theorem primrec_letterLit {G : α → ℕ} {a : α → ℕ × Bool} {J L : α → ℕ} (hG : Primrec G)
    (ha : Primrec a) (hJ : Primrec J) (hL : Primrec L) :
    Primrec fun x => letterLit (G x) (a x) (J x) (L x) := by
  show Primrec fun x => bif (a x).2 then ((cv 0 ((a x).1 % G x) (J x) (L x), false) : ℕ × Bool)
    else (cv 0 ((a x).1 % G x) (L x) (J x), true)
  have hm : Primrec fun x => (a x).1 % G x := Primrec.nat_mod.comp (Primrec.fst.comp ha) hG
  exact Primrec.cond (Primrec.snd.comp ha)
    (Primrec.pair (primrec_cv (Primrec.const 0) hm hJ hL) (Primrec.const false))
    (Primrec.pair (primrec_cv (Primrec.const 0) hm hL hJ) (Primrec.const true))

theorem primrec_unitaryCons {G D : α → ℕ} (hG : Primrec G) (hD : Primrec D) :
    Primrec fun x => unitaryCons (G x) (D x) := by
  show Primrec fun x => (List.range (G x)).flatMap fun i => grid (D x) fun p q =>
    diffC (sumProd 1 (D x) (fun l => (cv 0 i l p, true)) (fun l => (cv 0 i l q, false)))
      (constC (kdelta p q))
  have hi : Primrec fun w : (α × ℕ) × ℕ × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
  have hp : Primrec fun w : (α × ℕ) × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hq : Primrec fun w : (α × ℕ) × ℕ × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have hf1 : Primrec₂ fun (w : (α × ℕ) × ℕ × ℕ) (l : ℕ) =>
      ((cv 0 w.1.2 l w.2.1, true) : ℕ × Bool) :=
    primrec_litFun true (Primrec.const 0) hi hp
  have hg1 : Primrec₂ fun (w : (α × ℕ) × ℕ × ℕ) (l : ℕ) =>
      ((cv 0 w.1.2 l w.2.2, false) : ℕ × Bool) :=
    primrec_litFun false (Primrec.const 0) hi hq
  have hF : Primrec fun w : (α × ℕ) × ℕ × ℕ =>
      diffC (sumProd 1 (D w.1.1) (fun l => (cv 0 w.1.2 l w.2.1, true))
          (fun l => (cv 0 w.1.2 l w.2.2, false)))
        (constC (kdelta w.2.1 w.2.2)) :=
    primrec_diffC
      (primrec_sumProd (Primrec.const 1) (hD.comp (Primrec.fst.comp Primrec.fst)) hf1 hg1)
      (primrec_constC (primrec_kdelta hp hq))
  have h1 : Primrec₂ fun (x : α) (i : ℕ) => grid (D x) fun p q =>
      diffC (sumProd 1 (D x) (fun l => (cv 0 i l p, true)) (fun l => (cv 0 i l q, false)))
        (constC (kdelta p q)) :=
    primrec_grid (F := fun (y : α × ℕ) (p q : ℕ) =>
      diffC (sumProd 1 (D y.1) (fun l => (cv 0 y.2 l p, true)) (fun l => (cv 0 y.2 l q, false)))
        (constC (kdelta p q))) (hD.comp Primrec.fst) hF
  exact Primrec.list_flatMap (Primrec.list_range.comp hG) h1

theorem primrec_wordBase {D : α → ℕ} (hD : Primrec D) : Primrec fun x => wordBase (D x) := by
  show Primrec fun x => grid (D x) fun j k =>
    diffC (varC (cv 1 (Encodable.encode ([] : List (ℕ × Bool))) j k, false)) (constC (kdelta j k))
  have hj : Primrec fun w : α × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun w : α × ℕ × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have hF : Primrec fun w : α × ℕ × ℕ =>
      diffC (varC (cv 1 (Encodable.encode ([] : List (ℕ × Bool))) w.2.1 w.2.2, false))
        (constC (kdelta w.2.1 w.2.2)) :=
    primrec_diffC
      (primrec_varC (Primrec.pair (primrec_cv (Primrec.const 1)
        (Primrec.const (Encodable.encode ([] : List (ℕ × Bool)))) hj hk) (Primrec.const false)))
      (primrec_constC (primrec_kdelta hj hk))
  exact primrec_grid (F := fun (_ : α) (j k : ℕ) =>
    diffC (varC (cv 1 (Encodable.encode ([] : List (ℕ × Bool))) j k, false))
      (constC (kdelta j k))) hD hF

theorem primrec_wordStep {G D : α → ℕ} {a : α → ℕ × Bool} {u : α → List (ℕ × Bool)}
    (hG : Primrec G) (hD : Primrec D) (ha : Primrec a) (hu : Primrec u) :
    Primrec fun x => wordStep (G x) (D x) (a x) (u x) := by
  show Primrec fun x => grid (D x) fun j k =>
    diffC (varC (cv 1 (Encodable.encode (a x :: u x)) j k, false))
      (sumProd 1 (D x) (fun l => letterLit (G x) (a x) j l)
        (fun l => (cv 1 (Encodable.encode (u x)) l k, false)))
  have hj : Primrec fun w : α × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun w : α × ℕ × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have he1 : Primrec fun w : α × ℕ × ℕ => Encodable.encode (a w.1 :: u w.1) :=
    Primrec.encode.comp (Primrec.list_cons.comp (ha.comp Primrec.fst) (hu.comp Primrec.fst))
  have he2 : Primrec fun w : α × ℕ × ℕ => Encodable.encode (u w.1) :=
    Primrec.encode.comp (hu.comp Primrec.fst)
  have hf1 : Primrec₂ fun (w : α × ℕ × ℕ) (l : ℕ) => letterLit (G w.1) (a w.1) w.2.1 l :=
    primrec_letterLit (hG.comp (Primrec.fst.comp Primrec.fst))
      (ha.comp (Primrec.fst.comp Primrec.fst)) (hj.comp Primrec.fst) Primrec.snd
  have hg1 : Primrec₂ fun (w : α × ℕ × ℕ) (l : ℕ) =>
      ((cv 1 (Encodable.encode (u w.1)) l w.2.2, false) : ℕ × Bool) :=
    primrec_litFun false (Primrec.const 1) he2 hk
  have hF : Primrec fun w : α × ℕ × ℕ =>
      diffC (varC (cv 1 (Encodable.encode (a w.1 :: u w.1)) w.2.1 w.2.2, false))
        (sumProd 1 (D w.1) (fun l => letterLit (G w.1) (a w.1) w.2.1 l)
          (fun l => (cv 1 (Encodable.encode (u w.1)) l w.2.2, false))) :=
    primrec_diffC
      (primrec_varC (Primrec.pair (primrec_cv (Primrec.const 1) he1 hj hk) (Primrec.const false)))
      (primrec_sumProd (Primrec.const 1) (hD.comp Primrec.fst) hf1 hg1)
  exact primrec_grid (F := fun (x : α) (j k : ℕ) =>
    diffC (varC (cv 1 (Encodable.encode (a x :: u x)) j k, false))
      (sumProd 1 (D x) (fun l => letterLit (G x) (a x) j l)
        (fun l => (cv 1 (Encodable.encode (u x)) l k, false)))) hD hF

/-- `wordCons` as a list recursion. -/
theorem recOn_wordCons (G D : ℕ) (v : List (ℕ × Bool)) :
    List.recOn (motive := fun _ => List CPoly) v (wordBase D)
      (fun b l (IH : List CPoly) => wordStep G D b l ++ IH) = wordCons G D v := by
  induction v with
  | nil => rfl
  | cons a v ih => exact congrArg (fun t => wordStep G D a v ++ t) ih

theorem primrec_wordCons {G D : α → ℕ} {u : α → List (ℕ × Bool)} (hG : Primrec G)
    (hD : Primrec D) (hu : Primrec u) : Primrec fun x => wordCons (G x) (D x) (u x) := by
  have hh : Primrec₂ fun (x : α) (t : (ℕ × Bool) × List (ℕ × Bool) × List CPoly) =>
      wordStep (G x) (D x) t.1 t.2.1 ++ t.2.2 :=
    Primrec.list_append.comp
      (primrec_wordStep (hG.comp Primrec.fst) (hD.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr := Primrec.list_rec (σ := List CPoly) (f := u) (g := fun x => wordBase (D x))
    (h := fun (x : α) (t : (ℕ × Bool) × List (ℕ × Bool) × List CPoly) =>
      wordStep (G x) (D x) t.1 t.2.1 ++ t.2.2) hu (primrec_wordBase hD) hh
  exact hr.of_eq fun x => recOn_wordCons (G x) (D x) (u x)

theorem primrec_scaledDefectCons {D S : α → ℕ} {r : α → List (ℕ × Bool)} (hD : Primrec D)
    (hS : Primrec S) (hr : Primrec r) : Primrec fun x => scaledDefectCons (D x) (S x) (r x) := by
  show Primrec fun x => grid (D x) fun j k =>
    diffC (varC (cv 2 (Encodable.encode (r x)) j k, false))
      (diffC (scaledVarC (S x) (cv 1 (Encodable.encode (r x)) j k, false))
        (constC (S x * kdelta j k)))
  have he : Primrec fun w : α × ℕ × ℕ => Encodable.encode (r w.1) :=
    Primrec.encode.comp (hr.comp Primrec.fst)
  have hj : Primrec fun w : α × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun w : α × ℕ × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have hS' : Primrec fun w : α × ℕ × ℕ => S w.1 := hS.comp Primrec.fst
  have hF : Primrec fun w : α × ℕ × ℕ =>
      diffC (varC (cv 2 (Encodable.encode (r w.1)) w.2.1 w.2.2, false))
        (diffC (scaledVarC (S w.1) (cv 1 (Encodable.encode (r w.1)) w.2.1 w.2.2, false))
          (constC (S w.1 * kdelta w.2.1 w.2.2))) :=
    primrec_diffC
      (primrec_varC (Primrec.pair (primrec_cv (Primrec.const 2) he hj hk) (Primrec.const false)))
      (primrec_diffC
        (primrec_scaledVarC hS'
          (Primrec.pair (primrec_cv (Primrec.const 1) he hj hk) (Primrec.const false)))
        (primrec_constC (Primrec.nat_mul.comp hS' (primrec_kdelta hj hk))))
  exact primrec_grid (F := fun (x : α) (j k : ℕ) =>
    diffC (varC (cv 2 (Encodable.encode (r x)) j k, false))
      (diffC (scaledVarC (S x) (cv 1 (Encodable.encode (r x)) j k, false))
        (constC (S x * kdelta j k)))) hD hF

theorem primrec_contractionCons {D : α → ℕ} {r : α → List (ℕ × Bool)} (hD : Primrec D)
    (hr : Primrec r) : Primrec fun x => contractionCons (D x) (r x) := by
  show Primrec fun x => grid (D x) fun j k =>
    diffC (constC (kdelta j k))
      (sumProd 1 (D x) (fun l => (cv 2 (Encodable.encode (r x)) l j, true))
          (fun l => (cv 2 (Encodable.encode (r x)) l k, false)) ++
        sumProd 1 (D x) (fun l => (cv 3 (Encodable.encode (r x)) l j, true))
          (fun l => (cv 3 (Encodable.encode (r x)) l k, false)))
  have he : Primrec fun w : α × ℕ × ℕ => Encodable.encode (r w.1) :=
    Primrec.encode.comp (hr.comp Primrec.fst)
  have hj : Primrec fun w : α × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun w : α × ℕ × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have hs : ∀ b : ℕ, Primrec fun w : α × ℕ × ℕ =>
      sumProd 1 (D w.1) (fun l => (cv b (Encodable.encode (r w.1)) l w.2.1, true))
        (fun l => (cv b (Encodable.encode (r w.1)) l w.2.2, false)) := fun b =>
    primrec_sumProd (Primrec.const 1) (hD.comp Primrec.fst)
      (primrec_litFun true (Primrec.const b) he hj) (primrec_litFun false (Primrec.const b) he hk)
  have hF : Primrec fun w : α × ℕ × ℕ =>
      diffC (constC (kdelta w.2.1 w.2.2))
        (sumProd 1 (D w.1) (fun l => (cv 2 (Encodable.encode (r w.1)) l w.2.1, true))
            (fun l => (cv 2 (Encodable.encode (r w.1)) l w.2.2, false)) ++
          sumProd 1 (D w.1) (fun l => (cv 3 (Encodable.encode (r w.1)) l w.2.1, true))
            (fun l => (cv 3 (Encodable.encode (r w.1)) l w.2.2, false))) :=
    primrec_diffC (primrec_constC (primrec_kdelta hj hk)) (Primrec.list_append.comp (hs 2) (hs 3))
  exact primrec_grid (F := fun (x : α) (j k : ℕ) =>
    diffC (constC (kdelta j k))
      (sumProd 1 (D x) (fun l => (cv 2 (Encodable.encode (r x)) l j, true))
          (fun l => (cv 2 (Encodable.encode (r x)) l k, false)) ++
        sumProd 1 (D x) (fun l => (cv 3 (Encodable.encode (r x)) l j, true))
          (fun l => (cv 3 (Encodable.encode (r x)) l k, false)))) hD hF

theorem primrec_relatorCons {G D S : α → ℕ} {r : α → List (ℕ × Bool)} (hG : Primrec G)
    (hD : Primrec D) (hS : Primrec S) (hr : Primrec r) :
    Primrec fun x => relatorCons (G x) (D x) (S x) (r x) := by
  show Primrec fun x => wordCons (G x) (D x) (r x) ++
    (scaledDefectCons (D x) (S x) (r x) ++ contractionCons (D x) (r x))
  exact Primrec.list_append.comp (primrec_wordCons hG hD hr)
    (Primrec.list_append.comp (primrec_scaledDefectCons hD hS hr) (primrec_contractionCons hD hr))

theorem primrec_xNormPoly {D : α → ℕ} (hD : Primrec D) : Primrec fun x => xNormPoly (D x) := by
  show Primrec fun x =>
    diffC (sumProd 1 (D x) (fun l => (cv 4 0 l 0, true)) (fun l => (cv 4 0 l 0, false)))
      (constC 1)
  have hf1 : Primrec₂ fun (_ : α) (l : ℕ) => ((cv 4 0 l 0, true) : ℕ × Bool) :=
    primrec_litFun true (Primrec.const 4) (Primrec.const 0) (Primrec.const 0)
  have hg1 : Primrec₂ fun (_ : α) (l : ℕ) => ((cv 4 0 l 0, false) : ℕ × Bool) :=
    primrec_litFun false (Primrec.const 4) (Primrec.const 0) (Primrec.const 0)
  exact primrec_diffC (primrec_sumProd (Primrec.const 1) hD hf1 hg1)
    (primrec_constC (Primrec.const 1))

theorem primrec_yRow {D E J : α → ℕ} (hD : Primrec D) (hE : Primrec E) (hJ : Primrec J) :
    Primrec fun x => yRow (D x) (E x) (J x) := by
  show Primrec fun x => diffC (varC (cv 5 0 (J x) 0, false))
    (diffC (sumProd 1 (D x) (fun l => (cv 1 (E x) (J x) l, false)) (fun l => (cv 4 0 l 0, false)))
      (varC (cv 4 0 (J x) 0, false)))
  have hf1 : Primrec₂ fun (x : α) (l : ℕ) => ((cv 1 (E x) (J x) l, false) : ℕ × Bool) :=
    Primrec.pair
      (primrec_cv (Primrec.const 1) (hE.comp Primrec.fst) (hJ.comp Primrec.fst) Primrec.snd)
      (Primrec.const false)
  have hg1 : Primrec₂ fun (_ : α) (l : ℕ) => ((cv 4 0 l 0, false) : ℕ × Bool) :=
    primrec_litFun false (Primrec.const 4) (Primrec.const 0) (Primrec.const 0)
  exact primrec_diffC
    (primrec_varC (Primrec.pair (primrec_cv (Primrec.const 5) (Primrec.const 0) hJ
      (Primrec.const 0)) (Primrec.const false)))
    (primrec_diffC (primrec_sumProd (Primrec.const 1) hD hf1 hg1)
      (primrec_varC (Primrec.pair (primrec_cv (Primrec.const 4) (Primrec.const 0) hJ
        (Primrec.const 0)) (Primrec.const false))))

theorem primrec_vCons {G D : α → ℕ} {v : α → List (ℕ × Bool)} (hG : Primrec G) (hD : Primrec D)
    (hv : Primrec v) : Primrec fun x => vCons (G x) (D x) (v x) := by
  show Primrec fun x => wordCons (G x) (D x) (v x) ++
    (xNormPoly (D x) :: (List.range (D x)).map (yRow (D x) (Encodable.encode (v x))))
  have hy : Primrec₂ fun (x : α) (j : ℕ) => yRow (D x) (Encodable.encode (v x)) j :=
    primrec_yRow (hD.comp Primrec.fst) (Primrec.encode.comp (hv.comp Primrec.fst)) Primrec.snd
  exact Primrec.list_append.comp (primrec_wordCons hG hD hv)
    (Primrec.list_cons.comp (primrec_xNormPoly hD)
      (Primrec.list_map (Primrec.list_range.comp hD) hy))

theorem primrec_vNonneg {D : α → ℕ} (hD : Primrec D) : Primrec fun x => vNonneg (D x) := by
  show Primrec fun x =>
    diffC (sumProd 4 (D x) (fun l => (cv 5 0 l 0, true)) (fun l => (cv 5 0 l 0, false)))
      (constC 1)
  have hf1 : Primrec₂ fun (_ : α) (l : ℕ) => ((cv 5 0 l 0, true) : ℕ × Bool) :=
    primrec_litFun true (Primrec.const 5) (Primrec.const 0) (Primrec.const 0)
  have hg1 : Primrec₂ fun (_ : α) (l : ℕ) => ((cv 5 0 l 0, false) : ℕ × Bool) :=
    primrec_litFun false (Primrec.const 5) (Primrec.const 0) (Primrec.const 0)
  exact primrec_diffC (primrec_sumProd (Primrec.const 4) hD hf1 hg1)
    (primrec_constC (Primrec.const 1))

end GroupApproximation.Full.NN02c
