import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Builders
import Mathlib.Computability.Primrec.List

/-!
# Primitive recursiveness of the polynomial builders (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

The translation of the literal predicate into a neutral polynomial system is a
computable function. This file proves that the compiler `compileSystem` from complex to
real systems, and the elementary builders of `Builders.lean`, are primitive recursive.
Every statement is in the "parametrised" form `Primrec fun x => builder (f x) …`, so
that they compose directly.
-/

namespace GroupApproximation.Full.NN02c

variable {α : Type*} [Primcodable α]

/-! ### Real polynomials and the compiler -/

theorem primrec_negCoef {c : α → Coef} (hc : Primrec c) : Primrec fun x => negCoef (c x) := by
  show Primrec fun x => ((!(c x).1, (c x).2) : Coef)
  exact Primrec.pair (Primrec.not.comp (Primrec.fst.comp hc)) (Primrec.snd.comp hc)

theorem primrec_mulVar {j : α → ℕ} {p : α → Poly} (hj : Primrec j) (hp : Primrec p) :
    Primrec fun x => mulVar (j x) (p x) := by
  show Primrec fun x => (p x).map fun m => (m.1, j x :: m.2)
  have h2 : Primrec fun q : α × (Coef × List ℕ) => ((q.2.1, j q.1 :: q.2.2) : Coef × List ℕ) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (hj.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map hp h2

theorem primrec_negPoly {p : α → Poly} (hp : Primrec p) : Primrec fun x => negPoly (p x) := by
  show Primrec fun x => (p x).map fun m => (negCoef m.1, m.2)
  have h2 : Primrec fun q : α × (Coef × List ℕ) => ((negCoef q.2.1, q.2.2) : Coef × List ℕ) :=
    Primrec.pair (primrec_negCoef (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_map hp h2

theorem primrec_stepMono {a : α → ℕ × Bool} {rs : α → Poly × Poly} (ha : Primrec a)
    (hrs : Primrec rs) : Primrec fun x => stepMono (a x) (rs x) := by
  show Primrec fun x =>
    bif (a x).2 then
      (mulVar (2 * (a x).1) (rs x).1 ++ mulVar (2 * (a x).1 + 1) (rs x).2,
        mulVar (2 * (a x).1) (rs x).2 ++ negPoly (mulVar (2 * (a x).1 + 1) (rs x).1))
    else
      (mulVar (2 * (a x).1) (rs x).1 ++ negPoly (mulVar (2 * (a x).1 + 1) (rs x).2),
        mulVar (2 * (a x).1) (rs x).2 ++ mulVar (2 * (a x).1 + 1) (rs x).1)
  have h2 : Primrec fun x => 2 * (a x).1 :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp ha)
  have h3 : Primrec fun x => 2 * (a x).1 + 1 := Primrec.nat_add.comp h2 (Primrec.const 1)
  have hr1 : Primrec fun x => (rs x).1 := Primrec.fst.comp hrs
  have hr2 : Primrec fun x => (rs x).2 := Primrec.snd.comp hrs
  exact Primrec.cond (Primrec.snd.comp ha)
    (Primrec.pair (Primrec.list_append.comp (primrec_mulVar h2 hr1) (primrec_mulVar h3 hr2))
      (Primrec.list_append.comp (primrec_mulVar h2 hr2) (primrec_negPoly (primrec_mulVar h3 hr1))))
    (Primrec.pair (Primrec.list_append.comp (primrec_mulVar h2 hr1)
        (primrec_negPoly (primrec_mulVar h3 hr2)))
      (Primrec.list_append.comp (primrec_mulVar h2 hr2) (primrec_mulVar h3 hr1)))

theorem primrec_compileMono {c : α → Coef} {l : α → List (ℕ × Bool)} (hc : Primrec c)
    (hl : Primrec l) : Primrec fun x => compileMono (c x) (l x) := by
  show Primrec fun x => (l x).foldr stepMono (([(c x, [])], []) : Poly × Poly)
  have hg : Primrec fun x => (([(c x, [])], []) : Poly × Poly) :=
    Primrec.pair (Primrec.list_cons.comp (Primrec.pair hc (Primrec.const [])) (Primrec.const []))
      (Primrec.const [])
  have hh : Primrec fun q : α × ((ℕ × Bool) × (Poly × Poly)) => stepMono q.2.1 q.2.2 :=
    primrec_stepMono (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr
    (h := fun (_ : α) (bs : (ℕ × Bool) × (Poly × Poly)) => stepMono bs.1 bs.2) hl hg hh

theorem primrec_compileRe {p : α → CPoly} (hp : Primrec p) : Primrec fun x => compileRe (p x) := by
  show Primrec fun x => (p x).flatMap fun m => (compileMono m.1 m.2).1
  have h2 : Primrec fun q : α × (Coef × List (ℕ × Bool)) => (compileMono q.2.1 q.2.2).1 :=
    Primrec.fst.comp
      (primrec_compileMono (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_flatMap hp h2

theorem primrec_compileIm {p : α → CPoly} (hp : Primrec p) : Primrec fun x => compileIm (p x) := by
  show Primrec fun x => (p x).flatMap fun m => (compileMono m.1 m.2).2
  have h2 : Primrec fun q : α × (Coef × List (ℕ × Bool)) => (compileMono q.2.1 q.2.2).2 :=
    Primrec.snd.comp
      (primrec_compileMono (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_flatMap hp h2

theorem primrec_compileSystem {S : α → CSystem} (hS : Primrec S) :
    Primrec fun x => compileSystem (S x) := by
  show Primrec fun x => (((S x).1.flatMap fun p => [compileRe p, compileIm p],
    (S x).2.map fun p => compileRe p) : PolySystem)
  have h1 : Primrec fun q : α × CPoly => ([compileRe q.2, compileIm q.2] : List Poly) :=
    Primrec.list_cons.comp (primrec_compileRe Primrec.snd)
      (Primrec.list_cons.comp (primrec_compileIm Primrec.snd) (Primrec.const []))
  have h2 : Primrec fun q : α × CPoly => compileRe q.2 := primrec_compileRe Primrec.snd
  exact Primrec.pair (Primrec.list_flatMap (Primrec.fst.comp hS) h1)
    (Primrec.list_map (Primrec.snd.comp hS) h2)

/-! ### Builders -/

theorem primrec_cv {b e j k : α → ℕ} (hb : Primrec b) (he : Primrec e) (hj : Primrec j)
    (hk : Primrec k) : Primrec fun x => cv (b x) (e x) (j x) (k x) := by
  show Primrec fun x => Nat.pair (b x) (Nat.pair (e x) (Nat.pair (j x) (k x)))
  exact Primrec₂.natPair.comp hb (Primrec₂.natPair.comp he (Primrec₂.natPair.comp hj hk))

theorem primrec_kdelta {j k : α → ℕ} (hj : Primrec j) (hk : Primrec k) :
    Primrec fun x => kdelta (j x) (k x) := by
  show Primrec fun x => if j x = k x then 1 else 0
  exact Primrec.ite (Primrec.eq.comp hj hk) (Primrec.const 1) (Primrec.const 0)

theorem primrec_negC {p : α → CPoly} (hp : Primrec p) : Primrec fun x => negC (p x) := by
  show Primrec fun x => (p x).map fun m => (negCoef m.1, m.2)
  have h2 : Primrec fun q : α × (Coef × List (ℕ × Bool)) =>
      ((negCoef q.2.1, q.2.2) : Coef × List (ℕ × Bool)) :=
    Primrec.pair (primrec_negCoef (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_map hp h2

theorem primrec_diffC {p q : α → CPoly} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => diffC (p x) (q x) := by
  show Primrec fun x => p x ++ negC (q x)
  exact Primrec.list_append.comp hp (primrec_negC hq)

theorem primrec_scaledVarC {n : α → ℕ} {a : α → ℕ × Bool} (hn : Primrec n) (ha : Primrec a) :
    Primrec fun x => scaledVarC (n x) (a x) := by
  show Primrec fun x => ([((false, n x), [a x])] : CPoly)
  exact Primrec.list_cons.comp
    (Primrec.pair (Primrec.pair (Primrec.const false) hn)
      (Primrec.list_cons.comp ha (Primrec.const [])))
    (Primrec.const [])

theorem primrec_varC {a : α → ℕ × Bool} (ha : Primrec a) : Primrec fun x => varC (a x) := by
  show Primrec fun x => scaledVarC 1 (a x)
  exact primrec_scaledVarC (Primrec.const 1) ha

theorem primrec_constC {n : α → ℕ} (hn : Primrec n) : Primrec fun x => constC (n x) := by
  show Primrec fun x => ([((false, n x), [])] : CPoly)
  exact Primrec.list_cons.comp (Primrec.pair (Primrec.pair (Primrec.const false) hn)
    (Primrec.const [])) (Primrec.const [])

theorem primrec_sumProd {n d : α → ℕ} {f g : α → ℕ → ℕ × Bool} (hn : Primrec n)
    (hd : Primrec d) (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec fun x => sumProd (n x) (d x) (f x) (g x) := by
  show Primrec fun x => (List.range (d x)).map fun l =>
    (((false, n x), [f x l, g x l]) : Coef × List (ℕ × Bool))
  have hf' : Primrec fun q : α × ℕ => f q.1 q.2 := hf
  have hg' : Primrec fun q : α × ℕ => g q.1 q.2 := hg
  have h2 : Primrec fun q : α × ℕ =>
      (((false, n q.1), [f q.1 q.2, g q.1 q.2]) : Coef × List (ℕ × Bool)) :=
    Primrec.pair (Primrec.pair (Primrec.const false) (hn.comp Primrec.fst))
      (Primrec.list_cons.comp hf' (Primrec.list_cons.comp hg' (Primrec.const [])))
  exact Primrec.list_map (Primrec.list_range.comp hd) h2

/-- A letter `(cv b e l p, t)` depending on the summation index `l`. -/
theorem primrec_litFun {b e p : α → ℕ} (t : Bool) (hb : Primrec b) (he : Primrec e)
    (hp : Primrec p) : Primrec₂ fun (x : α) (l : ℕ) => (cv (b x) (e x) l (p x), t) := by
  show Primrec fun q : α × ℕ => (cv (b q.1) (e q.1) q.2 (p q.1), t)
  exact Primrec.pair
    (primrec_cv (hb.comp Primrec.fst) (he.comp Primrec.fst) Primrec.snd (hp.comp Primrec.fst))
    (Primrec.const t)

theorem primrec_grid {d : α → ℕ} {F : α → ℕ → ℕ → CPoly} (hd : Primrec d)
    (hF : Primrec fun w : α × ℕ × ℕ => F w.1 w.2.1 w.2.2) :
    Primrec fun x => grid (d x) (F x) := by
  show Primrec fun x => (List.range (d x)).flatMap fun j => (List.range (d x)).map fun k => F x j k
  have hpair : Primrec fun q : (α × ℕ) × ℕ => ((q.1.1, q.1.2, q.2) : α × ℕ × ℕ) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have h0 : Primrec fun q : (α × ℕ) × ℕ => F q.1.1 q.1.2 q.2 := hF.comp hpair
  have h1 : Primrec fun y : α × ℕ => (List.range (d y.1)).map fun k => F y.1 y.2 k :=
    Primrec.list_map (Primrec.list_range.comp (hd.comp Primrec.fst)) h0
  exact Primrec.list_flatMap (Primrec.list_range.comp hd) h1

end GroupApproximation.Full.NN02c
