import Mathlib.Computability.Primrec.List

/-!
# List recursion schemes for the decision procedure

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  The symbolic procedure of
`RCFDecision/Algo.lean` (Basu--Pollack--Roy, *Algorithms in Real Algebraic Geometry*,
Ch. 2 and Ch. 10) is written with structural recursion on one list, or simultaneously on
two lists.  This file turns such defining equations into `Primrec` statements:

* `listRec₂`, `listRec₁`: recursion on one list (with or without a parameter);
* `primrec_replicate`, `primrec_zip`;
* `zipRec`, `zipRec₀`: simultaneous recursion on two lists, stopping at the shorter one;
* `zipLong`: pointwise combination of two lists, keeping the longer tail;
* `primrec_list_any`, `primrec_list_all`, `primrec_option_elim`.
-/

namespace GroupApproximation.Full.NN11b.PR

section Equations

variable {α β γ σ : Type*}

/-- `List.replicate` as an iterate. -/
theorem replicate_eq_iterate (n : ℕ) (a : β) : List.replicate n a = (List.cons a)^[n] [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (List.cons a) ih).trans (Function.iterate_succ_apply' (List.cons a) n []).symm

/-- One step of `List.zip` as a left fold over the first list: the state is the reversed
accumulated zip and the unused part of the second list. -/
def zipStep (s : List (β × γ) × List γ) (x : β) : List (β × γ) × List γ :=
  match s.2 with
  | [] => (s.1, [])
  | y :: r => ((x, y) :: s.1, r)

theorem foldl_zipStep (xs : List β) : ∀ (acc : List (β × γ)) (ys : List γ),
    (xs.foldl zipStep (acc, ys)).1 = (List.zip xs ys).reverse ++ acc := by
  induction xs with
  | nil => intro acc ys; rfl
  | cons x xs ih =>
    intro acc ys
    cases ys with
    | nil =>
      exact (ih acc []).trans
        (congrArg (fun z : List (β × γ) => z.reverse ++ acc) (List.zip_nil_right (l := xs)))
    | cons y ys =>
      have e : List.zip (x :: xs) (y :: ys) = (x, y) :: List.zip xs ys := rfl
      refine (ih ((x, y) :: acc) ys).trans ?_
      rw [e, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem zip_eq_foldl (xs : List β) (ys : List γ) :
    List.zip xs ys = (xs.foldl zipStep (([] : List (β × γ)), ys)).1.reverse := by
  rw [foldl_zipStep xs [] ys, List.append_nil, List.reverse_reverse]

/-- Closed form of a simultaneous recursion on two lists. -/
theorem zipRec_eq {F : α → List β → List γ → σ} {c : α → σ} {H : α → β × γ × σ → σ}
    (h0 : ∀ a ys, F a [] ys = c a) (h0' : ∀ a x xs, F a (x :: xs) [] = c a)
    (h1 : ∀ a x xs y ys, F a (x :: xs) (y :: ys) = H a (x, y, F a xs ys)) (a : α)
    (xs : List β) :
    ∀ ys : List γ, F a xs ys = (List.zip xs ys).foldr (fun q s => H a (q.1, q.2, s)) (c a) := by
  induction xs with
  | nil => intro ys; exact h0 a ys
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => exact h0' a x xs
    | cons y ys => exact (h1 a x xs y ys).trans (congrArg (fun s => H a (x, y, s)) (ih ys))

/-- Closed form of a pointwise combination keeping the longer tail. -/
theorem zipLong_eq {F : List β → List β → List β} {op : β → β → β}
    (h0 : ∀ v, F [] v = v) (h0' : ∀ a u, F (a :: u) [] = a :: u)
    (h1 : ∀ a u b v, F (a :: u) (b :: v) = op a b :: F u v) (u : List β) :
    ∀ v : List β, F u v
      = (List.zip u v).map (fun p => op p.1 p.2) ++ u.drop v.length ++ v.drop u.length := by
  induction u with
  | nil =>
    intro v
    rw [List.drop_nil]
    exact h0 v
  | cons a u ih =>
    intro v
    cases v with
    | nil => exact (h0' a u).trans (List.append_nil (a :: u)).symm
    | cons b v => exact (h1 a u b v).trans (congrArg (List.cons (op a b)) (ih v))

end Equations

section Schemes

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/-- Structural recursion on a list, with a parameter. -/
theorem listRec₂ {F : α → List β → σ} {g : α → σ} {h : α → β × List β × σ → σ}
    (hg : Primrec g) (hh : Primrec₂ h) (h0 : ∀ a, F a [] = g a)
    (h1 : ∀ a b l, F a (b :: l) = h a (b, l, F a l)) : Primrec₂ F := by
  show Primrec fun p : α × List β => F p.1 p.2
  refine (Primrec.list_rec (f := fun p : α × List β => p.2) (g := fun p : α × List β => g p.1)
    (h := fun (p : α × List β) (q : β × List β × σ) => h p.1 q) Primrec.snd
    (hg.comp Primrec.fst) (hh.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
    fun p => ?_
  obtain ⟨a, l⟩ := p
  induction l with
  | nil => exact (h0 a).symm
  | cons b l ih => exact (congrArg (fun x => h a (b, l, x)) ih).trans (h1 a b l).symm

/-- Structural recursion on a list, without a parameter. -/
theorem listRec₁ {F : List β → σ} {c : σ} {h : β × List β × σ → σ} (hh : Primrec h)
    (h0 : F [] = c) (h1 : ∀ b l, F (b :: l) = h (b, l, F l)) : Primrec F := by
  refine (Primrec.list_rec (f := fun l : List β => l) (g := fun _ : List β => c)
    (h := fun (_ : List β) (q : β × List β × σ) => h q) Primrec.id (Primrec.const c)
    (hh.comp Primrec.snd).to₂).of_eq fun l => ?_
  induction l with
  | nil => exact h0.symm
  | cons b l ih => exact (congrArg (fun x => h (b, l, x)) ih).trans (h1 b l).symm

/-- `List.replicate` is primitive recursive. -/
theorem primrec_replicate : Primrec₂ fun (n : ℕ) (a : β) => List.replicate n a := by
  show Primrec fun p : ℕ × β => List.replicate p.1 p.2
  exact (Primrec.nat_iterate (f := fun p : ℕ × β => p.1) (g := fun _ : ℕ × β => ([] : List β))
    (h := fun (p : ℕ × β) (l : List β) => p.2 :: l) Primrec.fst (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p =>
      (replicate_eq_iterate p.1 p.2).symm

theorem primrec_zipStep : Primrec₂ (@zipStep β γ) := by
  show Primrec fun p : (List (β × γ) × List γ) × β => zipStep p.1 p.2
  refine (Primrec.list_casesOn (f := fun p : (List (β × γ) × List γ) × β => p.1.2)
    (g := fun p : (List (β × γ) × List γ) × β => (p.1.1, ([] : List γ)))
    (h := fun (p : (List (β × γ) × List γ) × β) (q : γ × List γ) => ((p.2, q.1) :: p.1.1, q.2))
    (Primrec.snd.comp Primrec.fst)
    (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const []))
    (Primrec.pair
      (Primrec.list_cons.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)) (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun p => ?_
  rcases p with ⟨⟨_, _ | ⟨_, _⟩⟩, _⟩ <;> rfl

/-- `List.zip` is primitive recursive. -/
theorem primrec_zip : Primrec₂ (@List.zip β γ) := by
  show Primrec fun p : List β × List γ => List.zip p.1 p.2
  exact (Primrec.list_reverse.comp (Primrec.fst.comp
    (Primrec.list_foldl (f := fun p : List β × List γ => p.1)
      (g := fun p : List β × List γ => (([] : List (β × γ)), p.2))
      (h := fun (_ : List β × List γ) (q : (List (β × γ) × List γ) × β) => zipStep q.1 q.2)
      Primrec.fst (Primrec.pair (Primrec.const []) Primrec.snd)
      (primrec_zipStep.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂))).of_eq
    fun p => (zip_eq_foldl p.1 p.2).symm

/-- Simultaneous recursion on two lists, with a parameter, stopping at the shorter list. -/
theorem zipRec {F : α → List β → List γ → σ} {c : α → σ} {H : α → β × γ × σ → σ}
    (hc : Primrec c) (hH : Primrec₂ H)
    (h0 : ∀ a ys, F a [] ys = c a) (h0' : ∀ a x xs, F a (x :: xs) [] = c a)
    (h1 : ∀ a x xs y ys, F a (x :: xs) (y :: ys) = H a (x, y, F a xs ys)) :
    Primrec fun p : α × List β × List γ => F p.1 p.2.1 p.2.2 := by
  refine (Primrec.list_foldr (f := fun p : α × List β × List γ => List.zip p.2.1 p.2.2)
    (g := fun p : α × List β × List γ => c p.1)
    (h := fun (p : α × List β × List γ) (q : (β × γ) × σ) => H p.1 (q.1.1, q.1.2, q.2))
    (primrec_zip.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (hc.comp Primrec.fst)
    (hH.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))).to₂).of_eq fun p => ?_
  exact (zipRec_eq h0 h0' h1 p.1 p.2.1 p.2.2).symm

/-- Simultaneous recursion on two lists, without a parameter. -/
theorem zipRec₀ {F : List β → List γ → σ} {c : σ} {H : β × γ × σ → σ} (hH : Primrec H)
    (h0 : ∀ ys, F [] ys = c) (h0' : ∀ x xs, F (x :: xs) [] = c)
    (h1 : ∀ x xs y ys, F (x :: xs) (y :: ys) = H (x, y, F xs ys)) : Primrec₂ F := by
  show Primrec fun p : List β × List γ => F p.1 p.2
  exact (zipRec (F := fun (_ : Unit) => F) (c := fun _ : Unit => c)
    (H := fun (_ : Unit) (q : β × γ × σ) => H q) (Primrec.const c) (hH.comp Primrec.snd).to₂
    (fun _ ys => h0 ys) (fun _ x xs => h0' x xs) (fun _ x xs y ys => h1 x xs y ys)).comp
    (Primrec.pair (Primrec.const ()) Primrec.id)

/-- Pointwise combination of two lists keeping the longer tail. -/
theorem zipLong {F : List β → List β → List β} {op : β → β → β} (hop : Primrec₂ op)
    (h0 : ∀ v, F [] v = v) (h0' : ∀ a u, F (a :: u) [] = a :: u)
    (h1 : ∀ a u b v, F (a :: u) (b :: v) = op a b :: F u v) : Primrec₂ F := by
  show Primrec fun p : List β × List β => F p.1 p.2
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_map (f := fun p : List β × List β => List.zip p.1 p.2)
        (g := fun (_ : List β × List β) (q : β × β) => op q.1 q.2)
        (primrec_zip.comp Primrec.fst Primrec.snd)
        (hop.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
      (Primrec.list_drop.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst))
    (Primrec.list_drop.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)).of_eq
    fun p => (zipLong_eq h0 h0' h1 p.1 p.2).symm

/-- `List.any` with a primitive recursive predicate depending on a parameter. -/
theorem primrec_list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec₂ p) : Primrec fun a => (f a).any (p a) := by
  refine (Primrec.list_foldr (f := f) (g := fun _ : α => false)
    (h := fun (a : α) (q : β × Bool) => p a q.1 || q.2) hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih => exact congrArg (fun s => p a b || s) ih

/-- `List.all` with a primitive recursive predicate depending on a parameter. -/
theorem primrec_list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec₂ p) : Primrec fun a => (f a).all (p a) := by
  refine (Primrec.list_foldr (f := f) (g := fun _ : α => true)
    (h := fun (a : α) (q : β × Bool) => p a q.1 && q.2) hf (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih => exact congrArg (fun s => p a b && s) ih

/-- `Option.elim` with primitive recursive branches. -/
theorem primrec_option_elim {o : α → Option β} {d : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hd : Primrec d) (hg : Primrec₂ g) : Primrec fun a => (o a).elim (d a) (g a) := by
  refine (Primrec.option_casesOn ho hd hg).of_eq fun a => ?_
  cases o a <;> rfl

end Schemes

end GroupApproximation.Full.NN11b.PR
