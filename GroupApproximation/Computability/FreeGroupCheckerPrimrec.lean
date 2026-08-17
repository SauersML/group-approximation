import GroupApproximation.Computability.FreeGroupDeletionPrimrec

/-!
# The deletion checker is primitive recursive

This finishes the plumbing that `FreeGroupDeletionPrimrec` set up.  Over the
alphabet `ℕ`, which is what `PresentationCode` words use, the certificate
checker of `FreeGroupDeletion` is primitive recursive:

* `primrec_cancelsAt` — the `Bool` test at a position, from `list_getElem?` and
  the `Option` combinators.
* `primrec_deleteAt` — one deletion, from the closed form
  `cond (cancelsAt L i) (some (L.take i ++ L.drop (i + 2))) none`.
* `primrec_applySteps` — the whole replay, from `list_foldl` and the fold form.

With these, the search over certificates in `D2` is a search a partial recursive
function can perform, which is exactly what the raw-word route was chosen to
make possible: no step of it mentions a free-group element, and `FreeGroup` has
no `Primcodable` instance at this Mathlib revision.
-/

namespace GroupApproximation
namespace Computability

/-- The position test, with the `Option` nesting made explicit. -/
theorem cancelsAt_eq_bind (L : List (ℕ × Bool)) (i : ℕ) :
    cancelsAt L i
      = ((L[i]?.bind fun p => (L[i + 1]?).map fun q =>
            (p.1 == q.1 && q.2 == !p.2)).getD false) := by
  unfold cancelsAt
  cases hp : L[i]? with
  | none => simp
  | some p =>
      cases hq : L[i + 1]? with
      | none => simp
      | some q =>
          obtain ⟨x, b⟩ := p
          obtain ⟨y, c⟩ := q
          simp

theorem primrec_cancelsAt : Primrec₂ (cancelsAt : List (ℕ × Bool) → ℕ → Bool) := by
  have h1 : Primrec fun x : List (ℕ × Bool) × ℕ => x.1[x.2]? :=
    Primrec.list_getElem?.comp Primrec.fst Primrec.snd
  have h2 : Primrec fun x : List (ℕ × Bool) × ℕ => x.1[x.2 + 1]? :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.succ.comp Primrec.snd)
  have hg : Primrec₂ fun (y : (List (ℕ × Bool) × ℕ) × (ℕ × Bool)) (q : ℕ × Bool) =>
      (y.2.1 == q.1 && q.2 == !y.2.2) :=
    (Primrec.and.comp
      (Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.beq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.not.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂
  have hmap : Primrec₂ fun (x : List (ℕ × Bool) × ℕ) (p : ℕ × Bool) =>
      (x.1[x.2 + 1]?).map fun q => (p.1 == q.1 && q.2 == !p.2) :=
    Primrec.option_map (h2.comp Primrec.fst) hg
  have hbind : Primrec fun x : List (ℕ × Bool) × ℕ =>
      (x.1[x.2]?).bind fun p => (x.1[x.2 + 1]?).map fun q =>
        (p.1 == q.1 && q.2 == !p.2) :=
    Primrec.option_bind h1 hmap
  have hfin := Primrec.option_getD.comp hbind (Primrec.const false)
  exact hfin.of_eq fun x => (cancelsAt_eq_bind x.1 x.2).symm

/-- The closed form as a `cond`, which is what `Primrec.cond` consumes. -/
theorem deleteAt_eq_cond (L : List (ℕ × Bool)) (i : ℕ) :
    deleteAt L i
      = cond (cancelsAt L i) (some (L.take i ++ L.drop (i + 2))) none := by
  rw [deleteAt_eq_ite]
  cases cancelsAt L i <;> simp

theorem primrec_deleteAt :
    Primrec₂ (deleteAt : List (ℕ × Bool) → ℕ → Option (List (ℕ × Bool))) := by
  have hsome : Primrec fun x : List (ℕ × Bool) × ℕ =>
      some (x.1.take x.2 ++ x.1.drop (x.2 + 2)) :=
    Primrec.option_some.comp
      (Primrec.list_append.comp
        (Primrec.list_take.comp Primrec.snd Primrec.fst)
        (Primrec.list_drop.comp
          (Primrec.succ.comp (Primrec.succ.comp Primrec.snd)) Primrec.fst))
  have h := Primrec.cond primrec_cancelsAt hsome (Primrec.const none)
  exact h.of_eq fun x => (deleteAt_eq_cond x.1 x.2).symm

theorem primrec_applySteps :
    Primrec₂ (applySteps : List (ℕ × Bool) → List ℕ → Option (List (ℕ × Bool))) := by
  have hstep : Primrec₂ fun (x : List (ℕ × Bool) × List ℕ)
      (p : Option (List (ℕ × Bool)) × ℕ) => p.1.bind fun M => deleteAt M p.2 := by
    have hf : Primrec fun z : (List (ℕ × Bool) × List ℕ) × (Option (List (ℕ × Bool)) × ℕ) =>
        z.2.1 := Primrec.fst.comp Primrec.snd
    have hg : Primrec₂ fun (z : (List (ℕ × Bool) × List ℕ) × (Option (List (ℕ × Bool)) × ℕ))
        (M : List (ℕ × Bool)) => deleteAt M z.2.2 :=
      primrec_deleteAt.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact Primrec.option_bind hf hg
  have h : Primrec fun x : List (ℕ × Bool) × List ℕ =>
      x.2.foldl (fun acc i => acc.bind fun M => deleteAt M i) (some x.1) :=
    Primrec.list_foldl Primrec.snd (Primrec.option_some.comp Primrec.fst) hstep
  exact h.of_eq fun x => (applySteps_eq_foldl x.1 x.2).symm

end Computability
end GroupApproximation
