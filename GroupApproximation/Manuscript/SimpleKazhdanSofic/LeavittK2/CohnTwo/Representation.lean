import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fock representation of `C_2`

Lane `sk-leavitt-18`, third module.

`C_2` acts on `FockSpace k = (List (Fin 2) → k)`: `e_i` prepends the letter `i`
(`shiftOp`), and `e_i*` deletes a leading `i` (`deleteOp`). The Cohn relations
`e_i* e_j = δ_ij` hold, but `ee* + ff* = 1` fails on the empty word, which is
the vacuum that `p` projects onto.

Route: `fock_coword` (`β*` reads at `β ++ w`), `fock_p` (`p` projects onto the
vacuum), `fock_word_pt` (`α` moves the vacuum to `α`), hence
`fock_unit : α p β*` acts by `f ↦ (w ↦ if w = α then f β else 0)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace CohnTwo

open CohnRelativeK1

variable (k : Type*) [Field k]

/-- Functions on finite binary words. -/
abbrev FockSpace := List (Fin 2) → k

/-- The point mass `c` at the word `u`. -/
def pt (u : List (Fin 2)) (c : k) : FockSpace k := fun w => if w = u then c else 0

/-- Prepend the letter `i`: `(e_i f)(i :: w) = f w`, and zero off `i :: _`. -/
def shiftFun (i : Fin 2) (f : FockSpace k) : List (Fin 2) → k
  | [] => 0
  | j :: w => if j = i then f w else 0

/-- `e_i` on the Fock space. -/
def shiftOp (i : Fin 2) : Module.End k (FockSpace k) where
  toFun := shiftFun k i
  map_add' f g := by
    funext w
    cases w with
    | nil => simp [shiftFun]
    | cons j w => by_cases h : j = i <;> simp [shiftFun, h]
  map_smul' c f := by
    funext w
    cases w with
    | nil => simp [shiftFun]
    | cons j w => by_cases h : j = i <;> simp [shiftFun, h]

/-- `e_i*` on the Fock space: `(e_i* f)(w) = f (i :: w)`. -/
def deleteOp (i : Fin 2) : Module.End k (FockSpace k) where
  toFun f w := f (i :: w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deleteOp_mul_shiftOp_self (i : Fin 2) : deleteOp k i * shiftOp k i = 1 := by
  apply LinearMap.ext
  intro f
  funext w
  show (if i = i then f w else 0) = f w
  exact if_pos rfl

theorem deleteOp_mul_shiftOp_of_ne {i j : Fin 2} (h : i ≠ j) :
    deleteOp k i * shiftOp k j = 0 := by
  apply LinearMap.ext
  intro f
  funext w
  show (if i = j then f w else 0) = 0
  exact if_neg h

/-- The four generators on the Fock space. -/
def fockGen (g : BinaryLeavitt.Generator) : Module.End k (FockSpace k) :=
  if g = BinaryLeavitt.s0 then shiftOp k 0 else
  if g = BinaryLeavitt.s1 then shiftOp k 1 else
  if g = BinaryLeavitt.t0 then deleteOp k 0 else deleteOp k 1

theorem fockGen_s0 : fockGen k BinaryLeavitt.s0 = shiftOp k 0 := by
  simp [fockGen]

theorem fockGen_s1 : fockGen k BinaryLeavitt.s1 = shiftOp k 1 := by
  simp [fockGen, BinaryLeavitt.s0, BinaryLeavitt.s1]

theorem fockGen_t0 : fockGen k BinaryLeavitt.t0 = deleteOp k 0 := by
  simp [fockGen, BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0]

theorem fockGen_t1 : fockGen k BinaryLeavitt.t1 = deleteOp k 1 := by
  simp [fockGen, BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0, BinaryLeavitt.t1]

theorem fock_respects :
    ∀ ⦃x y : BinaryLeavitt.Free k⦄, CohnRelation k x y →
      FreeAlgebra.lift k (fockGen k) x = FreeAlgebra.lift k (fockGen k) y := by
  intro x y h
  cases h
  · rw [map_mul, map_one, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, fockGen_t0,
      fockGen_s0]
    exact deleteOp_mul_shiftOp_self k 0
  · rw [map_mul, map_zero, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, fockGen_t0,
      fockGen_s1]
    exact deleteOp_mul_shiftOp_of_ne k (show (0 : Fin 2) ≠ 1 by decide)
  · rw [map_mul, map_zero, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, fockGen_t1,
      fockGen_s0]
    exact deleteOp_mul_shiftOp_of_ne k (show (1 : Fin 2) ≠ 0 by decide)
  · rw [map_mul, map_one, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, fockGen_t1,
      fockGen_s1]
    exact deleteOp_mul_shiftOp_self k 1

/-- The Fock representation `C_2 →ₐ End_k(FockSpace k)`. -/
def fock : CohnTwo k →ₐ[k] Module.End k (FockSpace k) :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (fockGen k), fock_respects k⟩

theorem fock_generator (g : BinaryLeavitt.Generator) :
    fock k (generator k g) = fockGen k g := by
  rw [generator, quotientMap, fock, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]

theorem fock_gen (a : Fin 2) : fock k ((data k).gen a) = shiftOp k a := by
  rcases CohnTwoData.fin_two_cases a with rfl | rfl
  · rw [CohnTwoData.gen_zero]
    exact (fock_generator k BinaryLeavitt.s0).trans (fockGen_s0 k)
  · rw [CohnTwoData.gen_one]
    exact (fock_generator k BinaryLeavitt.s1).trans (fockGen_s1 k)

theorem fock_gs (a : Fin 2) : fock k ((data k).gs a) = deleteOp k a := by
  rcases CohnTwoData.fin_two_cases a with rfl | rfl
  · rw [CohnTwoData.gs_zero]
    exact (fock_generator k BinaryLeavitt.t0).trans (fockGen_t0 k)
  · rw [CohnTwoData.gs_one]
    exact (fock_generator k BinaryLeavitt.t1).trans (fockGen_t1 k)

theorem fock_coword (β : List (Fin 2)) (f : FockSpace k) (w : List (Fin 2)) :
    fock k ((data k).coword β) f w = f (β ++ w) := by
  induction β generalizing f w with
  | nil => rw [CohnTwoData.coword_nil, map_one, Module.End.one_apply, List.nil_append]
  | cons a β ih =>
    rw [CohnTwoData.coword_cons, map_mul, Module.End.mul_apply, ih, fock_gs, List.cons_append]
    rfl

theorem fock_p (f : FockSpace k) : fock k (data k).p f = pt k [] (f []) := by
  have hp : (data k).p = 1 - (data k).gen 0 * (data k).gs 0 - (data k).gen 1 * (data k).gs 1 := by
    unfold CohnTwoData.p
    rw [CohnTwoData.gen_zero, CohnTwoData.gs_zero, CohnTwoData.gen_one, CohnTwoData.gs_one]
  rw [hp, map_sub, map_sub, map_one, map_mul, map_mul, fock_gen, fock_gen, fock_gs, fock_gs]
  funext w
  rcases w with _ | ⟨j, w⟩
  · show f [] - 0 - 0 = if ([] : List (Fin 2)) = [] then f [] else 0
    rw [if_pos rfl, sub_zero, sub_zero]
  · show f (j :: w) - (if j = 0 then f (0 :: w) else 0) - (if j = 1 then f (1 :: w) else 0) =
      if j :: w = [] then f [] else 0
    rw [if_neg (List.cons_ne_nil j w)]
    rcases CohnTwoData.fin_two_cases j with rfl | rfl
    · rw [if_pos rfl, if_neg (show ¬ ((0 : Fin 2) = 1) by decide), sub_self, sub_zero]
    · rw [if_neg (show ¬ ((1 : Fin 2) = 0) by decide), if_pos rfl, sub_zero, sub_self]

theorem fock_word_pt (α : List (Fin 2)) (c : k) :
    fock k ((data k).word α) (pt k [] c) = pt k α c := by
  induction α with
  | nil => rw [CohnTwoData.word_nil, map_one, Module.End.one_apply]
  | cons a α ih =>
    rw [CohnTwoData.word_cons, map_mul, Module.End.mul_apply, ih, fock_gen]
    funext w
    rcases w with _ | ⟨j, w⟩
    · show (0 : k) = if ([] : List (Fin 2)) = a :: α then c else 0
      rw [if_neg (List.cons_ne_nil a α).symm]
    · show (if j = a then pt k α c w else 0) = if j :: w = a :: α then c else 0
      by_cases h : j = a
      · rw [if_pos h]
        show (if w = α then c else 0) = _
        by_cases hw : w = α
        · rw [if_pos hw, if_pos (show j :: w = a :: α by rw [h, hw])]
        · rw [if_neg hw, if_neg (fun hc => hw (List.cons.inj hc).2)]
      · rw [if_neg h, if_neg (fun hc => h (List.cons.inj hc).1)]

/-- The matrix unit `α p β*` acts by `f ↦ (w ↦ if w = α then f β else 0)`. -/
theorem fock_unit (α β : List (Fin 2)) (f : FockSpace k) :
    fock k ((data k).unit α β) f = pt k α (f β) := by
  have hc : fock k ((data k).coword β) f [] = f β := by
    rw [fock_coword, List.append_nil]
  rw [CohnTwoData.unit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, fock_p, hc,
    fock_word_pt]

end CohnTwo

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.pt
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.shiftFun
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.shiftOp
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.deleteOp
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.deleteOp_mul_shiftOp_self
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.deleteOp_mul_shiftOp_of_ne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fockGen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fockGen_t1
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock_respects
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock_gen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock_gs
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock_p
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.fock_unit
