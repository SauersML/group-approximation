import GroupApproximation.Computability.TrNatRecurrence
import GroupApproximation.Computability.QuadMachine
import GroupApproximation.Computability.ModularMachineUndecidable

/-!
# The index map is computable

This closes the arithmetic half of `D4'`.  The map built inside
`exists_modularMachine_halting_not_computablePred` is

    f m = (D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))

and `initQCfg` leaves the back stack empty with the side fixed, so `encCfg` of
it has a constant first component and, in the second, `encList` of the encoded
symbol list.  Everything here is about that symbol list and that fold; nothing
touches the machine's transition function, and no `Primrec` fact about
`PartrecToTM2`, `TM2to1` or `TM1to0` is needed.

* `encList_eq_foldr` / `primrec_encList` --- the Horner fold is primitive
  recursive.  `encList` is literally `List.foldr (fun d acc => d + base * acc) 0`.
* `map_enc_trInit` --- the symbol list is a fixed head followed by the reversed
  digits: `trList [m] = trNat m ++ [Γ'.cons]`, and `trInit` reverses, tags the
  head `true` and leaves the tail `false`.  This is a computation, not an
  induction.
* `computable_encList_map_trInit` --- the second component of `f`, computable.

The symbol reading `enc` is arbitrary, which is the point: the encoding that
actually appears is built from `Fintype.equivFin` and is noncomputable, and it
does not matter, because only its values at finitely many symbols occur and
each of those is a fixed natural.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

/-- The Horner encoding is a `foldr`. -/
theorem encList_eq_foldr (base : ℕ) (l : List ℕ) :
    encList base l = l.foldr (fun d acc => d + base * acc) 0 := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [encList_cons, ih, List.foldr_cons]

/-- **The Horner encoding is primitive recursive.** -/
theorem primrec_encList (base : ℕ) : Primrec (encList base) := by
  have h : Primrec (fun l : List ℕ => l.foldr (fun d acc => d + base * acc) 0) := by
    refine Primrec.list_foldr (f := fun l : List ℕ => l)
      (g := fun _ : List ℕ => (0 : ℕ))
      (h := fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 + base * p.2)
      Primrec.id (Primrec.const 0) ?_
    exact (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.const base)
        (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun l => (encList_eq_foldr base l).symm

/-- **The initial symbol list.**  A fixed head, then the reversed digits of the
input, each tagged `false`. -/
theorem map_enc_trInit (enc : TM2to1.Γ' K' (fun _ : K' => Γ') → ℕ) (m : ℕ) :
    ((TM2to1.trInit K'.main (trList [m])).map enc)
      = enc (true, Function.update (fun _ => none) K'.main (some Γ'.cons))
        :: ((trNat m).reverse.map
              (fun a => enc (false, Function.update (fun _ => none) K'.main (some a)))) := by
  simp [TM2to1.trInit, trList, List.reverse_append]

/-- **The second component of the index map is computable.** -/
theorem computable_encList_map_trInit (base : ℕ)
    (enc : TM2to1.Γ' K' (fun _ : K' => Γ') → ℕ) :
    Computable (fun m : ℕ =>
      encList base ((TM2to1.trInit K'.main (trList [m])).map enc)) := by
  have hdigits : Computable (fun m : ℕ =>
      (trNat m).map (fun a => enc (false, Function.update (fun _ => none) K'.main (some a)))) :=
    computable_map_trNat _
  have hrev : Computable (fun m : ℕ =>
      ((trNat m).map
        (fun a => enc (false, Function.update (fun _ => none) K'.main (some a)))).reverse) :=
    Computable.list_reverse.comp hdigits
  have hcons : Computable (fun m : ℕ =>
      enc (true, Function.update (fun _ => none) K'.main (some Γ'.cons))
        :: ((trNat m).map
              (fun a => enc (false,
                Function.update (fun _ => none) K'.main (some a)))).reverse) :=
    Computable.list_cons.comp (Computable.const _) hrev
  have h := (primrec_encList base).to_comp.comp hcons
  refine h.of_eq fun m => ?_
  rw [map_enc_trInit enc m, List.map_reverse]

/-! ## The index map itself -/

/-- **The initial configuration, encoded.**  `initQCfg` leaves the back stack
empty and fixes the side, so the pair is a constant beside the Horner value of
the encoded symbol list.  This is why no part of the machine's transition
function enters the computability question. -/
theorem encCfg_initQCfg {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (D : TMData Γ Λ) (M : TM0.Machine Γ Λ) (l : List Γ) :
    (D.toQuad M).encCfg (D.initQCfg l)
      = ((D.toQuad M).tagA (D.stIdx default false true),
          encList (D.toQuad M).m (l.map D.encodeSym)) := by
  simp [QuadMachine.encCfg, TMData.initQCfg]

/-- **The index map is computable**, for any state type and any machine: the
first component is constant and the second is the fold proved computable above.
The symbol encoding inside `D` may be choice-based — as `TMData.ofFintype`'s is
— without affecting this, since it is applied only to the finitely many symbols
of the initial word and each of its values is a fixed natural. -/
theorem computable_index_map {Λ : Type} [Inhabited Λ]
    (D : TMData (TM2to1.Γ' K' (fun _ : K' => Γ')) Λ)
    (M : TM0.Machine (TM2to1.Γ' K' (fun _ : K' => Γ')) Λ) :
    Computable (fun m : ℕ =>
      (D.toQuad M).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))) := by
  have hpair :=
    (Computable.const ((D.toQuad M).tagA (D.stIdx default false true))).pair
      (computable_encList_map_trInit (D.toQuad M).m D.encodeSym)
  exact hpair.of_eq fun m => (encCfg_initQCfg D M _).symm

end Computability
end GroupApproximation
