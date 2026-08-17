import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Tactic.NormNum

/-!
# The binary digit list, and its primitive recursiveness

The remaining hypothesis of
`Computability.ComputableConfigReduction.exists_modularMachine_config_halting_not_computablePred_of_computable`
is that the index map of `exists_modularMachine_halting_not_computablePred` is
computable.  Unfolding that map leaves a constant first component and, in the
second, a Horner value over the binary digits of the input with one fixed
natural per digit value.  This module supplies the digit list and the fact that
it is primitive recursive, which is the only genuinely recursive ingredient;
everything else there is `List.reverse`, `List.map` and a fold, all of which
Mathlib already has.

`binDigits a b m` is the base-two expansion of `m`, least significant digit
first, reading a zero digit as `a` and a one digit as `b`.  It is stated in this
form, rather than as `Nat.digits 2 m` mapped, because Mathlib carries no
`Primrec` fact about `Nat.digits`, whereas the recursion below is exactly the
shape `Primrec.nat_strong_rec` consumes.

The recursion descends by halving, so it is a strong recursion rather than a
structural one, and `Primrec.nat_strong_rec` is the right tool: it asks for the
value at `n` to be recoverable from the list of values at `0, …, n - 1`, and
`m / 2 < m` puts the needed entry inside that list.
-/

namespace GroupApproximation
namespace Computability

/-- The base-two expansion of `m`, least significant digit first, with `a` for a
zero digit and `b` for a one digit. -/
def binDigits (a b : ℕ) : ℕ → List ℕ
  | 0 => []
  | (n + 1) => (if (n + 1) % 2 = 0 then a else b) :: binDigits a b ((n + 1) / 2)
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) Nat.one_lt_two

@[simp] theorem binDigits_zero (a b : ℕ) : binDigits a b 0 = [] := by
  rw [binDigits]

theorem binDigits_succ (a b n : ℕ) :
    binDigits a b (n + 1)
      = (if (n + 1) % 2 = 0 then a else b) :: binDigits a b ((n + 1) / 2) := by
  rw [binDigits]

/-- The step function of the strong recursion: given the values of `binDigits`
at every index below `n`, presented as a list of length `n`, produce the value
at `n`.  The recursive entry sits at index `n / 2`, which is in range exactly
when `n` is positive. -/
def binStep (a b : ℕ) (L : List (List ℕ)) : Option (List ℕ) :=
  if L.length = 0 then some []
  else some ((if L.length % 2 = 0 then a else b) :: L.getD (L.length / 2) [])

theorem primrec_binStep (a b : ℕ) : Primrec (binStep a b) := by
  have hlen : Primrec (fun L : List (List ℕ) => L.length) := Primrec.list_length
  have hdigit : Primrec (fun L : List (List ℕ) =>
      if L.length % 2 = 0 then a else b) := by
    refine Primrec.ite ?_ (Primrec.const a) (Primrec.const b)
    exact Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2))
      (Primrec.const 0)
  have hrec : Primrec (fun L : List (List ℕ) => L.getD (L.length / 2) []) :=
    (Primrec.list_getD []).comp Primrec.id
      (Primrec.nat_div.comp hlen (Primrec.const 2))
  refine Primrec.ite ?_ (Primrec.const (some []))
    (Primrec.option_some.comp (Primrec.list_cons.comp hdigit hrec))
  exact Primrec.eq.comp hlen (Primrec.const 0)

/-- The list of earlier values has length `n`, so the length appearing in
`binStep` is the index itself. -/
theorem length_range_map (a b n : ℕ) :
    ((List.range n).map (binDigits a b)).length = n := by
  simp

/-- The entry the step function reaches for is the value at `n / 2`. -/
theorem getD_range_map (a b n : ℕ) (h : n / 2 < n) :
    ((List.range n).map (binDigits a b)).getD (n / 2) [] = binDigits a b (n / 2) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem binStep_spec (a b n : ℕ) :
    binStep a b ((List.range n).map (binDigits a b)) = some (binDigits a b n) := by
  cases n with
  | zero => simp [binStep]
  | succ k =>
      have hlt : (k + 1) / 2 < k + 1 :=
        Nat.div_lt_self (Nat.succ_pos k) Nat.one_lt_two
      rw [binStep, if_neg (by simp), length_range_map, getD_range_map a b _ hlt,
        binDigits_succ]

/-- **The digit list is primitive recursive.**  This is the only recursive
ingredient of the index map; the rest is `List.reverse`, `List.map` and a fold. -/
theorem primrec_binDigits (a b : ℕ) : Primrec (binDigits a b) := by
  have h : Primrec₂ (fun (_ : Unit) (n : ℕ) => binDigits a b n) :=
    Primrec.nat_strong_rec _
      ((primrec_binStep a b).comp Primrec.snd).to₂
      (fun _ n => binStep_spec a b n)
  simpa using h.comp (Primrec.const ()) Primrec.id

/-- **The digit list is computable**, the form the reduction lemmas consume. -/
theorem computable_binDigits (a b : ℕ) : Computable (binDigits a b) :=
  (primrec_binDigits a b).to_comp

end Computability
end GroupApproximation
