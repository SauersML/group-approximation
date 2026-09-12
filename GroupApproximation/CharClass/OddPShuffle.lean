import GroupApproximation.CharClass.OddPTupleAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Signed slot permutations of the flat tensor power, and the riffle shuffle

The Cartan comparison of the odd-primary reduced powers passes between `C(X)^{⊗2p}` read as
`x₁ … x_p y₁ … y_p` and the same tensor read as `(x₁y₁) … (x_py_p)`, and it needs that passage to be
a chain map that turns the diagonal cyclic action into the cyclic action of the pairs.  Rather than
build that one map by hand, this file builds **every** signed permutation of slots at once.

* `permTup π t = t ∘ π`: slot `i` of the new tuple holds slot `π i` of the old one.
* `permExp X π t`: the Koszul exponent, the sum of `|t (π i)| · |t (π j)|` over the new positions
  `i < j` whose sources are in the opposite order.
* `tupPermAll K X r π`: the operator on the full model, `single t ↦ (-1)^{permExp} • single (permTup π t)`.

## Main results

* `tupPermAll_mul_tupDAll` — every signed permutation is a chain map.
* `tupPermAll_mul` — `tupPermAll π * tupPermAll ρ = tupPermAll (ρ * π)`: the exponents add up to an
  even correction, because a pair reordered by both stages is not reordered by their composite.
* `tupTAll_eq_tupPermAll` — the cyclic operator of `OddPTupleAction` is the permutation `finRotate r`.
* `tupRiffleAll_conj` — `R * B = T² * R` for the riffle `R` and the blockwise rotation `B`, a group
  identity of slot permutations.
* degree-`k` twins of all of these on `tupMod`, through `tupIncl`.

## The sign bookkeeping

For the chain map, differentiating the old slot `π i` changes the Koszul exponent by the degrees of
the slots reordered with it, `E + F` (`permExp_update`), and the prefix of the old slot differs from
the prefix of the new slot by the same slots with an even correction (`tupPre_perm_add`).  Both are
pointwise identities of `if`-sums over new positions, so no reindexing of a Finset interval survives.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Permuted tuples and prefixes -/

section Tuples

variable {X : TopCat.{0}} {r : ℕ}

/-- **Permute the slots of a tuple**: slot `i` of the new tuple holds slot `π i` of the old one. -/
def permTup (π : Equiv.Perm (Fin r)) (t : TupAll X r) : TupAll X r := t ∘ π

theorem permTup_apply (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) :
    permTup π t i = t (π i) := rfl

/-- Permuting by `ρ` and then by `π` is permuting by `ρ * π`. -/
theorem permTup_mul (π ρ : Equiv.Perm (Fin r)) (t : TupAll X r) :
    permTup π (permTup ρ t) = permTup (ρ * π) t := rfl

theorem permTup_one (t : TupAll X r) : permTup (1 : Equiv.Perm (Fin r)) t = t := rfl

/-- Updating old slot `π i` and permuting is permuting and updating new slot `i`. -/
theorem permTup_update (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) (τ : TagSimp X) :
    permTup π (Function.update t (π i) τ) = Function.update (permTup π t) i τ := by
  have h := Function.update_comp_equiv t π (π i) τ
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The Koszul prefix as a sum over all slots, with the order condition as an `if`. -/
theorem tupPre_eq_sum_ite (t : TupAll X r) (a : Fin r) :
    tupPre t a = ∑ l : Fin r, if l < a then (t l).1 else 0 := by
  have h := Finset.sum_filter (s := (Finset.univ : Finset (Fin r))) (fun l : Fin r => l < a)
    (fun l => (t l).1)
  rw [← h, tupPre]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext l
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The prefix of the permuted tuple, over new positions. -/
theorem tupPre_permTup (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) :
    tupPre (permTup π t) i = ∑ j : Fin r, if j < i then (t (π j)).1 else 0 := by
  rw [tupPre_eq_sum_ite]
  simp only [permTup_apply]

/-- The prefix of an old slot, reindexed over new positions. -/
theorem tupPre_perm_apply (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) :
    tupPre t (π i) = ∑ j : Fin r, if π j < π i then (t (π j)).1 else 0 := by
  rw [tupPre_eq_sum_ite]
  exact (Equiv.sum_comp π (fun l : Fin r => if l < π i then (t l).1 else 0)).symm

/-- The pointwise form of `tupPre_perm_add`. -/
theorem perm_pre_pointwise (π : Equiv.Perm (Fin r)) (i j : Fin r) (d : ℕ) :
    (if π j < π i then d else 0) + (if j < i ∧ π i < π j then d else 0)
      = (if j < i then d else 0) + (if i < j ∧ π j < π i then d else 0) := by
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : π j ≠ π i := fun h => hji (π.injective h)
    rcases lt_or_gt_of_ne hji with h1 | h1 <;> rcases lt_or_gt_of_ne hne with h2 | h2 <;>
      simp [h1, h2, lt_asymm h1, lt_asymm h2]

/-- **The two prefixes of one slot.**  The old prefix of `π i` and the new prefix of `i` differ by
the slots reordered with it: `F` counts those before `i` in the new order and after `π i` in the
old, `E` the reverse. -/
theorem tupPre_perm_add (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) :
    tupPre t (π i) + ∑ j : Fin r, (if j < i ∧ π i < π j then (t (π j)).1 else 0)
      = tupPre (permTup π t) i + ∑ j : Fin r, (if i < j ∧ π j < π i then (t (π j)).1 else 0) := by
  rw [tupPre_perm_apply, tupPre_permTup, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => perm_pre_pointwise π i j _

end Tuples

/-! ## 2. The Koszul exponent -/

/-- A double sum over `Fin r` whose summand vanishes off the row `a = i` is that row. -/
theorem sum_sum_ite_eq_left {M : Type*} [AddCommMonoid M] {r : ℕ} (i : Fin r) (f : Fin r → M) :
    (∑ a : Fin r, ∑ b : Fin r, if a = i then f b else 0) = ∑ b : Fin r, f b := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- A double sum over `Fin r` whose summand vanishes off the column `b = i` is that column. -/
theorem sum_sum_ite_eq_right {M : Type*} [AddCommMonoid M] {r : ℕ} (i : Fin r) (f : Fin r → M) :
    (∑ a : Fin r, ∑ b : Fin r, if b = i then f a else 0) = ∑ a : Fin r, f a := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The value of `finRotate r j`, with the wrap-around as an `if` (so that `omega` can read it). -/
theorem finRotate_val_eq_ite {r : ℕ} (j : Fin r) :
    ((finRotate r j : Fin r) : ℕ) = if (j : ℕ) + 1 = r then 0 else (j : ℕ) + 1 := by
  rw [finRotate_val_eq]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by have := j.2; omega)

section Exponent

variable (X : TopCat.{0}) {r : ℕ}

/-- **The Koszul exponent of a slot permutation**: over pairs of new positions `i < j` whose sources
are in the opposite order, the product of the two degrees. -/
def permExp (π : Equiv.Perm (Fin r)) (t : TupAll X r) : ℕ :=
  ∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then (t (π i)).1 * (t (π j)).1 else 0

theorem permExp_one (t : TupAll X r) : permExp X (1 : Equiv.Perm (Fin r)) t = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun h => lt_asymm h.1 h.2

/-- **Differentiating one slot moves the exponent by the slots reordered with it.** -/
theorem permExp_update (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) (τ : TagSimp X)
    (hd : τ.1 + 1 = (t (π i)).1) :
    permExp X π (Function.update t (π i) τ)
        + (∑ j : Fin r, (if i < j ∧ π j < π i then (t (π j)).1 else 0)
          + ∑ j : Fin r, (if j < i ∧ π i < π j then (t (π j)).1 else 0))
      = permExp X π t := by
  have hpt : ∀ a b : Fin r,
      (if a < b ∧ π b < π a then (t (π a)).1 * (t (π b)).1 else 0)
        = (if a < b ∧ π b < π a then
              ((Function.update t (π i) τ) (π a)).1 * ((Function.update t (π i) τ) (π b)).1
            else 0)
          + (if a = i then (if i < b ∧ π b < π i then (t (π b)).1 else 0) else 0)
          + (if b = i then (if a < i ∧ π i < π a then (t (π a)).1 else 0) else 0) := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i
    · subst ha
      subst hb
      simp
    · subst ha
      rw [Function.update_self, Function.update_of_ne (fun h => hb (π.injective h)), ← hd,
        if_pos rfl, if_neg hb, add_zero]
      split_ifs <;> ring
    · subst hb
      rw [Function.update_self, Function.update_of_ne (fun h => ha (π.injective h)), ← hd,
        if_neg ha, if_pos rfl, add_zero]
      split_ifs <;> ring
    · rw [Function.update_of_ne (fun h => ha (π.injective h)),
        Function.update_of_ne (fun h => hb (π.injective h)), if_neg ha, if_neg hb]
      simp only [add_zero]
  have hsum : (∑ a : Fin r, ∑ b : Fin r,
        if a < b ∧ π b < π a then (t (π a)).1 * (t (π b)).1 else 0)
      = ∑ a : Fin r, ∑ b : Fin r,
          ((if a < b ∧ π b < π a then
              ((Function.update t (π i) τ) (π a)).1 * ((Function.update t (π i) τ) (π b)).1
            else 0)
          + (if a = i then (if i < b ∧ π b < π i then (t (π b)).1 else 0) else 0)
          + (if b = i then (if a < i ∧ π i < π a then (t (π a)).1 else 0) else 0)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
  simp only [Finset.sum_add_distrib, sum_sum_ite_eq_left, sum_sum_ite_eq_right] at hsum
  unfold permExp
  omega

/-- **The exponent is a cocycle up to an even correction**: permuting by `ρ` and then by `π`
accumulates the exponent of `ρ * π` plus twice the pairs reordered by both stages. -/
theorem permExp_mul (π ρ : Equiv.Perm (Fin r)) (t : TupAll X r) :
    permExp X ρ t + permExp X π (permTup ρ t)
      = permExp X (ρ * π) t
        + 2 * ∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π j < π i ∧ ρ (π i) < ρ (π j) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0 := by
  have hre : permExp X ρ t = ∑ i : Fin r, ∑ j : Fin r,
      if π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0 := by
    unfold permExp
    refine (Equiv.sum_comp π (fun a => ∑ b : Fin r,
      if a < b ∧ ρ b < ρ a then (t (ρ a)).1 * (t (ρ b)).1 else 0)).symm.trans ?_
    exact Finset.sum_congr rfl fun i _ => (Equiv.sum_comp π (fun b =>
      if π i < b ∧ ρ b < ρ (π i) then (t (ρ (π i))).1 * (t (ρ b)).1 else 0)).symm
  have hB : permExp X π (permTup ρ t) = ∑ i : Fin r, ∑ j : Fin r,
      if i < j ∧ π j < π i then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0 := rfl
  have hC : permExp X (ρ * π) t = ∑ i : Fin r, ∑ j : Fin r,
      if i < j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0 := rfl
  have hsplit : ∀ i j : Fin r,
      (if π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
        = (if i < j ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1
            else 0)
          + (if j < i ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1
            else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · rcases lt_or_gt_of_ne hij with h | h
      · simp [h, lt_asymm h]
      · simp [h, lt_asymm h]
  have hswap : (∑ i : Fin r, ∑ j : Fin r,
        if j < i ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
      = ∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π j < π i ∧ ρ (π i) < ρ (π j) then (t (ρ (π i))).1 * (t (ρ (π j))).1
          else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have e1 : (∑ i : Fin r, ∑ j : Fin r,
        if π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
      = (∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1
          else 0)
        + ∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π j < π i ∧ ρ (π i) < ρ (π j) then (t (ρ (π i))).1 * (t (ρ (π j))).1
          else 0 := by
    rw [← hswap, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hsplit i j
  have hpt : ∀ i j : Fin r,
      (if i < j ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
        + (if i < j ∧ π j < π i then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
      = (if i < j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
        + (if i < j ∧ π j < π i ∧ ρ (π i) < ρ (π j) then (t (ρ (π i))).1 * (t (ρ (π j))).1
          else 0) := by
    intro i j
    by_cases hij : i < j
    · have hne1 : π i ≠ π j := fun h => (ne_of_lt hij) (π.injective h)
      have hne2 : ρ (π i) ≠ ρ (π j) := fun h => hne1 (ρ.injective h)
      rcases lt_or_gt_of_ne hne1 with h1 | h1 <;> rcases lt_or_gt_of_ne hne2 with h2 | h2 <;>
        simp [hij, h1, h2, lt_asymm h1, lt_asymm h2]
    · simp [hij]
  have hmain : (∑ i : Fin r, ∑ j : Fin r,
        if i < j ∧ π i < π j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
      + (∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π j < π i then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
      = (∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ ρ (π j) < ρ (π i) then (t (ρ (π i))).1 * (t (ρ (π j))).1 else 0)
        + ∑ i : Fin r, ∑ j : Fin r,
          if i < j ∧ π j < π i ∧ ρ (π i) < ρ (π j) then (t (ρ (π i))).1 * (t (ρ (π j))).1
          else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpt i j
  omega

/-- For new positions `i < j`, the rotation reorders their sources exactly when `j` is the last slot. -/
theorem finRotate_reorders_iff (m : ℕ) (i j : Fin (m + 1)) :
    (i < j ∧ finRotate (m + 1) j < finRotate (m + 1) i) ↔ (j = Fin.last m ∧ (i : ℕ) < m) := by
  have hi := i.2
  have hj := j.2
  have hri := finRotate_val_eq_ite i
  have hrj := finRotate_val_eq_ite j
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.val_last]
  split_ifs at hri hrj <;> constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩

theorem finRotate_castSucc_eq (m : ℕ) (i : Fin m) :
    finRotate (m + 1) (Fin.castSucc i) = Fin.succ i := by
  apply Fin.ext
  rw [finRotate_val_eq_ite, Fin.val_castSucc, Fin.val_succ, if_neg (by have := i.2; omega)]

theorem permExp_finRotate_succ (m : ℕ) (t : TupAll X (m + 1)) :
    permExp X (finRotate (m + 1)) t = (∑ i : Fin m, (t i.succ).1) * (t 0).1 := by
  have hrow : ∀ i : Fin (m + 1),
      (∑ j : Fin (m + 1), if i < j ∧ finRotate (m + 1) j < finRotate (m + 1) i then
          (t (finRotate (m + 1) i)).1 * (t (finRotate (m + 1) j)).1 else 0)
        = if (i : ℕ) < m then (t (finRotate (m + 1) i)).1 * (t 0).1 else 0 := by
    intro i
    simp only [finRotate_reorders_iff, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      finRotate_last]
  unfold permExp
  rw [Finset.sum_congr rfl fun i _ => hrow i, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceIte, Fin.val_last, lt_irrefl, add_zero,
    finRotate_castSucc_eq, Finset.sum_mul]

theorem rotExp_succ (m : ℕ) (t : TupAll X (m + 1)) :
    rotExp X t = (t 0).1 * ∑ i : Fin m, (t i.succ).1 := by
  have h0 : tupDeg t 0 = (t 0).1 := tupDeg_val t 0
  have hN : ∑ j : Fin (m + 1), (t j).1 = (t 0).1 + ∑ i : Fin m, (t i.succ).1 :=
    Fin.sum_univ_succ _
  rw [rotExp, h0, hN, Nat.add_sub_cancel_left]

/-- **The cyclic exponent is the Koszul exponent of the rotation.** -/
theorem rotExp_eq_permExp (t : TupAll X r) : rotExp X t = permExp X (finRotate r) t := by
  cases r with
  | zero => simp [rotExp, permExp, tupDeg]
  | succ m => rw [rotExp_succ, permExp_finRotate_succ, mul_comm]

end Exponent

/-! ## 3. The operator on the full model -/

section FullModel

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

/-- **The signed slot permutation on the full model.** -/
def tupPermAll (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) (π : Equiv.Perm (Fin r)) :
    Module.End K (tupAllMod K X r) :=
  Finsupp.linearCombination K
    (fun t : TupAll X r => ((-1 : K) ^ permExp X π t) • Finsupp.single (permTup π t) (1 : K))

theorem tupPermAll_single (π : Equiv.Perm (Fin r)) (t : TupAll X r) :
    tupPermAll K X r π (Finsupp.single t (1 : K))
      = ((-1 : K) ^ permExp X π t) • Finsupp.single (permTup π t) (1 : K) := by
  rw [tupPermAll, Finsupp.linearCombination_single, one_smul]

/-- **The sign identity behind `P ∘ d = d ∘ P`**, for new slot `i`, old slot `π i`, and one face
`τ` of it. -/
theorem tupPerm_sign (π : Equiv.Perm (Fin r)) (t : TupAll X r) (i : Fin r) (τ : TagSimp X)
    (hd : τ.1 + 1 = (t (π i)).1) :
    (-1 : K) ^ tupPre t (π i) * (-1 : K) ^ permExp X π (Function.update t (π i) τ)
      = (-1 : K) ^ permExp X π t * (-1 : K) ^ tupPre (permTup π t) i := by
  rw [← pow_add, ← pow_add]
  have h1 := permExp_update X π t i τ hd
  have h2 := tupPre_perm_add π t i
  refine neg_one_pow_eq_of_add_two_mul
    (∑ j : Fin r, (if j < i ∧ π i < π j then (t (π j)).1 else 0)) ?_
  omega

/-- **`P ∘ d = d ∘ P` on a basis element of the full model.** -/
theorem tupPermAll_tupDAll_single (π : Equiv.Perm (Fin r)) (t : TupAll X r) :
    tupPermAll K X r π (tupDAll K X r (Finsupp.single t (1 : K)))
      = tupDAll K X r (tupPermAll K X r π (Finsupp.single t (1 : K))) := by
  rw [tupPermAll_single, map_smul, tupDAll, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.smul_sum]
  rw [← Equiv.sum_comp π (fun j : Fin r => tupPermAll K X r π (slotBd K X j
    (Finsupp.single t (1 : K))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotBd_single, slotBd_single, slotBdGen, slotBdGen, map_smul,
    Finsupp.apply_linearCombination, smul_smul, permTup_apply, ← tupLC_smul_fun, ← tupLC_smul_fun]
  have key : ∀ τ₀ : TagSimp X, t (π i) = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ tupPre t (π i)) •
            (⇑(tupPermAll K X r π) ∘ fun τ : TagSimp X =>
              Finsupp.single (Function.update t (π i) τ) (1 : K)) τ) (tagBd K X τ₀)
        = Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ permExp X π t * (-1 : K) ^ tupPre (permTup π t) i) •
            Finsupp.single (Function.update (permTup π t) i τ) (1 : K)) (tagBd K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero => simp only [tagBd_zero, map_zero]
    | succ n =>
      rw [tagBd_succ_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain]
      refine tupLC_congr_fun K (fun σ' => ?_) _
      show ((-1 : K) ^ tupPre t (π i)) •
          tupPermAll K X r π (Finsupp.single (Function.update t (π i) ⟨n, σ'⟩) (1 : K))
        = ((-1 : K) ^ permExp X π t * (-1 : K) ^ tupPre (permTup π t) i) •
          Finsupp.single (Function.update (permTup π t) i ⟨n, σ'⟩) (1 : K)
      have hd : (⟨n, σ'⟩ : TagSimp X).1 + 1 = (t (π i)).1 := congrArg Sigma.fst h.symm
      rw [tupPermAll_single, smul_smul, tupPerm_sign K X π t i ⟨n, σ'⟩ hd, permTup_update]
  exact key (t (π i)) rfl

/-- **Every signed slot permutation is a chain map** on the full model. -/
theorem tupPermAll_mul_tupDAll (π : Equiv.Perm (Fin r)) :
    tupPermAll K X r π * tupDAll K X r = tupDAll K X r * tupPermAll K X r π := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  exact tupPermAll_tupDAll_single K X π t

/-- **Composition**: `tupPermAll π * tupPermAll ρ = tupPermAll (ρ * π)`. -/
theorem tupPermAll_mul (π ρ : Equiv.Perm (Fin r)) :
    tupPermAll K X r π * tupPermAll K X r ρ = tupPermAll K X r (ρ * π) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  simp only [tupPermAll_single, map_smul, smul_smul, permTup_mul]
  congr 1
  rw [← pow_add]
  exact (neg_one_pow_eq_of_add_two_mul _ (permExp_mul X π ρ t).symm).symm

theorem tupPermAll_one : tupPermAll K X r 1 = 1 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rw [tupPermAll_single, permExp_one, pow_zero, one_smul]
  rfl

/-- **The cyclic operator is the signed permutation `finRotate r`.** -/
theorem tupTAll_eq_tupPermAll : tupTAll K X r = tupPermAll K X r (finRotate r) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupTAll_single, tupPermAll_single, rotExp_eq_permExp]
  rfl

/-! ## 4. The degree-`k` carrier -/

theorem permTup_tot {k : ℕ} (π : Equiv.Perm (Fin r)) (t : TupIdx X r k) :
    ∑ j : Fin r, (permTup π t.1 j).1 = k :=
  (Equiv.sum_comp π (fun j => (t.1 j).1)).trans t.2

/-- The permutation on degree-`k` indices. -/
def permTupIdx {k : ℕ} (π : Equiv.Perm (Fin r)) (t : TupIdx X r k) : TupIdx X r k :=
  ⟨permTup π t.1, permTup_tot X π t⟩

@[simp] theorem permTupIdx_val {k : ℕ} (π : Equiv.Perm (Fin r)) (t : TupIdx X r k) :
    (permTupIdx X π t).1 = permTup π t.1 := rfl

/-- **The signed slot permutation on the `r`-fold tensor power in degree `k`.** -/
def tupPerm (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) (π : Equiv.Perm (Fin r)) :
    Module.End K (tupMod K X r k) :=
  Finsupp.linearCombination K
    (fun t : TupIdx X r k => ((-1 : K) ^ permExp X π t.1) • Finsupp.single (permTupIdx X π t) (1 : K))

theorem tupPerm_single {k : ℕ} (π : Equiv.Perm (Fin r)) (t : TupIdx X r k) :
    tupPerm K X r k π (Finsupp.single t (1 : K))
      = ((-1 : K) ^ permExp X π t.1) • Finsupp.single (permTupIdx X π t) (1 : K) := by
  rw [tupPerm, Finsupp.linearCombination_single, one_smul]

theorem tupIncl_comp_tupPerm (k : ℕ) (π : Equiv.Perm (Fin r)) :
    (tupIncl K X r k).comp (tupPerm K X r k π) = (tupPermAll K X r π).comp (tupIncl K X r k) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupPerm_single, map_smul, tupIncl_single, tupIncl_single, tupPermAll_single, permTupIdx_val]

/-- **The signed slot permutation is a chain map** in every degree. -/
theorem tupPerm_tupD (k : ℕ) (π : Equiv.Perm (Fin r)) (x : tupMod K X r (k + 1)) :
    tupPerm K X r k π (tupD K X r k x) = tupD K X r k (tupPerm K X r (k + 1) π x) := by
  apply tupIncl_injective K X k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupPerm K X k π) (tupD K X r k x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) x
  have h3 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) (tupPerm K X r (k + 1) π x)
  have h4 := LinearMap.congr_fun (tupIncl_comp_tupPerm K X (k + 1) π) x
  simp only [LinearMap.comp_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact LinearMap.congr_fun (tupPermAll_mul_tupDAll K X π) (tupIncl K X r (k + 1) x)

/-- **Composition** in degree `k`. -/
theorem tupPerm_mul (k : ℕ) (π ρ : Equiv.Perm (Fin r)) :
    tupPerm K X r k π * tupPerm K X r k ρ = tupPerm K X r k (ρ * π) := by
  apply LinearMap.ext
  intro x
  apply tupIncl_injective K X k
  rw [Module.End.mul_apply]
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupPerm K X k π) (tupPerm K X r k ρ x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupPerm K X k ρ) x
  have h3 := LinearMap.congr_fun (tupIncl_comp_tupPerm K X k (ρ * π)) x
  simp only [LinearMap.comp_apply] at h1 h2 h3
  rw [h1, h2, h3, ← Module.End.mul_apply, tupPermAll_mul]

/-- The cyclic operator in degree `k` is the signed permutation `finRotate r`. -/
theorem tupT_eq_tupPerm (k : ℕ) : tupT K X r k = tupPerm K X r k (finRotate r) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupT_single, tupPerm_single, rotExp_eq_permExp]
  rfl

end FullModel

/-! ## 5. The riffle and the blockwise rotation -/

section Riffle

/-- The source slot of new slot `i` under the riffle of `2m` slots: `2j ↦ j`, `2j + 1 ↦ m + j`. -/
def riffleSrc (m i : ℕ) : ℕ := if i % 2 = 0 then i / 2 else m + i / 2

/-- The new slot of old slot `j` under the riffle: `j ↦ 2j` for `j < m`, `m + j ↦ 2j + 1`. -/
def riffleTgt (m j : ℕ) : ℕ := if j < m then 2 * j else 2 * (j - m) + 1

theorem riffleSrc_lt {m i : ℕ} (hi : i < 2 * m) : riffleSrc m i < 2 * m := by
  unfold riffleSrc
  split_ifs <;> omega

theorem riffleTgt_lt {m j : ℕ} (hj : j < 2 * m) : riffleTgt m j < 2 * m := by
  unfold riffleTgt
  split_ifs <;> omega

/-- **The riffle of slots**, `x₁ … x_m y₁ … y_m ↦ x₁ y₁ … x_m y_m`: new slot `2j` holds old slot `j`
and new slot `2j + 1` holds old slot `m + j`. -/
def riffleEquiv (m : ℕ) : Equiv.Perm (Fin (2 * m)) where
  toFun i := ⟨riffleSrc m i, riffleSrc_lt i.2⟩
  invFun j := ⟨riffleTgt m j, riffleTgt_lt j.2⟩
  left_inv i := by
    apply Fin.ext
    show riffleTgt m (riffleSrc m (i : ℕ)) = (i : ℕ)
    have := i.2
    unfold riffleTgt riffleSrc
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    show riffleSrc m (riffleTgt m (j : ℕ)) = (j : ℕ)
    have := j.2
    unfold riffleTgt riffleSrc
    split_ifs <;> omega

theorem riffleEquiv_val (m : ℕ) (i : Fin (2 * m)) :
    ((riffleEquiv m i : Fin (2 * m)) : ℕ) = riffleSrc m (i : ℕ) := rfl

/-- The source slot of new slot `i` under the blockwise rotation: each block of `m` slots is
rotated by one, slot `0` of the block to its end. -/
def blockRotSrc (m i : ℕ) : ℕ :=
  if i < m then (if i + 1 = m then 0 else i + 1) else (if i + 1 = 2 * m then m else i + 1)

def blockRotTgt (m j : ℕ) : ℕ :=
  if j < m then (if j = 0 then m - 1 else j - 1) else (if j = m then 2 * m - 1 else j - 1)

theorem blockRotSrc_lt {m i : ℕ} (hi : i < 2 * m) : blockRotSrc m i < 2 * m := by
  unfold blockRotSrc
  split_ifs <;> omega

theorem blockRotTgt_lt {m j : ℕ} (hj : j < 2 * m) : blockRotTgt m j < 2 * m := by
  unfold blockRotTgt
  split_ifs <;> omega

/-- **The blockwise rotation** `x₁ … x_m y₁ … y_m ↦ x₂ … x_m x₁ y₂ … y_m y₁`. -/
def blockRotEquiv (m : ℕ) : Equiv.Perm (Fin (2 * m)) where
  toFun i := ⟨blockRotSrc m i, blockRotSrc_lt i.2⟩
  invFun j := ⟨blockRotTgt m j, blockRotTgt_lt j.2⟩
  left_inv i := by
    apply Fin.ext
    show blockRotTgt m (blockRotSrc m (i : ℕ)) = (i : ℕ)
    have := i.2
    unfold blockRotTgt blockRotSrc
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    show blockRotSrc m (blockRotTgt m (j : ℕ)) = (j : ℕ)
    have := j.2
    unfold blockRotTgt blockRotSrc
    split_ifs <;> omega

theorem blockRotEquiv_val (m : ℕ) (i : Fin (2 * m)) :
    ((blockRotEquiv m i : Fin (2 * m)) : ℕ) = blockRotSrc m (i : ℕ) := rfl

/-- **The group identity behind the conjugation**: rotating each block and riffling is riffling and
moving the first pair to the end. -/
theorem blockRotEquiv_mul_riffleEquiv (m : ℕ) :
    blockRotEquiv m * riffleEquiv m
      = riffleEquiv m * (finRotate (2 * m) * finRotate (2 * m)) := by
  refine Equiv.ext fun i => Fin.ext ?_
  have hi := i.2
  simp only [Equiv.Perm.mul_apply, riffleEquiv_val, blockRotEquiv_val, finRotate_val_eq_ite]
  unfold riffleSrc blockRotSrc
  split_ifs <;> omega

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The riffle on the full model**, with its Koszul sign. -/
def tupRiffleAll (m : ℕ) : Module.End K (tupAllMod K X (2 * m)) :=
  tupPermAll K X (2 * m) (riffleEquiv m)

/-- **The blockwise rotation on the full model**, with its Koszul sign. -/
def tupBlockRotAll (m : ℕ) : Module.End K (tupAllMod K X (2 * m)) :=
  tupPermAll K X (2 * m) (blockRotEquiv m)

theorem tupRiffleAll_mul_tupDAll (m : ℕ) :
    tupRiffleAll K X m * tupDAll K X (2 * m) = tupDAll K X (2 * m) * tupRiffleAll K X m :=
  tupPermAll_mul_tupDAll K X (riffleEquiv m)

theorem tupBlockRotAll_mul_tupDAll (m : ℕ) :
    tupBlockRotAll K X m * tupDAll K X (2 * m) = tupDAll K X (2 * m) * tupBlockRotAll K X m :=
  tupPermAll_mul_tupDAll K X (blockRotEquiv m)

/-- **`R ∘ B = T² ∘ R`**: the riffle carries the blockwise rotation to the rotation of pairs. -/
theorem tupRiffleAll_conj (m : ℕ) :
    tupRiffleAll K X m * tupBlockRotAll K X m = tupTAll K X (2 * m) ^ 2 * tupRiffleAll K X m := by
  rw [tupRiffleAll, tupBlockRotAll, tupPermAll_mul, pow_two, tupTAll_eq_tupPermAll, tupPermAll_mul,
    tupPermAll_mul, blockRotEquiv_mul_riffleEquiv]

/-- The riffle in degree `k`. -/
def tupRiffle (m k : ℕ) : Module.End K (tupMod K X (2 * m) k) :=
  tupPerm K X (2 * m) k (riffleEquiv m)

/-- The blockwise rotation in degree `k`. -/
def tupBlockRot (m k : ℕ) : Module.End K (tupMod K X (2 * m) k) :=
  tupPerm K X (2 * m) k (blockRotEquiv m)

theorem tupIncl_comp_tupRiffle (m k : ℕ) :
    (tupIncl K X (2 * m) k).comp (tupRiffle K X m k)
      = (tupRiffleAll K X m).comp (tupIncl K X (2 * m) k) :=
  tupIncl_comp_tupPerm K X k (riffleEquiv m)

theorem tupIncl_comp_tupBlockRot (m k : ℕ) :
    (tupIncl K X (2 * m) k).comp (tupBlockRot K X m k)
      = (tupBlockRotAll K X m).comp (tupIncl K X (2 * m) k) :=
  tupIncl_comp_tupPerm K X k (blockRotEquiv m)

theorem tupRiffle_tupD (m k : ℕ) (x : tupMod K X (2 * m) (k + 1)) :
    tupRiffle K X m k (tupD K X (2 * m) k x) = tupD K X (2 * m) k (tupRiffle K X m (k + 1) x) :=
  tupPerm_tupD K X k (riffleEquiv m) x

theorem tupBlockRot_tupD (m k : ℕ) (x : tupMod K X (2 * m) (k + 1)) :
    tupBlockRot K X m k (tupD K X (2 * m) k x)
      = tupD K X (2 * m) k (tupBlockRot K X m (k + 1) x) :=
  tupPerm_tupD K X k (blockRotEquiv m) x

/-- **`R ∘ B = T² ∘ R` in degree `k`.** -/
theorem tupRiffle_conj (m k : ℕ) :
    tupRiffle K X m k * tupBlockRot K X m k = tupT K X (2 * m) k ^ 2 * tupRiffle K X m k := by
  rw [tupRiffle, tupBlockRot, tupPerm_mul, pow_two, tupT_eq_tupPerm, tupPerm_mul, tupPerm_mul,
    blockRotEquiv_mul_riffleEquiv]

end Riffle

end

#audit_axioms tupPermAll_mul_tupDAll
#audit_axioms tupPermAll_mul
#audit_axioms tupTAll_eq_tupPermAll
#audit_axioms tupPerm_tupD
#audit_axioms tupRiffleAll_conj
#audit_axioms tupRiffle_conj

end GroupApproximation.CharClass
