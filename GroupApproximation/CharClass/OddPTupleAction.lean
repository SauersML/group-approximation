import GroupApproximation.CharClass.OddPTupleD
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.Nat.Even

/-!
# The cyclic action on the flat `r`-fold tensor power

`tupT` moves slot `0` of a tuple to the end, with the Koszul sign of moving a degree-`n₀` element
past the rest, `(-1)^{n₀ (N - n₀)}` where `N` is the total degree.  The direction is fixed on
purpose (plan §3.2, corrected 2026-09-10 on `sp-descent`'s finding): the descent's `eT` is this
operator at the two-letter alphabet, so `(T - 1)` transcribes with no inversion.

## Main results

* `tupT_tupD` — `tupT` is a chain map: `T ∘ d = d ∘ T`, with no sign.
* `tupT_pow_card` — `tupT ^ r = 1` **for every arity `r`**, with no hypothesis on `r`: `r`
  applications accumulate `(-1)^{Σ_s n_s (N - n_s)}`, and `Σ n_s (N - n_s) ≡ N² - N` is even.

Both are proved on the full model `tupAllMod` of `OddPTupleD.lean` and transported along the
injective `tupIncl`.

## Design

Degrees of slots are read as a function `tupDeg t : ℕ → ℕ` (zero past the arity), so every prefix
and total is a `Finset.range` sum of naturals, and the rotation is the shift `l ↦ (l + 1) % r` of
that function.  No `Fin` arithmetic survives past `finRotate_val_eq`.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Degrees, prefixes and totals as `range` sums -/

section Degrees

variable {X : TopCat.{0}} {r : ℕ}

/-- The value of `finRotate r j` is `(j + 1) % r`. -/
theorem finRotate_val_eq (j : Fin r) : ((finRotate r j : Fin r) : ℕ) = (j.val + 1) % r := by
  cases r with
  | zero => exact j.elim0
  | succ m =>
    have h := coe_finRotate j
    rw [h]
    split_ifs with hj
    · have hv : j.val = m := congrArg Fin.val hj
      rw [hv, Nat.mod_self]
    · have hv : j.val < m := Fin.val_lt_last hj
      rw [Nat.mod_eq_of_lt (show j.val + 1 < m + 1 by omega)]

/-- The degree of slot `l`, and `0` past the arity. -/
def tupDeg (t : TupAll X r) (l : ℕ) : ℕ := if h : l < r then (t ⟨l, h⟩).1 else 0

theorem tupDeg_val (t : TupAll X r) (j : Fin r) : tupDeg t j.val = (t j).1 :=
  dif_pos j.2

theorem tupDeg_of_le (t : TupAll X r) {l : ℕ} (hl : r ≤ l) : tupDeg t l = 0 :=
  dif_neg (show ¬ l < r by omega)

/-- The prefix at slot `j` is the `range` sum of the slot degrees below `j`. -/
theorem tupPre_eq_sum_range (t : TupAll X r) (j : Fin r) :
    tupPre t j = ∑ l ∈ Finset.range j.val, tupDeg t l := by
  have hmap : (Finset.Iio j).map Fin.valEmbedding = Finset.range j.val := by
    rw [Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
  rw [tupPre, ← hmap, Finset.sum_map]
  exact Finset.sum_congr rfl fun l _ => (tupDeg_val t l).symm

/-- The total degree is the `range` sum of the slot degrees. -/
theorem tupTot_eq_sum_range (t : TupAll X r) :
    ∑ j : Fin r, (t j).1 = ∑ l ∈ Finset.range r, tupDeg t l := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => (tupDeg_val t j).symm

theorem tupDeg_le_tot (t : TupAll X r) (l : ℕ) : tupDeg t l ≤ ∑ j : Fin r, (t j).1 := by
  by_cases hl : l < r
  · rw [tupTot_eq_sum_range]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hl)
  · rw [tupDeg_of_le t (show r ≤ l by omega)]
    exact Nat.zero_le _

theorem tupDeg_update_self (t : TupAll X r) (j : Fin r) (τ : TagSimp X) :
    tupDeg (Function.update t j τ) j.val = τ.1 := by
  rw [tupDeg_val, Function.update_self]

theorem tupDeg_update_of_ne (t : TupAll X r) (j : Fin r) (τ : TagSimp X) {l : ℕ}
    (hl : l ≠ j.val) : tupDeg (Function.update t j τ) l = tupDeg t l := by
  by_cases h : l < r
  · simp only [tupDeg, dif_pos h]
    rw [Function.update_of_ne]
    intro he
    exact hl (congrArg Fin.val he)
  · simp only [tupDeg, dif_neg h]

/-- Replacing slot `j` by a tag one degree lower drops the total degree by one. -/
theorem tupTot_update_succ (t : TupAll X r) (j : Fin r) (τ : TagSimp X)
    (hd : τ.1 + 1 = (t j).1) :
    ∑ l : Fin r, (Function.update t j τ l).1 + 1 = ∑ l : Fin r, (t l).1 := by
  have hj : j ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ j
  have hrest : ∀ m ∈ (Finset.univ : Finset (Fin r)).erase j,
      (Function.update t j τ m).1 = (t m).1 := by
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  have e1 : ∑ l : Fin r, (Function.update t j τ l).1
      = τ.1 + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t m).1 := by
    rw [← Finset.add_sum_erase _ _ hj, Function.update_self]
    exact congrArg (fun z => τ.1 + z) (Finset.sum_congr rfl hrest)
  have e2 : ∑ l : Fin r, (t l).1
      = (t j).1 + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t m).1 :=
    (Finset.add_sum_erase _ _ hj).symm
  omega

end Degrees

/-! ## 2. The rotation -/

section Rotation

variable {X : TopCat.{0}} {r : ℕ}

/-- **Slot `0` to the end**: `(tupRot t) j = t (j + 1)`. -/
def tupRot (t : TupAll X r) : TupAll X r := t ∘ finRotate r

theorem tupRot_apply (t : TupAll X r) (j : Fin r) : tupRot t j = t (finRotate r j) := rfl

theorem tupDeg_tupRot (t : TupAll X r) {l : ℕ} (hl : l < r) :
    tupDeg (tupRot t) l = tupDeg t ((l + 1) % r) := by
  have hl' : (l + 1) % r < r := Nat.mod_lt _ (by omega)
  unfold tupDeg
  rw [dif_pos hl, dif_pos hl', tupRot_apply]
  have he : finRotate r ⟨l, hl⟩ = ⟨(l + 1) % r, hl'⟩ := Fin.ext (finRotate_val_eq _)
  rw [he]

/-- Rotation preserves the total degree. -/
theorem tupTot_tupRot (t : TupAll X r) : ∑ j : Fin r, (tupRot t j).1 = ∑ j : Fin r, (t j).1 :=
  Equiv.sum_comp (finRotate r) (fun j => (t j).1)

/-- Updating slot `finRotate r i` and rotating is rotating and updating slot `i`. -/
theorem tupRot_update (t : TupAll X r) (i : Fin r) (τ : TagSimp X) :
    tupRot (Function.update t (finRotate r i) τ) = Function.update (tupRot t) i τ := by
  have h := Function.update_comp_equiv t (finRotate r) (finRotate r i) τ
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The prefix of the rotated tuple at slot `i` sums the degrees of slots `1, …, i`. -/
theorem tupPre_tupRot (t : TupAll X r) (i : Fin r) :
    tupPre (tupRot t) i = ∑ l ∈ Finset.range i.val, tupDeg t (l + 1) := by
  rw [tupPre_eq_sum_range]
  have hi := i.2
  refine Finset.sum_congr rfl fun l hl => ?_
  have hli : l < i.val := Finset.mem_range.mp hl
  rw [tupDeg_tupRot t (show l < r by omega), Nat.mod_eq_of_lt (show l + 1 < r by omega)]

theorem tupRot_iterate_apply (s : ℕ) (t : TupAll X r) (j : Fin r) :
    (tupRot^[s] t) j = t ⟨(j.val + s) % r, Nat.mod_lt _ j.pos⟩ := by
  induction s generalizing j with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact congrArg t (Fin.ext (Nat.mod_eq_of_lt j.2).symm)
  | succ s ih =>
    rw [Function.iterate_succ_apply', tupRot_apply, ih]
    refine congrArg t (Fin.ext ?_)
    show ((finRotate r j : Fin r).val + s) % r = (j.val + (s + 1)) % r
    rw [finRotate_val_eq, Nat.mod_add_mod, show j.val + 1 + s = j.val + (s + 1) by omega]

theorem tupRot_iterate_card (t : TupAll X r) : tupRot^[r] t = t := by
  funext j
  rw [tupRot_iterate_apply]
  refine congrArg t (Fin.ext ?_)
  show (j.val + r) % r = j.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

theorem tupDeg_tupRot_iterate_zero (s : ℕ) (t : TupAll X r) (hs : s < r) :
    tupDeg (tupRot^[s] t) 0 = tupDeg t s := by
  unfold tupDeg
  rw [dif_pos (show 0 < r by omega), dif_pos hs, tupRot_iterate_apply]
  refine congrArg (fun z : Fin r => (t z).1) (Fin.ext ?_)
  show (0 + s) % r = s
  rw [Nat.zero_add, Nat.mod_eq_of_lt hs]

theorem tupTot_tupRot_iterate (s : ℕ) (t : TupAll X r) :
    ∑ j : Fin r, ((tupRot^[s] t) j).1 = ∑ j : Fin r, (t j).1 := by
  induction s with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply', tupTot_tupRot, ih]

end Rotation

/-! ## 3. Two sign helpers -/

/-- Exponents that differ by an even number give the same sign. -/
theorem neg_one_pow_add_two_mul {K : Type} [Ring K] (a e : ℕ) :
    (-1 : K) ^ (a + 2 * e) = (-1 : K) ^ a := by
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem neg_one_pow_eq_of_add_two_mul {K : Type} [Ring K] {a c : ℕ} (e : ℕ)
    (h : a + 2 * e = c) : (-1 : K) ^ a = (-1 : K) ^ c := by
  rw [← h, neg_one_pow_add_two_mul]

/-! ## 4. The operator on the full model -/

section FullModel

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

/-- The Koszul exponent of moving slot `0` past the rest: `n₀ · (N − n₀)`. -/
def rotExp (t : TupAll X r) : ℕ := tupDeg t 0 * (∑ j : Fin r, (t j).1 - tupDeg t 0)

/-- The cyclic operator on the full model. -/
def tupTAll (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) : Module.End K (tupAllMod K X r) :=
  Finsupp.linearCombination K
    (fun t : TupAll X r => ((-1 : K) ^ rotExp X t) • Finsupp.single (tupRot t) (1 : K))

theorem tupTAll_single (t : TupAll X r) :
    tupTAll K X r (Finsupp.single t (1 : K))
      = ((-1 : K) ^ rotExp X t) • Finsupp.single (tupRot t) (1 : K) := by
  rw [tupTAll, Finsupp.linearCombination_single, one_smul]

/-- **The sign identity behind `T ∘ d = d ∘ T`**, for one slot `j = finRotate r i` and one face
`τ` of it. -/
theorem tupT_sign (t : TupAll X r) (i : Fin r) (τ : TagSimp X)
    (hd : τ.1 + 1 = (t (finRotate r i)).1) :
    (-1 : K) ^ tupPre t (finRotate r i) * (-1 : K) ^ rotExp X (Function.update t (finRotate r i) τ)
      = (-1 : K) ^ rotExp X t * (-1 : K) ^ tupPre (tupRot t) i := by
  rw [← pow_add, ← pow_add]
  have hr : 0 < r := i.pos
  set j := finRotate r i
  have hjv : j.val = (i.val + 1) % r := finRotate_val_eq i
  have htot := tupTot_update_succ t j τ hd
  set N := ∑ l : Fin r, (t l).1 with hN
  set N' := ∑ l : Fin r, (Function.update t j τ l).1 with hN'
  have hdj : tupDeg t j.val = τ.1 + 1 := by rw [tupDeg_val]; exact hd.symm
  rw [tupPre_tupRot, tupPre_eq_sum_range]
  unfold rotExp
  rw [← hN, ← hN']
  have hi2 := i.2
  by_cases hlast : i.val + 1 = r
  · -- slot `0` is differentiated
    have hj0 : j.val = 0 := by rw [hjv, hlast, Nat.mod_self]
    have hi : i.val = r - 1 := by omega
    have hd0 : tupDeg t 0 = τ.1 + 1 := by
      have h' := hdj
      rwa [hj0] at h'
    have hu0 : tupDeg (Function.update t j τ) 0 = τ.1 := by
      have h' := tupDeg_update_self t j τ
      rwa [hj0] at h'
    have hrest : ∑ l ∈ Finset.range i.val, tupDeg t (l + 1) + tupDeg t 0 = N := by
      rw [hN, tupTot_eq_sum_range, hi]
      have h' := Finset.sum_range_succ' (fun l => tupDeg t l) (r - 1)
      rw [Nat.sub_add_cancel hr] at h'
      exact h'.symm
    rw [hj0, Finset.sum_range_zero, hu0, hd0]
    set R := ∑ l ∈ Finset.range i.val, tupDeg t (l + 1)
    refine neg_one_pow_eq_of_add_two_mul R ?_
    have h1 : N - (τ.1 + 1) = R := by omega
    have h2 : N' - τ.1 = R := by omega
    rw [h1, h2]
    ring
  · -- a later slot is differentiated
    have hjv' : j.val = i.val + 1 := by
      rw [hjv, Nat.mod_eq_of_lt (show i.val + 1 < r by omega)]
    have hu0 : tupDeg (Function.update t j τ) 0 = tupDeg t 0 :=
      tupDeg_update_of_ne t j τ (show 0 ≠ j.val by omega)
    have hle : tupDeg t 0 ≤ N' := by
      rw [← hu0]
      exact tupDeg_le_tot (Function.update t j τ) 0
    rw [hjv', Finset.sum_range_succ', hu0]
    set P := ∑ l ∈ Finset.range i.val, tupDeg t (l + 1)
    set d0 := tupDeg t 0
    have h1 : N - d0 = (N' - d0) + 1 := by omega
    rw [h1]
    congr 1
    ring

/-- **`T ∘ d = d ∘ T` on a basis element of the full model.** -/
theorem tupTAll_tupDAll_single (t : TupAll X r) :
    tupTAll K X r (tupDAll K X r (Finsupp.single t (1 : K)))
      = tupDAll K X r (tupTAll K X r (Finsupp.single t (1 : K))) := by
  rw [tupTAll_single, map_smul, tupDAll, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.smul_sum]
  rw [← Equiv.sum_comp (finRotate r) (fun j : Fin r => tupTAll K X r (slotBd K X j
    (Finsupp.single t (1 : K))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotBd_single, slotBd_single, slotBdGen, slotBdGen, map_smul,
    Finsupp.apply_linearCombination, smul_smul, tupRot_apply, ← tupLC_smul_fun, ← tupLC_smul_fun]
  have key : ∀ τ₀ : TagSimp X, t (finRotate r i) = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ tupPre t (finRotate r i)) •
            (⇑(tupTAll K X r) ∘ fun τ : TagSimp X =>
              Finsupp.single (Function.update t (finRotate r i) τ) (1 : K)) τ) (tagBd K X τ₀)
        = Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ rotExp X t * (-1 : K) ^ tupPre (tupRot t) i) •
            Finsupp.single (Function.update (tupRot t) i τ) (1 : K)) (tagBd K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero => simp only [tagBd_zero, map_zero]
    | succ n =>
      rw [tagBd_succ_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain]
      refine tupLC_congr_fun K (fun σ' => ?_) _
      show ((-1 : K) ^ tupPre t (finRotate r i)) •
          tupTAll K X r (Finsupp.single (Function.update t (finRotate r i) ⟨n, σ'⟩) (1 : K))
        = ((-1 : K) ^ rotExp X t * (-1 : K) ^ tupPre (tupRot t) i) •
          Finsupp.single (Function.update (tupRot t) i ⟨n, σ'⟩) (1 : K)
      have hd : (⟨n, σ'⟩ : TagSimp X).1 + 1 = (t (finRotate r i)).1 := congrArg Sigma.fst h.symm
      rw [tupTAll_single, smul_smul, tupT_sign K X t i ⟨n, σ'⟩ hd, tupRot_update]
  exact key (t (finRotate r i)) rfl

theorem tupTAll_mul_tupDAll : tupTAll K X r * tupDAll K X r = tupDAll K X r * tupTAll K X r := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  exact tupTAll_tupDAll_single K X t

/-! ## 5. `T ^ r = 1` -/

theorem tupTAll_pow_single (m : ℕ) (t : TupAll X r) :
    (tupTAll K X r ^ m) (Finsupp.single t (1 : K))
      = ((-1 : K) ^ (∑ s ∈ Finset.range m, rotExp X (tupRot^[s] t))) •
          Finsupp.single (tupRot^[m] t) (1 : K) := by
  induction m with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Finset.sum_range_zero, one_smul,
      Function.iterate_zero_apply]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, tupTAll_single, smul_smul,
      Finset.sum_range_succ, pow_add, Function.iterate_succ_apply']

/-- The accumulated exponent of `r` rotations is even. -/
theorem even_sum_rotExp (t : TupAll X r) :
    Even (∑ s ∈ Finset.range r, rotExp X (tupRot^[s] t)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = ∑ j : Fin r, (t j).1 := ⟨_, rfl⟩
  have hterm : ∀ s ∈ Finset.range r,
      rotExp X (tupRot^[s] t) = tupDeg t s * (N - tupDeg t s) := by
    intro s hs
    have hs' : s < r := Finset.mem_range.mp hs
    rw [rotExp, tupTot_tupRot_iterate, ← hN, tupDeg_tupRot_iterate_zero s t hs']
  rw [Finset.sum_congr rfl hterm]
  have hsum : ∑ s ∈ Finset.range r, tupDeg t s = N := by
    rw [hN, tupTot_eq_sum_range]
  have hle : ∀ s, tupDeg t s ≤ N := fun s => by
    rw [hN]
    exact tupDeg_le_tot t s
  -- `d (N - d) + d · d = d N`, summed: `S + Σ d² = N²`
  have hsq : ∀ d : ℕ, d * d = d + d * (d - 1) := by
    intro d
    cases d with
    | zero => rfl
    | succ n => rw [Nat.add_sub_cancel]; ring
  have hS : ∑ s ∈ Finset.range r, tupDeg t s * (N - tupDeg t s)
      + (N + ∑ s ∈ Finset.range r, tupDeg t s * (tupDeg t s - 1)) = N + N * (N - 1) := by
    rw [← hsq N]
    have h1 : ∑ s ∈ Finset.range r, tupDeg t s * (N - tupDeg t s)
        + ∑ s ∈ Finset.range r, tupDeg t s * tupDeg t s = N * N := by
      rw [← Finset.sum_add_distrib]
      have h2 : ∀ s ∈ Finset.range r,
          tupDeg t s * (N - tupDeg t s) + tupDeg t s * tupDeg t s = tupDeg t s * N := by
        intro s _
        rw [← Nat.mul_add, Nat.sub_add_cancel (hle s)]
      rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, hsum]
    have h3 : ∑ s ∈ Finset.range r, tupDeg t s * tupDeg t s
        = N + ∑ s ∈ Finset.range r, tupDeg t s * (tupDeg t s - 1) := by
      rw [Finset.sum_congr rfl fun s _ => hsq (tupDeg t s), Finset.sum_add_distrib, hsum]
    rw [← h1, h3]
  have hE1 : Even (∑ s ∈ Finset.range r, tupDeg t s * (tupDeg t s - 1)) :=
    Finset.sum_induction _ Even (fun _ _ ha hb => ha.add hb) ⟨0, rfl⟩
      fun s _ => Nat.even_mul_pred_self (tupDeg t s)
  have hE2 : Even (N * (N - 1)) := Nat.even_mul_pred_self N
  have hcancel : ∑ s ∈ Finset.range r, tupDeg t s * (N - tupDeg t s)
      + ∑ s ∈ Finset.range r, tupDeg t s * (tupDeg t s - 1) = N * (N - 1) := by omega
  have hE3 : Even (∑ s ∈ Finset.range r, tupDeg t s * (N - tupDeg t s)
      + ∑ s ∈ Finset.range r, tupDeg t s * (tupDeg t s - 1)) := by
    rw [hcancel]
    exact hE2
  exact (Nat.even_add.mp hE3).mpr hE1

theorem tupTAll_pow_card : tupTAll K X r ^ r = 1 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rw [tupTAll_pow_single, (even_sum_rotExp X t).neg_one_pow, one_smul, tupRot_iterate_card]

/-! ## 6. The degree-`k` carrier -/

theorem tupTot_tupRot_idx {k : ℕ} (t : TupIdx X r k) : ∑ j : Fin r, (tupRot t.1 j).1 = k :=
  (tupTot_tupRot t.1).trans t.2

/-- The rotation on degree-`k` indices. -/
def tupRotIdx {k : ℕ} (t : TupIdx X r k) : TupIdx X r k := ⟨tupRot t.1, tupTot_tupRot_idx X t⟩

@[simp] theorem tupRotIdx_val {k : ℕ} (t : TupIdx X r k) : (tupRotIdx X t).1 = tupRot t.1 := rfl

/-- **The cyclic operator on the `r`-fold tensor power in degree `k`**: slot `0` to the end, with
the Koszul sign `(-1)^{n₀ (k − n₀)}`. -/
def tupT (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) : Module.End K (tupMod K X r k) :=
  Finsupp.linearCombination K
    (fun t : TupIdx X r k => ((-1 : K) ^ rotExp X t.1) • Finsupp.single (tupRotIdx X t) (1 : K))

theorem tupT_single {k : ℕ} (t : TupIdx X r k) :
    tupT K X r k (Finsupp.single t (1 : K))
      = ((-1 : K) ^ rotExp X t.1) • Finsupp.single (tupRotIdx X t) (1 : K) := by
  rw [tupT, Finsupp.linearCombination_single, one_smul]

theorem tupIncl_comp_tupT (k : ℕ) :
    (tupIncl K X r k).comp (tupT K X r k) = (tupTAll K X r).comp (tupIncl K X r k) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [tupT_single, map_smul, tupIncl_single, tupIncl_single, tupTAll_single, tupRotIdx_val]

theorem tupIncl_tupT_pow (k m : ℕ) (x : tupMod K X r k) :
    tupIncl K X r k ((tupT K X r k ^ m) x) = (tupTAll K X r ^ m) (tupIncl K X r k x) := by
  induction m generalizing x with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact LinearMap.congr_fun (tupIncl_comp_tupT K X k) _

/-- **`T ^ r = 1`, at every arity.** -/
theorem tupT_pow_card (k : ℕ) : tupT K X r k ^ r = 1 := by
  apply LinearMap.ext
  intro x
  apply tupIncl_injective K X k
  rw [tupIncl_tupT_pow, tupTAll_pow_card, Module.End.one_apply, Module.End.one_apply]

/-- **`T` is a chain map.** -/
theorem tupT_tupD (k : ℕ) (x : tupMod K X r (k + 1)) :
    tupT K X r k (tupD K X r k x) = tupD K X r k (tupT K X r (k + 1) x) := by
  apply tupIncl_injective K X k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupT K X k) (tupD K X r k x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) x
  have h3 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) (tupT K X r (k + 1) x)
  have h4 := LinearMap.congr_fun (tupIncl_comp_tupT K X (k + 1)) x
  simp only [LinearMap.comp_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact LinearMap.congr_fun (tupTAll_mul_tupDAll K X) (tupIncl K X r (k + 1) x)

end FullModel

end

end GroupApproximation.CharClass
