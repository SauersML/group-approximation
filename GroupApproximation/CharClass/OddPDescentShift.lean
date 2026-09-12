import GroupApproximation.CharClass.OddPDescentComplex
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-!
# The cyclic shift and the norm on `E^{⊗p}`

The `ℤ/p`-action of the odd-primary construction, on the two-letter tensor power.

## The convention, and why it is load-bearing

`eT` is **`sp-design`'s** cyclic shift: slot `0` moves to the **end**, and the Koszul sign
is the degree of slot `0` times the degree of everything else, `(−1)^{d₀·(k − d₀)}`.  In
the exterior reading of `OddPDescentWord.lean` this is exactly the graded algebra
automorphism `ξ_j ↦ ξ_{j−1 mod p}` — VERIFIED against `sp-design`'s word model on every
basis element at `p = 3, 5, 7`.

`sp-steenrod`'s planned `tupT` (their report §3.2) reads the sign off the **last** slot,
which is the **inverse** shift.  The two are not interchangeable here: running the identical
descent with `T` replaced by `T⁻¹` — a consistent relabelling of the generator of `ℤ/p`,
under which `N` is unchanged — gives `1, 2, 6, 10` for `sp-design`'s direction at
`p = 3, 5, 7, 11` and `2, 2, 1, 1` for the other.  Both are units, so the programme is safe
either way, but `λ₁ = ((p−1)/2)!` is a theorem about **this** direction only.  The
asymmetry is real, not a bookkeeping slip: the contraction `eH = ∂/∂ξ_0` and the
Alexander–Whitney evaluation both single out slot `0`.

## What is proved here

* `eT_pow_card : eT ^ p = 1`, with **no hypothesis on `p` beyond `NeZero`** — the sign
  product telescopes to `(−1)^{k(k−1)}` because a letter's degree is `0` or `1`, so
  `d² = d`.  This is `sp-steenrod`'s `tupT_pow_card` for the two-letter alphabet.
* `eT_comp_eWedge : eT ∘ eWedge (a+1) = eWedge a ∘ eT`, the statement that `eT` is an
  algebra map.  This is the one genuinely delicate sign computation of the lane, and it
  splits on whether `a + 1` wraps to `0`.
* `eN := Σ_{k<p} eT^k` and `eN ∘ (eT − 1) = 0`, which is the telescoping identity
  `grNorm_mul_grS` of `OddPGroupRing.lean` transported to this module: the *same*
  `geom_sum_mul`, in the endomorphism ring instead of the group ring.  It is what makes
  every element of the descent a cocycle.
-/

namespace GroupApproximation.CharClass

-- The `ℕ → Fin p` coercion is a SCOPED instance (`Fin.NatCast`), deliberately not
-- global; without this `open` the ascription `(n : Fin p)` reports a bare type
-- mismatch with no mention of a missing instance.
open Fin.NatCast

variable {p : ℕ} [NeZero p]

/-! ## 0. Arithmetic in `Fin p` -/

theorem eOne_val (hp : 1 < p) : ((1 : Fin p) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt hp

/-- `l + 1` does not wrap when there is room. -/
theorem eSucc_val (hp : 1 < p) (l : Fin p) (h : (l : ℕ) + 1 < p) :
    ((l + 1 : Fin p) : ℕ) = (l : ℕ) + 1 := by
  have h1 : ((1 : Fin p) : ℕ) = 1 := eOne_val hp
  have hlt : (l : ℕ) + ((1 : Fin p) : ℕ) < p := by rw [h1]; exact h
  rw [Fin.val_add_eq_of_add_lt hlt, h1]

/-- `l + 1` does not wrap exactly when it is not `0`. -/
theorem eSucc_val' (hp : 1 < p) (l : Fin p) (h : l + 1 ≠ 0) :
    ((l + 1 : Fin p) : ℕ) = (l : ℕ) + 1 := by
  have h1 : ((1 : Fin p) : ℕ) = 1 := eOne_val hp
  have hite := Fin.val_add_eq_ite l (1 : Fin p)
  rw [h1] at hite
  by_cases hc : p ≤ (l : ℕ) + 1
  · exfalso
    refine h (Fin.ext ?_)
    have hl := l.isLt
    rw [hite, if_pos hc, Fin.val_zero]
    omega
  · rw [hite, if_neg hc]

/-- `l - 1` does not wrap when `l` is not `0`. -/
theorem ePred_val (hp : 1 < p) (l : Fin p) (h : 1 ≤ (l : ℕ)) :
    ((l - 1 : Fin p) : ℕ) = (l : ℕ) - 1 := by
  have hadd : (l - 1 : Fin p) + 1 = l := by abel
  have hne : (l - 1 : Fin p) + 1 ≠ 0 := by
    rw [hadd]
    intro hcon
    rw [hcon, Fin.val_zero] at h
    omega
  have hv := eSucc_val' hp (l - 1) hne
  rw [hadd] at hv
  omega

theorem eLast_val (hp : 1 < p) (a : Fin p) (h : a + 1 = 0) : (a : ℕ) + 1 = p := by
  have h1 : ((1 : Fin p) : ℕ) = 1 := eOne_val hp
  have hite := Fin.val_add_eq_ite a (1 : Fin p)
  rw [h1, h, Fin.val_zero] at hite
  have ha := a.isLt
  by_cases hc : p ≤ (a : ℕ) + 1
  · rw [if_pos hc] at hite; omega
  · rw [if_neg hc] at hite; omega

/-- `Iic a` is `Iio (a+1)` when `a + 1` does not wrap. -/
theorem eIic_eq_Iio_succ (hp : 1 < p) (a : Fin p) (h : a + 1 ≠ 0) :
    Finset.Iic a = Finset.Iio (a + 1) := by
  ext m
  simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def, eSucc_val' hp a h]
  omega

/-- `Iic a` is everything when `a` is the last slot. -/
theorem eIic_eq_univ (hp : 1 < p) (a : Fin p) (h : a + 1 = 0) :
    Finset.Iic a = Finset.univ := by
  have hv := eLast_val hp a h
  ext m
  simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
  have := m.isLt
  omega

/-- `Iic a` is `{0}` together with the shift of `Iio a`. -/
theorem eIic_eq_insert (hp : 1 < p) (a : Fin p) :
    Finset.Iic a = insert (0 : Fin p) ((Finset.Iio a).image (fun l => l + 1)) := by
  classical
  ext m
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_image, Finset.mem_Iio,
    Fin.le_def, Fin.lt_def]
  constructor
  · intro hm
    by_cases h0 : m = 0
    · exact Or.inl h0
    · refine Or.inr ⟨m - 1, ?_, ?_⟩
      · have hadd : (m - 1 : Fin p) + 1 = m := by abel
        have hne : (m - 1 : Fin p) + 1 ≠ 0 := by rw [hadd]; exact h0
        have hv := eSucc_val' hp (m - 1) hne
        rw [hadd] at hv
        omega
      · abel
  · rintro (rfl | ⟨l, hl, rfl⟩)
    · simp
    · have hlt : (l : ℕ) + 1 < p := by have := a.isLt; omega
      rw [eSucc_val hp l hlt]
      omega

/-- **Reindexing a prefix sum by the shift.**  `l + 1` never wraps for `l < a`, so the
image of `Iio a` is `Iic a` with the slot `0` removed — no case split. -/
theorem eSum_Iio_shift (hp : 1 < p) (f : Fin p → ℕ) (a : Fin p) :
    (∑ l ∈ Finset.Iio a, f (l + 1)) + f 0 = ∑ m ∈ Finset.Iic a, f m := by
  classical
  have h0 : (0 : Fin p) ∉ (Finset.Iio a).image (fun l => l + 1) := by
    simp only [Finset.mem_image, Finset.mem_Iio, not_exists, not_and]
    intro l hl heq
    have hlt : (l : ℕ) + 1 < p := by
      have := a.isLt; rw [Fin.lt_def] at hl; omega
    have hv := eSucc_val hp l hlt
    rw [heq, Fin.val_zero] at hv
    omega
  have hinj : ∀ x ∈ Finset.Iio a, ∀ y ∈ Finset.Iio a,
      (fun l : Fin p => l + 1) x = (fun l : Fin p => l + 1) y → x = y := by
    intro x _ y _ h
    exact add_right_cancel h
  rw [eIic_eq_insert hp a, Finset.sum_insert h0, Finset.sum_image hinj, add_comm]

/-! ## 1. The shift on words -/

/-- The slot rotation: slot `0` moves to the end. -/
def eRot (w : EWord p) : EWord p := fun j => w (j + 1)

@[simp] theorem eRot_apply (w : EWord p) (j : Fin p) : eRot w j = w (j + 1) := rfl

theorem eDeg_eRot (w : EWord p) : eDeg (eRot w) = eDeg w := by
  unfold eDeg
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin p))
    (fun j => eLetterDeg (eRot w j)) (fun j => eLetterDeg (w j)) fun _ => rfl

/-- Updating slot `a + 1` of `w` is updating slot `a` of the rotation. -/
theorem eRot_update (w : EWord p) (a : Fin p) (x : ELetter) :
    eRot (Function.update w (a + 1) x) = Function.update (eRot w) a x := by
  funext j
  by_cases h : j = a
  · subst h
    rw [eRot_apply, Function.update_self, Function.update_self]
  · have h' : j + 1 ≠ a + 1 := fun hh => h (add_right_cancel hh)
    rw [eRot_apply, Function.update_of_ne h', Function.update_of_ne h, eRot_apply]

theorem eRot_iterate (n : ℕ) (w : EWord p) : eRot^[n] w = fun j => w (j + (n : Fin p)) := by
  induction n with
  | zero => funext j; simp
  | succ n ih =>
      funext j
      rw [Function.iterate_succ_apply', ih]
      simp only [eRot_apply]
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
      abel

theorem eRot_iterate_card (w : EWord p) : eRot^[p] w = w := by
  rw [eRot_iterate, Fin.natCast_self]
  funext j
  rw [add_zero]

theorem eDeg_eRot_iterate (n : ℕ) (w : EWord p) : eDeg (eRot^[n] w) = eDeg w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', eDeg_eRot, ih]

omit [NeZero p] in
/-- Putting `g` into an empty slot raises the degree by one. -/
theorem eDeg_update_true (w : EWord p) (a : Fin p) (h : w a = false) :
    eDeg (Function.update w a true) = eDeg w + 1 := by
  classical
  have ha : a ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ a
  have hrest : ∀ m ∈ (Finset.univ : Finset (Fin p)).erase a,
      eLetterDeg (Function.update w a true m) = eLetterDeg (w m) := by
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  have e1 : eDeg (Function.update w a true)
      = 1 + ∑ m ∈ (Finset.univ : Finset (Fin p)).erase a, eLetterDeg (w m) := by
    rw [eDeg, ← Finset.add_sum_erase _ _ ha, Function.update_self, eLetterDeg_true]
    exact congrArg (fun z => 1 + z) (Finset.sum_congr rfl hrest)
  have e2 : eDeg w = eLetterDeg (w a)
      + ∑ m ∈ (Finset.univ : Finset (Fin p)).erase a, eLetterDeg (w m) :=
    (Finset.add_sum_erase _ _ ha).symm
  rw [h, eLetterDeg_false] at e2
  omega

omit [NeZero p] in
theorem eLetterDeg_le_eDeg (w : EWord p) (a : Fin p) : eLetterDeg (w a) ≤ eDeg w :=
  Finset.single_le_sum (f := fun j => eLetterDeg (w j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)

/-! ## 2. The shift on `E^{⊗p}` -/

variable (K : Type) [CommRing K]

/-- The Koszul sign of the cyclic shift: the degree of slot `0`, which is the letter that
travels, times the degree of everything it travels past. -/
noncomputable def eSgn (w : EWord p) : K :=
  (-1 : K) ^ (eLetterDeg (w 0) * (eDeg w - eLetterDeg (w 0)))

noncomputable def eTGen (w : EWord p) : EMod K p := eSgn K w • Finsupp.single (eRot w) (1 : K)

/-- **The cyclic shift of `E^{⊗p}`**, `sp-design`'s direction. -/
noncomputable def eT : EMod K p →ₗ[K] EMod K p := Finsupp.linearCombination K (eTGen K)

@[simp] theorem eT_single (w : EWord p) :
    eT K (Finsupp.single w (1 : K)) = eSgn K w • Finsupp.single (eRot w) (1 : K) := by
  rw [eT, Finsupp.linearCombination_single, one_smul, eTGen]

theorem eT_smul_single (c : K) (w : EWord p) :
    eT K (c • Finsupp.single w (1 : K)) = c • (eSgn K w • Finsupp.single (eRot w) (1 : K)) := by
  rw [map_smul, eT_single]

omit [NeZero p] in
/-- Two signs agree as soon as their exponents have the same parity. -/
theorem eNegOnePow_congr {A B : ℕ} (h : A % 2 = B % 2) :
    ((-1 : K)) ^ A = ((-1 : K)) ^ B := by
  rcases Nat.even_or_odd A with hA | hA
  · have hB : Even B := by rw [Nat.even_iff] at hA ⊢; omega
    rw [hA.neg_one_pow, hB.neg_one_pow]
  · have hB : Odd B := by rw [Nat.odd_iff] at hA ⊢; omega
    rw [hA.neg_one_pow, hB.neg_one_pow]

/-! ### `eT ^ p = 1` -/

theorem eT_pow_single (n : ℕ) (w : EWord p) :
    ((eT K) ^ n) (Finsupp.single w (1 : K))
      = (∏ i ∈ Finset.range n, eSgn K (eRot^[i] w)) • Finsupp.single (eRot^[n] w) (1 : K) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      have hword : eRot^[n] (eRot w) = eRot^[n + 1] w :=
        (Function.iterate_succ_apply eRot n w).symm
      have hprod : eSgn K w * (∏ i ∈ Finset.range n, eSgn K (eRot^[i] (eRot w)))
          = ∏ i ∈ Finset.range (n + 1), eSgn K (eRot^[i] w) := by
        rw [Finset.prod_range_succ']
        simp only [Function.iterate_zero_apply]
        rw [mul_comm]
        congr 1
      rw [pow_succ, Module.End.mul_apply, eT_single, map_smul, ih (eRot w), smul_smul,
        hprod, hword]

theorem eSgn_prod_card (w : EWord p) :
    (∏ i ∈ Finset.range p, eSgn K (eRot^[i] w)) = 1 := by
  have hterm : ∀ i ∈ Finset.range p,
      eSgn K (eRot^[i] w)
        = (-1 : K) ^ (eLetterDeg (w (i : Fin p))
            * (eDeg w - eLetterDeg (w (i : Fin p)))) := by
    intro i _
    have hd : eDeg (eRot^[i] w) = eDeg w := eDeg_eRot_iterate i w
    have h0 : (eRot^[i] w) 0 = w (i : Fin p) := by rw [eRot_iterate]; simp
    simp only [eSgn, hd, h0]
  have hsum : ∑ i ∈ Finset.range p,
      eLetterDeg (w (i : Fin p)) * (eDeg w - eLetterDeg (w (i : Fin p)))
      = eDeg w * (eDeg w - 1) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => eLetterDeg (w (i : Fin p))
        * (eDeg w - eLetterDeg (w (i : Fin p)))) p]
    have hpt : ∀ j : Fin p,
        eLetterDeg (w ((j : ℕ) : Fin p)) * (eDeg w - eLetterDeg (w ((j : ℕ) : Fin p)))
          = eLetterDeg (w j) * (eDeg w - 1) := by
      intro j
      rw [Fin.cast_val_eq_self]
      rcases Bool.dichotomy (w j) with h | h <;> rw [h] <;> simp
    rw [Finset.sum_congr rfl fun j _ => hpt j, ← Finset.sum_mul]
    rfl
  rw [Finset.prod_congr rfl hterm, Finset.prod_pow_eq_pow_sum, hsum]
  rcases Nat.eq_zero_or_pos (eDeg w) with h | h
  · rw [h]; simp
  · obtain ⟨n, hn⟩ : ∃ n, eDeg w = n + 1 := ⟨eDeg w - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    exact Even.neg_one_pow (by rw [mul_comm]; exact Nat.even_mul_succ_self n)

theorem eT_pow_card : (eT (p := p) K) ^ p = 1 := by
  refine eMod_ext K fun w => ?_
  rw [eT_pow_single, eSgn_prod_card, eRot_iterate_card, one_smul, Module.End.one_apply]

/-! ### `eT` is an algebra map: the shift moves the wedge index by one -/

theorem eT_comp_eWedge (hp : 1 < p) (a : Fin p) :
    (eT K).comp (eWedge K (a + 1)) = (eWedge K a).comp (eT K) := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, eWedge_single, eT_single]
  by_cases hwa : w (a + 1) = true
  · rw [eWedgeGen_of_true K hwa, map_zero, eWedge_smul_single,
      eWedgeGen_of_true K (show eRot w a = true from hwa), smul_zero]
  · have hwa' : w (a + 1) = false := Bool.eq_false_of_not_eq_true hwa
    rw [eWedgeGen_of_false K hwa', eT_smul_single, eRot_update, eWedge_smul_single,
      eWedgeGen_of_false K (show eRot w a = false from hwa'), smul_smul, smul_smul]
    congr 1
    simp only [eSgn, ← pow_add]
    refine eNegOnePow_congr K ?_
    have hdegu : eDeg (Function.update w (a + 1) true) = eDeg w + 1 :=
      eDeg_update_true w (a + 1) hwa'
    have hshift : ePre (eRot w) a + eLetterDeg (w 0)
        = ∑ m ∈ Finset.Iic a, eLetterDeg (w m) :=
      eSum_Iio_shift hp (fun l => eLetterDeg (w l)) a
    have hle : eLetterDeg (w 0) ≤ eDeg w := eLetterDeg_le_eDeg w 0
    by_cases hz : a + 1 = 0
    · have hw0 : w 0 = false := by rw [← hz]; exact hwa'
      have hu0 : Function.update w (a + 1) true 0 = true := by
        rw [← hz, Function.update_self]
      have hIic : (∑ m ∈ Finset.Iic a, eLetterDeg (w m)) = eDeg w := by
        rw [eIic_eq_univ hp a hz]; rfl
      have hpre : ePre w (a + 1) = 0 := by rw [hz]; exact ePre_zero_of_card w
      rw [hw0, hIic, eLetterDeg_false] at hshift
      rw [hu0, hw0, hpre, hdegu, eLetterDeg_true, eLetterDeg_false]
      omega
    · have hu0 : Function.update w (a + 1) true 0 = w 0 :=
        Function.update_of_ne (Ne.symm hz) _ _
      have hIic : (∑ m ∈ Finset.Iic a, eLetterDeg (w m)) = ePre w (a + 1) := by
        rw [eIic_eq_Iio_succ hp a hz]; rfl
      rw [hIic] at hshift
      rw [hu0, hdegu]
      rcases Bool.dichotomy (w 0) with h0 | h0
      · rw [h0, eLetterDeg_false] at hshift hle ⊢
        omega
      · rw [h0, eLetterDeg_true] at hshift hle ⊢
        omega

theorem eT_comp_eD (hp : 1 < p) :
    (eT (p := p) K).comp (eD K) = (eD K).comp (eT (p := p) K) := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, eD_apply, map_sum]
  refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin p))
    (fun b => eWedge K b (eT K (Finsupp.single w (1 : K))))
    (fun a => eT K (eWedge K a (Finsupp.single w (1 : K)))) ?_).symm
  intro b
  have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (Finsupp.single w (1 : K)))
    (eT_comp_eWedge K hp b)
  simp only [LinearMap.comp_apply] at h
  exact h.symm

/-! ## 3. The norm -/

/-- **The norm** `N = 1 + T + ⋯ + T^{p−1}`, the `grNorm` of `OddPGroupRing.lean` acting on
`E^{⊗p}`. -/
noncomputable def eN : EMod K p →ₗ[K] EMod K p := ∑ k ∈ Finset.range p, (eT K) ^ k

/-- **The chain-complex identity of the resolution, on `E^{⊗p}`.**  `N·(T−1) = T^p − 1 = 0`
by the same telescoping `geom_sum_mul` that proves `grNorm_mul_grS`, taken in the
endomorphism ring rather than in the group ring. -/
theorem eN_mul_eT_sub_one :
    (eN (p := p) K) * (eT (p := p) K - 1) = 0 := by
  have h : (eN (p := p) K) * (eT (p := p) K - 1) = ((eT (p := p) K) ^ p - 1) :=
    geom_sum_mul (eT K) p
  rw [h, eT_pow_card]
  exact sub_self (1 : EMod K p →ₗ[K] EMod K p)

/-- **`N` is invariant under the shift, pointwise.**  Everything about `N` is proved
POINTWISE rather than in the endomorphism ring: `rw [mul_sub]` does not fire on
`Module.End`, because the `Sub` in the goal comes from `LinearMap.instSub` and the one in
`mul_sub` from the ring structure, and `rw` matches instances syntactically. -/
theorem eN_eT_apply (x : EMod K p) : eN K (eT K x) = eN K x := by
  have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f x)
    (eN_mul_eT_sub_one K (p := p))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at h
  exact eq_of_sub_eq_zero h

theorem eT_eN_apply (x : EMod K p) : eT K (eN K x) = eN K x := by
  have hcomm : eT K (eN K x) = eN K (eT K x) := by
    -- `rw [eN]` unfolds BOTH occurrences at once; asking for it twice fails
    rw [eN, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
  rw [hcomm, eN_eT_apply]

/-- `T·N = N` in the endomorphism ring. -/
theorem eT_mul_eN : (eT (p := p) K) * (eN (p := p) K) = eN (p := p) K := by
  refine eMod_ext K fun w => ?_
  rw [Module.End.mul_apply, eT_eN_apply]

/-- `N` written as the sum of the POSITIVE powers, which is the form the reflection
argument of `OddPDescentPairing.lean` needs. -/
theorem eN_sum_succ :
    (∑ k ∈ Finset.range p, (eT (p := p) K) ^ (k + 1)) = eN (p := p) K := by
  refine eMod_ext K fun w => ?_
  rw [LinearMap.sum_apply]
  have hterm : ∀ k ∈ Finset.range p,
      ((eT (p := p) K) ^ (k + 1)) (Finsupp.single w (1 : K))
        = eT K (((eT K) ^ k) (Finsupp.single w (1 : K))) := by
    intro k _
    rw [pow_succ', Module.End.mul_apply]
  rw [Finset.sum_congr rfl hterm, ← map_sum, ← LinearMap.sum_apply, ← eN, eT_eN_apply]

/-- Every power of the shift commutes with the differential. -/
theorem eT_pow_eD (hp : 1 < p) (k : ℕ) (x : EMod K p) :
    ((eT K) ^ k) (eD K x) = eD K (((eT K) ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih x]
      have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (((eT K) ^ k) x))
        (eT_comp_eD K hp)
      simp only [LinearMap.comp_apply] at h
      exact h

/-- **`N` commutes with the differential.** -/
theorem eN_comp_eD (hp : 1 < p) :
    (eN (p := p) K).comp (eD K) = (eD K).comp (eN (p := p) K) := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, eN, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => eT_pow_eD K hp k _

end GroupApproximation.CharClass
