import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCornerShift.CornerMap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Central
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Products

/-!
# Corner endomorphisms act trivially on stable `K₂` (lane LVCornerShift)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; ABC 2009, proof of
`thm:skewyao`, Step 3.  Let `S` be a ring, `u v : S` with `v * u = 1`, and `f : S →ₙ+* S` the
non-unital endomorphism `a ↦ u * a * v`.  For `k ∈ K₂(n, S)` the elements `f_* k` and `k` agree
after padding to rank `n + 2`.

The proof shifts the corner one index at a time.  `cornerMap (cornerCoeff ℓ u) (cornerCoeff ℓ v)`
multiplies the rows and columns with index `< ℓ` by `u` and `v`.  Stabilized once, the step from
`ℓ` to `ℓ + 1` is conjugation by the corner element `cornerConj` on the indices `ℓ`, `last n`.
Stabilized twice, `K₂` is central (`LVCentral.castSuccStab_castSuccStab_mem_center`), so that
conjugation does nothing.  At `ℓ = n` the corner map is `f_*`, and at `ℓ = 0` it is the identity.
-/

namespace GroupApproximation.Full.LVCornerShift

open SteinbergGroup

section Coefficients

variable {S : Type*} [Ring S]

/-- The diagonal coefficient equal to `c` on the indices `< ℓ` and to `1` on the others.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cornerCoeff {n : ℕ} (ℓ : ℕ) (c : S) (j : Fin n) : S :=
  if j.val < ℓ then c else 1

/-- `cornerCoeff` on an index below the threshold.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem cornerCoeff_of_lt {n ℓ : ℕ} {c : S} {j : Fin n} (h : j.val < ℓ) :
    cornerCoeff ℓ c j = c :=
  if_pos h

/-- `cornerCoeff` on an index at or above the threshold.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem cornerCoeff_of_not_lt {n ℓ : ℕ} {c : S} {j : Fin n} (h : ¬ j.val < ℓ) :
    cornerCoeff ℓ c j = 1 :=
  if_neg h

/-- The diagonal coefficients of `v` and `u` are inverse to each other on the left.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerCoeff_mul {n : ℕ} {u v : S} (hvu : v * u = 1) (ℓ : ℕ) (j : Fin n) :
    cornerCoeff ℓ v j * cornerCoeff ℓ u j = 1 := by
  by_cases h : j.val < ℓ
  · rw [cornerCoeff_of_lt h, cornerCoeff_of_lt h, hvu]
  · rw [cornerCoeff_of_not_lt h, cornerCoeff_of_not_lt h, one_mul]

/-- Raising the threshold from `ℓ` to `ℓ + 1` changes only the index `ℓ`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerCoeff_succ_of_ne {n ℓ : ℕ} (c : S) (j : Fin n) (hj : j.val ≠ ℓ) :
    cornerCoeff (ℓ + 1) c j = cornerCoeff ℓ c j := by
  by_cases h : j.val < ℓ
  · have h' : j.val < ℓ + 1 := by omega
    rw [cornerCoeff_of_lt h', cornerCoeff_of_lt h]
  · have h' : ¬ j.val < ℓ + 1 := by omega
    rw [cornerCoeff_of_not_lt h', cornerCoeff_of_not_lt h]

/-- **Corner shift induction** (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii;
ABC 2009, proof of `thm:skewyao`, Step 3).  After two stabilizations, the corner map with
threshold `ℓ ≤ n` fixes every `k ∈ K₂(n, S)`. -/
theorem stab_stab_cornerMap_eq {n : ℕ} {u v : S} (hvu : v * u = 1) (ℓ : ℕ) (hℓ : ℓ ≤ n)
    (k : SteinbergGroup (Fin n) S) (hk : projection k = 1) :
    LVCentral.castSuccStab (n + 1) S (LVCentral.castSuccStab n S
        (cornerMap (cornerCoeff ℓ u) (cornerCoeff ℓ v) (cornerCoeff_mul hvu ℓ) k)) =
      LVCentral.castSuccStab (n + 1) S (LVCentral.castSuccStab n S k) := by
  induction ℓ with
  | zero =>
      rw [cornerMap_eq_self (cornerCoeff 0 u) (cornerCoeff 0 v) (cornerCoeff_mul hvu 0)
        (fun j => cornerCoeff_of_not_lt (Nat.not_lt_zero j.val))
        (fun j => cornerCoeff_of_not_lt (Nat.not_lt_zero j.val)) k]
  | succ ℓ ih =>
      have hℓn : ℓ < n := hℓ
      have hσm : cornerCoeff (ℓ + 1) u (⟨ℓ, hℓn⟩ : Fin n) =
          u * cornerCoeff ℓ u (⟨ℓ, hℓn⟩ : Fin n) := by
        rw [cornerCoeff_of_lt (j := (⟨ℓ, hℓn⟩ : Fin n)) (Nat.lt_add_one ℓ),
          cornerCoeff_of_not_lt (j := (⟨ℓ, hℓn⟩ : Fin n)) (Nat.lt_irrefl ℓ), mul_one]
      have hτm : cornerCoeff (ℓ + 1) v (⟨ℓ, hℓn⟩ : Fin n) =
          cornerCoeff ℓ v (⟨ℓ, hℓn⟩ : Fin n) * v := by
        rw [cornerCoeff_of_lt (j := (⟨ℓ, hℓn⟩ : Fin n)) (Nat.lt_add_one ℓ),
          cornerCoeff_of_not_lt (j := (⟨ℓ, hℓn⟩ : Fin n)) (Nat.lt_irrefl ℓ), one_mul]
      have step := cornerConj_castSuccStab_cornerMap hvu (⟨ℓ, hℓn⟩ : Fin n)
        (cornerCoeff ℓ u) (cornerCoeff ℓ v) (cornerCoeff (ℓ + 1) u) (cornerCoeff (ℓ + 1) v)
        (cornerCoeff_mul hvu ℓ) (cornerCoeff_mul hvu (ℓ + 1)) hσm hτm
        (fun j hj => cornerCoeff_succ_of_ne u j (fun e => hj (Fin.ext e)))
        (fun j hj => cornerCoeff_succ_of_ne v j (fun e => hj (Fin.ext e))) k
      have hc := LVCentral.castSuccStab_castSuccStab_mem_center (MonoidHom.mem_ker.mpr hk)
      rw [← step, map_mul, map_mul, map_inv, ih hℓn.le,
        Subgroup.mem_center_iff.mp hc, mul_inv_cancel_right]

/-- The non-unital endomorphism `a ↦ u * a * v` induces the corner map with constant diagonals.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem nonUnitalMap_eq_cornerMap {n : ℕ} {u v : S} (f : S →ₙ+* S)
    (hf : ∀ a, f a = u * a * v) (σ τ : Fin n → S) (hστ : ∀ i, τ i * σ i = 1)
    (hσ : ∀ i, σ i = u) (hτ : ∀ i, τ i = v) (g : SteinbergGroup (Fin n) S) :
    LVCohnK2.nonUnitalMap f g = cornerMap σ τ hστ g := by
  have hh : LVCohnK2.nonUnitalMap (I := Fin n) f = cornerMap σ τ hστ := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change LVCohnK2.nonUnitalMap f (x i j hij a) = cornerMap σ τ hστ (x i j hij a)
    rw [LVCohnK2.nonUnitalMap_x, cornerMap_x, hf, hσ, hτ]
  exact DFunLike.congr_fun hh g

/-- Padding by two indices is two stabilizations.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem indexMap_castLEEmb_eq_stab {n : ℕ} (h : n ≤ n + 1 + 1) (g : SteinbergGroup (Fin n) S) :
    indexMap (Fin.castLEEmb h) g =
      LVCentral.castSuccStab (n + 1) S (LVCentral.castSuccStab n S g) := by
  have hh : indexMap (R := S) (Fin.castLEEmb h) =
      (LVCentral.castSuccStab (n + 1) S).comp (LVCentral.castSuccStab n S) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap (Fin.castLEEmb h) (x i j hij a) =
      LVCentral.castSuccStab (n + 1) S (LVCentral.castSuccStab n S (x i j hij a))
    rw [indexMap_x (Fin.castLEEmb h), LVCentral.castSuccStab_x, LVCentral.castSuccStab_x]
    refine x_eq_of_eq _ _ ?_ ?_ a
    · exact Fin.ext rfl
    · exact Fin.ext rfl
  exact DFunLike.congr_fun hh g

end Coefficients

/-- **Stable `K₂` is invariant under corner endomorphisms** (`simple_kazhdan_sofic_group.tex`
l.733-735, `sec:questions`, leaf T1b.iii; ABC 2009, proof of `thm:skewyao`, Step 3).  If
`v * u = 1` and `f a = u * a * v`, then `f_* k` and `k` agree after padding, for every
`k ∈ K₂(n, S)`. -/
theorem stableK2_corner_eq {S : Type*} [Ring S] (u v : S) (hvu : v * u = 1)
    (f : S →ₙ+* S) (hf : ∀ a, f a = u * a * v) (n : ℕ)
    (k : SteinbergGroup (Fin n) S) (hk : SteinbergGroup.projection k = 1) :
    ∃ (N : ℕ) (h : n ≤ N), SteinbergGroup.indexMap (Fin.castLEEmb h)
      (LVCohnK2.nonUnitalMap f k) = SteinbergGroup.indexMap (Fin.castLEEmb h) k := by
  refine ⟨n + 1 + 1, by omega, ?_⟩
  rw [indexMap_castLEEmb_eq_stab, indexMap_castLEEmb_eq_stab,
    nonUnitalMap_eq_cornerMap f hf (cornerCoeff n u) (cornerCoeff n v) (cornerCoeff_mul hvu n)
      (fun i => cornerCoeff_of_lt i.isLt) (fun i => cornerCoeff_of_lt i.isLt)]
  exact stab_stab_cornerMap_eq hvu n le_rfl k hk

end GroupApproximation.Full.LVCornerShift
