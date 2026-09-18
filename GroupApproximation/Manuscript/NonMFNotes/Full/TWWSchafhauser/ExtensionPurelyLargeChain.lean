import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionPurelyLargeWitness

/-!
# Purely large ideals: the chain closure

Lane TWWSch3c3, work order WO-TWWSch-3c-3 (C. Schafhauser, *Subalgebras of simple
AF-algebras*, Ann. of Math. 192 (2020), §3--4; non_mf_group_notes.tex,
thm:fixed-radical-membership).

Take an increasing sequence `D n` of separable closed subalgebras and countable sets
`c n` with `D n ⊆ closure (c n)`, where `D (n+1)` contains the uniform witnesses
attached to `c n`.  Then the closure of the union is purely large over `J`.  Witnesses
for dense approximants transfer to limit points because the witness bounds are uniform.

* `exists_near_of_mem_chainClosure`, `exists_near_jSet_of_mem_chainClosure`;
* `isHRStable_cut_chainClosure`, `isFullIn_cut_chainClosure`;
* `isPurelyLargeIdeal_chainClosure`, `isPurelyLargeIdeal_chainClosure_of_step`.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

variable {B : Type} [CStarAlgebra B]

/-- `‖d k d*‖ ≤ A² K`. -/
theorem norm_conj_le (d k : B) {A K : ℝ} (hd : ‖d‖ ≤ A) (hk : ‖k‖ ≤ K) :
    ‖d * k * star d‖ ≤ A * A * K := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hd
  have hK : 0 ≤ K := (norm_nonneg _).trans hk
  have h1 : ‖d * k‖ ≤ A * K := (norm_mul_le d k).trans (mul_le_mul hd hk (norm_nonneg _) hA)
  calc ‖d * k * star d‖ ≤ ‖d * k‖ * ‖star d‖ := norm_mul_le _ _
    _ ≤ A * K * A := by
      rw [norm_star]
      exact mul_le_mul h1 hd (norm_nonneg _) (mul_nonneg hA hK)
    _ = A * A * K := by ring

/-- Perturbation of a conjugate `d k d*`. -/
theorem norm_conj_sub_le (d d' k k' : B) {A K η : ℝ} (hd : ‖d‖ ≤ A) (hd' : ‖d'‖ ≤ A)
    (hk : ‖k‖ ≤ K) (hk' : ‖k'‖ ≤ K) (h1 : ‖d - d'‖ ≤ η) (h2 : ‖k - k'‖ ≤ η) :
    ‖d * k * star d - d' * k' * star d'‖ ≤ (2 * A * K + A * A) * η := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hd
  have hK : 0 ≤ K := (norm_nonneg _).trans hk
  have hη : 0 ≤ η := (norm_nonneg _).trans h1
  have e1 := norm_mul_sub_mul_le (d * k) (star d) (d' * k') (star d')
  rw [← star_sub, norm_star, norm_star] at e1
  have e3 : ‖d * k - d' * k'‖ ≤ η * K + A * η :=
    (norm_mul_sub_mul_le d k d' k').trans (add_le_add (mul_le_mul h1 hk (norm_nonneg _) hη)
      (mul_le_mul hd' h2 (norm_nonneg _) hA))
  have e4 : ‖d' * k'‖ ≤ A * K :=
    (norm_mul_le _ _).trans (mul_le_mul hd' hk' (norm_nonneg _) hA)
  have e5 : ‖d * k - d' * k'‖ * ‖d‖ ≤ (η * K + A * η) * A :=
    mul_le_mul e3 hd (norm_nonneg _) (add_nonneg (mul_nonneg hη hK) (mul_nonneg hA hη))
  have e6 : ‖d' * k'‖ * ‖d - d'‖ ≤ A * K * η := mul_le_mul e4 h1 (norm_nonneg _) (mul_nonneg hA hK)
  have e7 : (η * K + A * η) * A + A * K * η = (2 * A * K + A * A) * η := by ring
  linarith

/-- `‖p x q − p x' q‖ ≤ ‖p‖ ‖x − x'‖ ‖q‖`. -/
theorem norm_sandwich_sub_le (p x x' q : B) :
    ‖p * x * q - p * x' * q‖ ≤ ‖p‖ * ‖x - x'‖ * ‖q‖ := by
  have h : p * x * q - p * x' * q = p * (x - x') * q := by rw [mul_sub, sub_mul]
  rw [h]
  calc ‖p * (x - x') * q‖ ≤ ‖p * (x - x')‖ * ‖q‖ := norm_mul_le _ _
    _ ≤ ‖p‖ * ‖x - x'‖ * ‖q‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

theorem exists_pos_small (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ C * δ < ε := by
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hC1
  refine ⟨ε / (C + 1), hδ, ?_⟩
  have h1 : (C + 1) * (ε / (C + 1)) = ε := mul_div_cancel₀ ε hC1.ne'
  have h2 : C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hδ
  linarith

variable {J : NonUnitalStarSubalgebra ℂ B} {D : ℕ → StarSubalgebra ℂ B} {c : ℕ → Set B}

/-- Elements of the chain closure are eventually approximated by the sets `c n`. -/
theorem exists_near_of_mem_chainClosure (hD : Monotone D)
    (hc : ∀ n, (D n : Set B) ⊆ closure (c n)) {x : B} (hx : x ∈ chainClosure D) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∃ t ∈ c n, ‖x - t‖ < ε := by
  have hx' : x ∈ closure (⋃ n, (D n : Set B)) := by
    rw [← StarSubalgebra.coe_iSup_of_directed hD.directed_le,
      ← StarSubalgebra.topologicalClosure_coe]
    exact SetLike.mem_coe.mpr hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx' (ε / 2) (half_pos hε)
  obtain ⟨N, hyN⟩ := Set.mem_iUnion.mp hy
  refine ⟨N, fun n hn => ?_⟩
  have hyn : y ∈ closure (c n) := hc n (SetLike.mem_coe.mpr (hD hn (SetLike.mem_coe.mp hyN)))
  obtain ⟨t, ht, hyt⟩ := Metric.mem_closure_iff.mp hyn (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rw [dist_eq_norm] at hxy hyt
  have := norm_sub_le_norm_sub_add_norm_sub x y t
  linarith

/-- Elements of `J` in the chain closure are eventually approximated by `jSet J (c n)`. -/
theorem exists_near_jSet_of_mem_chainClosure (hD : Monotone D)
    (hc : ∀ n, (D n : Set B) ⊆ closure (c n)) {x : B} (hx : x ∈ chainClosure D) (hxJ : x ∈ J)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∃ j ∈ jSet J (c n), j ∈ J ∧ ‖x - j‖ < ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
  obtain ⟨N, hN⟩ := exists_near_of_mem_chainClosure hD hc hx hm0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht, hxt⟩ := hN n hn
  have hex : ∃ j' ∈ J, ‖t - j'‖ < 1 / ((m : ℝ) + 1) :=
    ⟨x, hxJ, by rw [norm_sub_rev]; exact hxt⟩
  refine ⟨jApprox J t m, mem_jSet ht m, jApprox_mem J t m, ?_⟩
  have h1 := jApprox_spec J t m hex
  have h2 := norm_sub_le_norm_sub_add_norm_sub x t (jApprox J t m)
  linarith

/-- **The Hjelmborg--Rørdam condition on the cuts of the chain closure.** -/
theorem isHRStable_cut_chainClosure (W : PurelyLargeWitnessData J) (hD : Monotone D)
    (hc : ∀ n, (D n : Set B) ⊆ closure (c n))
    (hw : ∀ n, witnessSet W (c n) ⊆ (D (n + 1) : Set B)) {e : B} (he : e ∈ chainClosure D)
    (heJ : e ∉ J) : IsHRStable (hereditaryCut e (sepIdeal (chainClosure D) J)) := by
  unfold hereditaryCut
  refine isHRStable_closure fun y hy ε hε => ?_
  obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
  obtain ⟨hjD, hjJ⟩ := mem_sepIdeal.mp (SetLike.mem_coe.mp hj)
  have hs := W.size_pos e heJ
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hs)
  obtain ⟨E, hE⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨a, ha⟩ := exists_nat_ge (‖e‖ + 1)
  obtain ⟨m, hm⟩ := exists_nat_ge (‖j‖ + 1)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max (W.bound a b m E) 0 + m := ⟨_, rfl⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmax := le_max_left (W.bound a b m E) 0
  have hmax0 := le_max_right (W.bound a b m E) 0
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hA0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (a : ℝ) * a * K := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 2 * (a : ℝ) * K + a * a := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; exact mul_nonneg (mul_nonneg hA0 hA0) hK0
  have hLLL : 0 ≤ L * L * L := mul_nonneg (mul_nonneg hL0 hL0) hL0
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hK0) (mul_nonneg hA0 hA0)
  have hC0 : 0 ≤ (4 * L + 4 * (L * L * L)) * G :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hL0) (mul_nonneg (by norm_num) hLLL)) hG0
  obtain ⟨δ₁, hδ₁, hCδ₁⟩ := exists_pos_small _ (ε / 2) hC0 (half_pos hε)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min 1 (W.size e / 2)) δ₁ := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (lt_min one_pos (half_pos hs)) hδ₁
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδs : δ ≤ W.size e / 2 := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := exists_near_of_mem_chainClosure hD hc he hδ
  obtain ⟨N₂, hN₂⟩ := exists_near_jSet_of_mem_chainClosure hD hc hjD hjJ hδ
  obtain ⟨t, ht, het⟩ := hN₁ (max N₁ N₂) (le_max_left _ _)
  obtain ⟨j', hj', hj'J, hjj'⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hea : ‖e‖ ≤ (a : ℝ) := by linarith
  have hta : ‖t‖ ≤ (a : ℝ) := by
    have := norm_le_norm_add_norm_sub' t e
    rw [norm_sub_rev] at this
    linarith
  have hts : 1 / ((b : ℝ) + 1) ≤ W.size t := by
    have := W.size_le e t
    linarith
  have hj'm : ‖j'‖ ≤ (m : ℝ) := by
    have := norm_le_norm_add_norm_sub' j' j
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨hkb, hk1, hk2⟩ := stableWitness_spec W a b m E t j' ⟨hta, hts, hj'm, hj'J⟩
  have hkw := stableWitness_mem_witnessSet W ht hj' a b m E
  have hkD : stableWitness W a b m E t j' ∈ chainClosure D :=
    le_chainClosure D (max N₁ N₂ + 1) (SetLike.mem_coe.mp (hw (max N₁ N₂) hkw))
  have hkJ := stableWitness_mem W a b m E t j'
  obtain ⟨k, hkdef⟩ : ∃ k : B, k = stableWitness W a b m E t j' := ⟨_, rfl⟩
  rw [← hkdef] at hkb hk1 hk2 hkD hkJ
  refine ⟨e * k * star e, subset_closure (mem_conjSet.mpr
    ⟨k, SetLike.mem_coe.mpr (mem_sepIdeal.mpr ⟨hkD, hkJ⟩), rfl⟩), ?_⟩
  have hkK : ‖k‖ ≤ K := by rw [hKdef]; linarith
  have hjK : ‖j‖ ≤ K := by rw [hKdef]; linarith
  have hj'K : ‖j'‖ ≤ K := by rw [hKdef]; linarith
  have hkkδ : ‖k - k‖ ≤ δ := by rw [sub_self, norm_zero]; exact hδ.le
  have hu := norm_conj_le e k hea hkK
  have hu' := norm_conj_le t k hta hkK
  have hv := norm_conj_le e j hea hjK
  have hv' := norm_conj_le t j' hta hj'K
  rw [← hLdef] at hu hu' hv hv'
  have huη := norm_conj_sub_le e t k k hea hta hkK hkK het.le hkkδ
  have hvη := norm_conj_sub_le e t j j' hea hta hjK hj'K het.le hjj'.le
  rw [← hGdef] at huη hvη
  obtain ⟨hp1, hp2⟩ := hr_perturb _ _ _ _ hu hu' hv hv' huη hvη
  have hCδ : (4 * L + 4 * (L * L * L)) * G * δ ≤ (4 * L + 4 * (L * L * L)) * G * δ₁ :=
    mul_le_mul_of_nonneg_left hδδ₁ hC0
  have hsplit : 4 * L * (G * δ) + 4 * (L * L * L) * (G * δ) =
      (4 * L + 4 * (L * L * L)) * G * δ := by ring
  have hn1 : 0 ≤ 4 * L * (G * δ) :=
    mul_nonneg (mul_nonneg (by norm_num) hL0) (mul_nonneg hG0 hδ.le)
  have hn2 : 0 ≤ 4 * (L * L * L) * (G * δ) :=
    mul_nonneg (mul_nonneg (by norm_num) hLLL) (mul_nonneg hG0 hδ.le)
  exact ⟨by linarith, by linarith⟩

/-- **Fullness of the cuts of the chain closure.** -/
theorem isFullIn_cut_chainClosure (W : PurelyLargeWitnessData J) (hD : Monotone D)
    (hc : ∀ n, (D n : Set B) ⊆ closure (c n))
    (hw : ∀ n, witnessSet W (c n) ⊆ (D (n + 1) : Set B)) {e : B} (he : e ∈ chainClosure D)
    (heJ : e ∉ J) :
    IsFullIn (hereditaryCut e (sepIdeal (chainClosure D) J)) (sepIdeal (chainClosure D) J) := by
  unfold IsFullIn hereditaryCut
  intro y hy
  obtain ⟨hyD, hyJ⟩ := mem_sepIdeal.mp (SetLike.mem_coe.mp hy)
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  have hs := W.size_pos e heJ
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hs)
  obtain ⟨E, hE⟩ := exists_nat_one_div_lt hε3
  obtain ⟨a, ha⟩ := exists_nat_ge (‖e‖ + 1)
  obtain ⟨m, hm⟩ := exists_nat_ge (‖y‖ + 1)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max (W.bound a b m E) 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hA0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 2 * (a : ℝ) * K + a * a := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hK0) (mul_nonneg hA0 hA0)
  have hC0 : 0 ≤ K * G * K := mul_nonneg (mul_nonneg hK0 hG0) hK0
  obtain ⟨δ₁, hδ₁, hCδ₁⟩ := exists_pos_small _ (ε / 3) hC0 hε3
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min 1 (W.size e / 2)) (min δ₁ (ε / 3)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min one_pos (half_pos hs)) (lt_min hδ₁ hε3)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδs : δ ≤ W.size e / 2 := by rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 3 := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := exists_near_of_mem_chainClosure hD hc he hδ
  obtain ⟨N₂, hN₂⟩ := exists_near_jSet_of_mem_chainClosure hD hc hyD hyJ hδ
  obtain ⟨t, ht, het⟩ := hN₁ (max N₁ N₂) (le_max_left _ _)
  obtain ⟨y', hy', hy'J, hyy'⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hea : ‖e‖ ≤ (a : ℝ) := by linarith
  have hta : ‖t‖ ≤ (a : ℝ) := by
    have := norm_le_norm_add_norm_sub' t e
    rw [norm_sub_rev] at this
    linarith
  have hts : 1 / ((b : ℝ) + 1) ≤ W.size t := by
    have := W.size_le e t
    linarith
  have hy'm : ‖y'‖ ≤ (m : ℝ) := by
    have := norm_le_norm_add_norm_sub' y' y
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨hpb, hkb, hqb, hfull⟩ := fullWitness_spec W a b m E t y' ⟨hta, hts, hy'm, hy'J⟩
  obtain ⟨hpw, hkw, hqw⟩ := fullWitness_mem_witnessSet W ht hy' a b m E
  obtain ⟨hpJ, hkJ, hqJ⟩ := fullWitness_mem W a b m E t y'
  obtain ⟨w, hwdef⟩ : ∃ w : B × B × B, w = fullWitness W a b m E t y' := ⟨_, rfl⟩
  rw [← hwdef] at hpb hkb hqb hfull hpw hkw hqw hpJ hkJ hqJ
  have hI : ∀ x, x ∈ witnessSet W (c (max N₁ N₂)) → x ∈ J →
      x ∈ (sepIdeal (chainClosure D) J : Set B) := fun x hx hxJ =>
    SetLike.mem_coe.mpr (mem_sepIdeal.mpr
      ⟨le_chainClosure D (max N₁ N₂ + 1) (SetLike.mem_coe.mp (hw (max N₁ N₂) hx)), hxJ⟩)
  refine ⟨w.1 * (e * w.2.1 * star e) * w.2.2, Submodule.subset_span
    ⟨w.1, hI _ hpw hpJ, e * w.2.1 * star e,
      subset_closure (mem_conjSet.mpr ⟨w.2.1, hI _ hkw hkJ, rfl⟩), w.2.2, hI _ hqw hqJ, rfl⟩,
    ?_⟩
  rw [dist_eq_norm]
  have hpK : ‖w.1‖ ≤ K := by rw [hKdef]; exact hpb.trans (le_max_left _ _)
  have hkK : ‖w.2.1‖ ≤ K := by rw [hKdef]; exact hkb.trans (le_max_left _ _)
  have hqK : ‖w.2.2‖ ≤ K := by rw [hKdef]; exact hqb.trans (le_max_left _ _)
  have hte : ‖t - e‖ ≤ δ := by rw [norm_sub_rev]; exact het.le
  have hkkδ : ‖w.2.1 - w.2.1‖ ≤ δ := by rw [sub_self, norm_zero]; exact hδ.le
  have hconj := norm_conj_sub_le t e w.2.1 w.2.1 hta hea hkK hkK hte hkkδ
  rw [← hGdef] at hconj
  have hsand := norm_sandwich_sub_le w.1 (t * w.2.1 * star t) (e * w.2.1 * star e) w.2.2
  have hGδ0 : 0 ≤ G * δ := mul_nonneg hG0 hδ.le
  have hprod : ‖w.1‖ * ‖t * w.2.1 * star t - e * w.2.1 * star e‖ * ‖w.2.2‖ ≤
      K * (G * δ) * K :=
    mul_le_mul (mul_le_mul hpK hconj (norm_nonneg _) hK0) hqK (norm_nonneg _)
      (mul_nonneg hK0 hGδ0)
  have hCδ : K * G * K * δ ≤ K * G * K * δ₁ := mul_le_mul_of_nonneg_left hδδ₁ hC0
  have hre : K * (G * δ) * K = K * G * K * δ := by ring
  have htri1 := norm_sub_le_norm_sub_add_norm_sub y y' (w.1 * (t * w.2.1 * star t) * w.2.2)
  have htri2 := norm_sub_le_norm_sub_add_norm_sub y (w.1 * (t * w.2.1 * star t) * w.2.2)
    (w.1 * (e * w.2.1 * star e) * w.2.2)
  linarith

/-- **The chain closure is purely large.** -/
theorem isPurelyLargeIdeal_chainClosure (W : PurelyLargeWitnessData J) (hD : Monotone D)
    (hsep : ∀ n, IsSepClosed (D n)) (hJR : ∀ b x : B, x ∈ J → x * b ∈ J)
    (hc : ∀ n, (D n : Set B) ⊆ closure (c n))
    (hw : ∀ n, witnessSet W (c n) ⊆ (D (n + 1) : Set B)) :
    IsPurelyLargeIdeal (chainClosure D) J :=
  isPurelyLargeIdeal_of_cut (isSepClosed_chainClosure hD hsep) hJR fun _ he heJ =>
    ⟨isHRStable_cut_chainClosure W hD hc hw he heJ, isFullIn_cut_chainClosure W hD hc hw he heJ⟩

/-- **The chain closure of a `purelyLargeStep` chain is purely large.** -/
theorem isPurelyLargeIdeal_chainClosure_of_step (W : PurelyLargeWitnessData J)
    (hD : Monotone D) (hsep : ∀ n, IsSepClosed (D n)) (hJR : ∀ b x : B, x ∈ J → x * b ∈ J)
    (hstep : ∀ n, purelyLargeStep W (D n) (D (n + 1))) :
    IsPurelyLargeIdeal (chainClosure D) J := by
  have h : ∀ n, ∃ c' : Set B, (D n : Set B) ⊆ closure c' ∧
      witnessSet W c' ⊆ (D (n + 1) : Set B) := hstep
  choose c' hc' hw' using h
  exact isPurelyLargeIdeal_chainClosure W hD hsep hJR hc' hw'

end

end GroupApproximation.Full.TWWSchafhauser
