import GroupApproximation.Kourovka1759.Main
import GroupApproximation.KohlFactorization.Statement

/-!
# Kohl's factorization conjecture

S. Kohl conjectured (RCWA package manual, chapter 2) that every residue-class-wise affine
permutation of `ℤ` is a product of class shifts, class reflections and class transpositions.
We prove it, and the converse.

* **Residue-class-wise affine permutations form a group.** A permutation is residue-class-wise
  affine exactly when, for some modulus `m ≥ 1`, it is arithmetic on every class:
  `g (r + t m) = g r + t (g (r + m) - g r)` (`Arith`). Being arithmetic is preserved by products
  (modulus `m_h m_g`) and inverses (modulus the product of the steps on the classes mod `m`).
  Class shifts, class reflections and class transpositions are residue-class-wise affine.
* **Factorization.** Let `g` be arithmetic modulo `L` with steps `d_j`.
  - `ρ` reflects every class `j + Lℤ` with `d_j < 0`, so `g ρ` is increasing on every class,
    with step `e_j = |d_j|`.
  - The image of the class `j` is the box `E_j = (g j mod e_j) + e_j ℤ`, reached with offset
    `c_j = g j / e_j`. These boxes are pairwise disjoint.
  - `κ` shifts every box `E_j` back by `c_j`. Then `κ g ρ` maps every class mod `L` canonically
    onto a box, so it is piecewise canonical and lies in `CT(ℤ)` by Kourovka 17.59.
  - So `g = κ⁻¹ (κ g ρ) ρ⁻¹` is a product of class shifts, class transpositions and class
    reflections.
-/

namespace GroupApproximation.KohlFactorization

open Equiv GroupApproximation.Kourovka1759 GroupApproximation.Kourovka1759.Box

/-! ### Residue-class-wise affine permutations form a group -/

/-- `g` is arithmetic modulo `m`: on every class `r + mℤ` it is `r + t m ↦ g r + t d`. -/
def Arith (g : Perm ℤ) (m : ℤ) : Prop :=
  0 < m ∧ ∀ r t : ℤ, g (r + t * m) = g r + t * (g (r + m) - g r)

theorem arith_of_rcwa {g : Perm ℤ} (hg : IsResidueClassWiseAffine g) : ∃ m, Arith g m := by
  obtain ⟨m, hm, haff⟩ := hg
  refine ⟨m, hm, fun r t => ?_⟩
  obtain ⟨a, b, c, hc, hab⟩ := haff r
  have h0 := hab 0
  have h1 := hab 1
  have ht := hab t
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  apply mul_left_cancel₀ hc
  linear_combination ht - h0 - t * (h1 - h0)

theorem rcwa_of_arith {g : Perm ℤ} {m : ℤ} (hg : Arith g m) : IsResidueClassWiseAffine g := by
  obtain ⟨hm, h⟩ := hg
  refine ⟨m, hm, fun r =>
    ⟨g (r + m) - g r, m * g r - (g (r + m) - g r) * r, m, hm.ne', fun t => ?_⟩⟩
  rw [h r t]
  ring

theorem arith_one : Arith 1 1 :=
  ⟨one_pos, fun r t => by simp only [Perm.one_apply]; ring⟩

theorem arith_mul {g h : Perm ℤ} {mg mh : ℤ} (hg : Arith g mg) (hh : Arith h mh) :
    Arith (g * h) (mh * mg) := by
  obtain ⟨hmg, hg⟩ := hg
  obtain ⟨hmh, hh⟩ := hh
  refine ⟨mul_pos hmh hmg, fun r t => ?_⟩
  simp only [Perm.mul_apply]
  have e1 : r + t * (mh * mg) = r + t * mg * mh := by ring
  have e2 : r + mh * mg = r + mg * mh := by ring
  rw [e1, e2, hh r (t * mg), hh r mg]
  have e3 : h r + t * mg * (h (r + mh) - h r) = h r + t * (h (r + mh) - h r) * mg := by ring
  have e4 : h r + mg * (h (r + mh) - h r) = h r + (h (r + mh) - h r) * mg := by ring
  rw [e3, e4, hg (h r) (t * (h (r + mh) - h r)), hg (h r) (h (r + mh) - h r)]
  ring

/-- The step of `g` on the class of `x` modulo `m`. -/
def arithStep (g : Perm ℤ) (m x : ℤ) : ℤ := g (x + m) - g x

theorem arith_inv {g : Perm ℤ} {m : ℤ} (hg : Arith g m) : ∃ M, Arith g⁻¹ M := by
  obtain ⟨hm, hg⟩ := hg
  have hper : ∀ x k : ℤ, arithStep g m (x + k * m) = arithStep g m x := by
    intro x k
    simp only [arithStep]
    have e : x + k * m + m = x + (k + 1) * m := by ring
    rw [e, hg x (k + 1), hg x k]
    ring
  have hne : ∀ x, arithStep g m x ≠ 0 := by
    intro x h0
    simp only [arithStep, sub_eq_zero] at h0
    have := g.injective h0
    linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = ∏ j ∈ Finset.range m.toNat, |arithStep g m (j : ℤ)| :=
    ⟨_, rfl⟩
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Finset.prod_pos fun j _ => abs_pos.2 (hne _)
  have hdvd : ∀ x, arithStep g m x ∣ M := by
    intro x
    have hx : x = x % m + x / m * m := (Int.emod_add_ediv_mul x m).symm
    have hr : arithStep g m x = arithStep g m (x % m) := by
      rw [← hper (x % m) (x / m), ← hx]
    have h0 : 0 ≤ x % m := Int.emod_nonneg x hm.ne'
    have h1 : x % m < m := Int.emod_lt_of_pos x hm
    have hmem : (x % m).toNat ∈ Finset.range m.toNat := Finset.mem_range.2 (by omega)
    have hd : |arithStep g m (((x % m).toNat : ℕ) : ℤ)| ∣ M := by
      rw [hMdef]
      exact Finset.dvd_prod_of_mem (fun j : ℕ => |arithStep g m (j : ℤ)|) hmem
    rw [Int.toNat_of_nonneg h0] at hd
    rw [hr]
    exact (abs_dvd _ _).1 hd
  refine ⟨M, hMpos, fun y t => ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x, y = g x := ⟨g⁻¹ y, (Equiv.apply_symm_apply g y).symm⟩
  obtain ⟨q, hq⟩ := hdvd x
  have key : ∀ s : ℤ, g (x + s * q * m) = g x + s * M := by
    intro s
    rw [hg x (s * q), hq]
    simp only [arithStep]
    ring
  have e1 : g⁻¹ (g x + t * M) = x + t * q * m := by
    rw [← key t]
    exact g.symm_apply_apply _
  have k1 := key 1
  rw [one_mul, one_mul] at k1
  have e2 : g⁻¹ (g x + M) = x + q * m := by
    rw [← k1]
    exact g.symm_apply_apply _
  rw [e1, e2]
  simp only [Perm.coe_inv, Equiv.symm_apply_apply]
  ring

/-- The residue-class-wise affine permutations of `ℤ`, as a subgroup. -/
def rcwaGroup : Subgroup (Perm ℤ) where
  carrier := {g | IsResidueClassWiseAffine g}
  mul_mem' := by
    intro g h hg hh
    obtain ⟨_, hg⟩ := arith_of_rcwa hg
    obtain ⟨_, hh⟩ := arith_of_rcwa hh
    exact rcwa_of_arith (arith_mul hg hh)
  one_mem' := rcwa_of_arith arith_one
  inv_mem' := by
    intro g hg
    obtain ⟨_, hm⟩ := arith_of_rcwa hg
    obtain ⟨_, hM⟩ := arith_inv hm
    exact rcwa_of_arith hM

theorem rcwa_of_isClassShift {g : Perm ℤ} (hg : IsClassShift g) :
    IsResidueClassWiseAffine g := by
  obtain ⟨r, m, hr, hrm, hin, hout⟩ := hg
  have hm : 0 < m := lt_of_le_of_lt hr hrm
  refine rcwa_of_arith ⟨hm, fun x t => ?_⟩
  by_cases hx : ∃ k : ℤ, x = r + k * m
  · obtain ⟨k, rfl⟩ := hx
    have e1 : r + k * m + t * m = r + (k + t) * m := by ring
    have e2 : r + k * m + m = r + (k + 1) * m := by ring
    rw [e1, e2, hin (k + t), hin (k + 1), hin k]
    ring
  · have hfix : ∀ s : ℤ, g (x + s * m) = x + s * m := by
      intro s
      apply hout
      intro t' ht'
      exact hx ⟨t' - s, by linear_combination ht'⟩
    have e3 : g x = x := by simpa using hfix 0
    have e2 : x + m = x + 1 * m := by ring
    rw [hfix t, e2, hfix 1, e3]
    ring

theorem rcwa_of_isClassReflection {g : Perm ℤ} (hg : IsClassReflection g) :
    IsResidueClassWiseAffine g := by
  obtain ⟨r, m, hr, hrm, hin, hout⟩ := hg
  have hm : 0 < m := lt_of_le_of_lt hr hrm
  refine rcwa_of_arith ⟨hm, fun x t => ?_⟩
  by_cases hx : ∃ k : ℤ, x = r + k * m
  · obtain ⟨k, rfl⟩ := hx
    have e1 : r + k * m + t * m = r + (k + t) * m := by ring
    have e2 : r + k * m + m = r + (k + 1) * m := by ring
    rw [e1, e2, hin (k + t), hin (k + 1), hin k]
    ring
  · have hfix : ∀ s : ℤ, g (x + s * m) = x + s * m := by
      intro s
      apply hout
      intro t' ht'
      exact hx ⟨t' - s, by linear_combination ht'⟩
    have e3 : g x = x := by simpa using hfix 0
    have e2 : x + m = x + 1 * m := by ring
    rw [hfix t, e2, hfix 1, e3]
    ring

theorem rcwa_of_isClassTransposition {g : Perm ℤ} (hg : IsClassTransposition g) :
    IsResidueClassWiseAffine g := by
  obtain ⟨A, B, h, rfl⟩ := IsClassTransposition.eq_swap hg
  exact (isPC_swap h).rcwa

/-! ### The group generated by class shifts, class reflections and class transpositions -/

/-- Class shifts, class reflections and class transpositions. -/
def cscrct : Set (Perm ℤ) :=
  {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g}

theorem mem_cscrct {g : Perm ℤ} :
    g ∈ cscrct ↔ IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g :=
  Iff.rfl

/-- The group they generate. -/
def cscrctGroup : Subgroup (Perm ℤ) := Subgroup.closure cscrct

theorem cscrctGroup_le_rcwaGroup : cscrctGroup ≤ rcwaGroup := by
  rw [cscrctGroup, Subgroup.closure_le]
  intro g hg
  rcases mem_cscrct.1 hg with hg | hg | hg
  · exact rcwa_of_isClassShift hg
  · exact rcwa_of_isClassReflection hg
  · exact rcwa_of_isClassTransposition hg

theorem ct_le_cscrctGroup : classTranspositionGroup ≤ cscrctGroup := by
  rw [classTranspositionGroup, cscrctGroup]
  exact Subgroup.closure_mono fun g hg => mem_cscrct.2 (Or.inr (Or.inr hg))

theorem transHom_elt (N : Box) (g : Perm ℤ) (t : ℤ) :
    transHom N g (N.r + t * N.m) = N.r + g t * N.m := by
  rw [transHom_apply, transFun_pos N g (N.elt_mem t), N.elt_div]

theorem transHom_mem_self (N : Box) (g : Perm ℤ) {n : ℤ} (hn : N.Mem n) :
    N.Mem (transHom N g n) := by
  rw [transHom_apply, transFun_pos N g hn]
  exact N.elt_mem _

/-- Transporting the translation `n ↦ n + 1` into a box gives its class shift. -/
theorem transHom_addRight_one_isClassShift (N : Box) :
    IsClassShift (transHom N (Equiv.addRight 1)) := by
  refine ⟨N.r, N.m, N.hr, N.hrm, fun t => ?_, fun n hn => ?_⟩
  · rw [transHom_elt]
    simp only [Equiv.coe_addRight]
    ring
  · apply transHom_fix
    intro hmem
    obtain ⟨t, ht⟩ := (N.mem_iff n).1 hmem
    exact hn t ht

/-- Transporting the negation `n ↦ -n` into a box gives its class reflection. -/
theorem transHom_neg_isClassReflection (N : Box) :
    IsClassReflection (transHom N (Equiv.neg ℤ)) := by
  refine ⟨N.r, N.m, N.hr, N.hrm, fun t => ?_, fun n hn => ?_⟩
  · rw [transHom_elt]
    simp only [Equiv.neg_apply]
    ring
  · apply transHom_fix
    intro hmem
    obtain ⟨t, ht⟩ := (N.mem_iff n).1 hmem
    exact hn t ht

theorem addRight_one_zpow (k : ℤ) : (Equiv.addRight (1 : ℤ)) ^ k = Equiv.addRight k := by
  induction k with
  | zero => ext n; simp
  | succ i ih =>
    rw [zpow_add_one, ih]
    ext n
    simp only [Perm.mul_apply, Equiv.coe_addRight]
    ring
  | pred i ih =>
    rw [zpow_sub_one, ih, mul_inv_eq_iff_eq_mul]
    ext n
    simp only [Perm.mul_apply, Equiv.coe_addRight]
    ring

theorem transHom_addRight_mem (N : Box) (k : ℤ) : transHom N (Equiv.addRight k) ∈ cscrctGroup := by
  rw [← addRight_one_zpow, map_zpow]
  exact zpow_mem (Subgroup.subset_closure
    (mem_cscrct.2 (Or.inl (transHom_addRight_one_isClassShift N)))) k

theorem transHom_neg_mem (N : Box) : transHom N (Equiv.neg ℤ) ∈ cscrctGroup :=
  Subgroup.subset_closure (mem_cscrct.2 (Or.inr (Or.inl (transHom_neg_isClassReflection N))))

/-! ### Products of transports into disjoint boxes -/

/-- A product of transports into pairwise disjoint boxes fixes every point outside the boxes,
and acts on each box by its own factor. -/
theorem prod_transHom_apply :
    ∀ (l : List (Box × Perm ℤ)), l.Pairwise (fun p q => p.1.Disj q.1) → ∀ n : ℤ,
      ((∀ p ∈ l, ¬ p.1.Mem n) → (l.map fun p => transHom p.1 p.2).prod n = n) ∧
      (∀ p ∈ l, p.1.Mem n → (l.map fun p => transHom p.1 p.2).prod n = transHom p.1 p.2 n)
  | [], _, _ => ⟨fun _ => by simp, fun _ hp => by simp at hp⟩
  | a :: l, hl, n => by
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl⟩ := hl
    have ih := prod_transHom_apply l hl n
    refine ⟨fun hn => ?_, fun p hp hpn => ?_⟩
    · rw [List.map_cons, List.prod_cons, Perm.mul_apply,
        ih.1 (fun p hp => hn p (List.mem_cons.2 (Or.inr hp)))]
      exact transHom_fix _ _ (hn a (List.mem_cons.2 (Or.inl rfl)))
    · rw [List.map_cons, List.prod_cons, Perm.mul_apply]
      rcases List.mem_cons.1 hp with rfl | hp'
      · rw [ih.1 (fun q hq hqn => ha q hq n hpn hqn)]
      · rw [ih.2 p hp' hpn]
        apply transHom_fix
        intro hmem
        exact ha p hp' _ hmem (transHom_mem_self p.1 p.2 hpn)

theorem boxProd_apply {L : ℕ} (B : Fin L → Box) (f : Fin L → Perm ℤ)
    (hB : ∀ i k, i ≠ k → (B i).Disj (B k)) (j : Fin L) {n : ℤ} (hn : (B j).Mem n) :
    ((List.finRange L).map fun i => transHom (B i) (f i)).prod n = transHom (B j) (f j) n := by
  have hl : ((List.finRange L).map fun i => (B i, f i)).Pairwise (fun p q => p.1.Disj q.1) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (R := fun a b : Fin L => a ≠ b) (fun {i k} hik => hB i k hik)
      (List.nodup_finRange L)
  have key := (prod_transHom_apply _ hl n).2 (B j, f j)
    (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩) hn
  rw [List.map_map] at key
  exact key

theorem boxProd_mem {L : ℕ} (B : Fin L → Box) (f : Fin L → Perm ℤ)
    (hf : ∀ j, transHom (B j) (f j) ∈ cscrctGroup) :
    ((List.finRange L).map fun i => transHom (B i) (f i)).prod ∈ cscrctGroup := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact hf j

/-! ### The factorization -/

theorem mem_cscrctGroup_of_rcwa {g : Perm ℤ} (hg : IsResidueClassWiseAffine g) :
    g ∈ cscrctGroup := by
  obtain ⟨m, hm, harith⟩ := arith_of_rcwa hg
  obtain ⟨L, rfl⟩ : ∃ L : ℕ, m = L := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  have hL : 0 < L := by exact_mod_cast hm
  -- the step of `g` on the class `j + Lℤ`
  obtain ⟨d, hdd⟩ : ∃ d : Fin L → ℤ, ∀ j, d j = g ((j : ℤ) + L) - g j := ⟨_, fun _ => rfl⟩
  have hkey : ∀ (j : Fin L) (t : ℤ), g ((j : ℤ) + t * L) = g j + t * d j := by
    intro j t
    rw [hdd j]
    exact harith j t
  have hd : ∀ j, d j ≠ 0 := by
    intro j h0
    rw [hdd j, sub_eq_zero] at h0
    have := g.injective h0
    linarith
  -- `ρ` reflects the classes on which `g` decreases
  obtain ⟨f, hf⟩ : ∃ f : Fin L → Perm ℤ, ∀ j, f j = if d j < 0 then Equiv.neg ℤ else 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Perm ℤ,
      ρ = ((List.finRange L).map fun i => transHom (child L i) (f i)).prod := ⟨_, rfl⟩
  have hρ : ∀ (j : Fin L) (t : ℤ), ρ ((j : ℤ) + t * L) = (j : ℤ) + f j t * L := by
    intro j t
    rw [hρdef]
    exact (boxProd_apply (child L) f (fun _ _ h => child_disj L h) j
      ((child L j).elt_mem t)).trans (transHom_elt (child L j) (f j) t)
  have hρmem : ρ ∈ cscrctGroup := by
    rw [hρdef]
    refine boxProd_mem (child L) f fun j => ?_
    rw [hf j]
    split_ifs
    · exact transHom_neg_mem _
    · rw [map_one]
      exact one_mem _
  -- `g ρ` is increasing on every class, with step `e j = |d j|`
  obtain ⟨e, he⟩ : ∃ e : Fin L → ℤ, ∀ j, e j = |d j| := ⟨_, fun _ => rfl⟩
  have hepos : ∀ j, 0 < e j := fun j => by rw [he j]; exact abs_pos.2 (hd j)
  have hstep : ∀ (j : Fin L) (t : ℤ), g (ρ ((j : ℤ) + t * L)) = g j + t * e j := by
    intro j t
    rw [hρ j t, hf j]
    by_cases h : d j < 0
    · rw [if_pos h, Equiv.neg_apply, hkey j (-t), he j, abs_of_neg h]
      ring
    · rw [if_neg h, Perm.one_apply, hkey j t, he j, abs_of_nonneg (not_lt.1 h)]
  -- the image of the class `j` is the box `E j`, reached with offset `c j`
  obtain ⟨E, hEr, hEm⟩ : ∃ E : Fin L → Box, (∀ j, (E j).r = g j % e j) ∧ ∀ j, (E j).m = e j :=
    ⟨fun j => ⟨g j % e j, e j, Int.emod_nonneg _ (hepos j).ne', Int.emod_lt_of_pos _ (hepos j)⟩,
      fun _ => rfl, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin L → ℤ, ∀ j, c j = g j / e j := ⟨_, fun _ => rfl⟩
  have hgj : ∀ j : Fin L, g (j : ℤ) = (E j).r + c j * (E j).m := by
    intro j
    rw [hEr j, hEm j, hc j]
    exact (Int.emod_add_ediv_mul (g j) (e j)).symm
  have hh : ∀ (j : Fin L) (t : ℤ), g (ρ ((j : ℤ) + t * L)) = (E j).r + (t + c j) * (E j).m := by
    intro j t
    rw [hstep j t, hgj j, ← hEm j]
    ring
  have hEdisj : ∀ i k : Fin L, i ≠ k → (E i).Disj (E k) := by
    intro i k hik n hi hk
    obtain ⟨u, hu⟩ := ((E i).mem_iff n).1 hi
    obtain ⟨v, hv⟩ := ((E k).mem_iff n).1 hk
    have h1 : (g * ρ) ((i : ℤ) + (u - c i) * L) = n := by
      rw [Perm.mul_apply, hh i (u - c i), hu]
      ring
    have h2 : (g * ρ) ((k : ℤ) + (v - c k) * L) = n := by
      rw [Perm.mul_apply, hh k (v - c k), hv]
      ring
    have h3 := (g * ρ).injective (h1.trans h2.symm)
    apply hik
    have hi' : ((i : ℤ) + (u - c i) * L) % L = i := by
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)
    have hk' : ((k : ℤ) + (v - c k) * L) % L = k := by
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast k.isLt)
    have hik' : (i : ℤ) = k := by rw [← hi', h3, hk']
    exact Fin.ext (by exact_mod_cast hik')
  -- `κ` shifts every box `E j` back by `c j`
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin L → Perm ℤ, ∀ j, φ j = Equiv.addRight (-(c j)) := ⟨_, fun _ => rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : Perm ℤ,
      κ = ((List.finRange L).map fun i => transHom (E i) (φ i)).prod := ⟨_, rfl⟩
  have hκ : ∀ (j : Fin L) (s : ℤ), κ ((E j).r + s * (E j).m) = (E j).r + (s - c j) * (E j).m := by
    intro j s
    rw [hκdef, boxProd_apply E φ hEdisj j ((E j).elt_mem s), transHom_elt, hφ j]
    simp only [Equiv.coe_addRight]
    ring
  have hκmem : κ ∈ cscrctGroup := by
    rw [hκdef]
    refine boxProd_mem E φ fun j => ?_
    rw [hφ j]
    exact transHom_addRight_mem _ _
  -- `κ g ρ` is piecewise canonical, hence in `CT(ℤ)`
  have hpc : IsPC (κ * (g * ρ)) := by
    refine ⟨L, hL, fun j => ⟨E j, fun t => ?_⟩⟩
    simp only [Perm.mul_apply, child_r, child_m]
    rw [hh j t, hκ j (t + c j)]
    ring
  have hmid : κ * (g * ρ) ∈ cscrctGroup := ct_le_cscrctGroup (mem_ct_of_isPC hpc)
  rw [show g = κ⁻¹ * (κ * (g * ρ)) * ρ⁻¹ by group]
  exact mul_mem (mul_mem (inv_mem hκmem) hmid) (inv_mem hρmem)

/-- **Kohl's factorization conjecture** (RCWA package manual, chapter 2): the
residue-class-wise affine permutations of `ℤ` are exactly the products of class shifts,
class reflections and class transpositions. -/
theorem kohl_factorization_conjecture :
    {g : Equiv.Perm ℤ | IsResidueClassWiseAffine g} =
      (Subgroup.closure {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g} :
        Set (Equiv.Perm ℤ)) := by
  ext g
  constructor
  · intro hg
    exact mem_cscrctGroup_of_rcwa hg
  · intro hg
    exact cscrctGroup_le_rcwaGroup hg

end GroupApproximation.KohlFactorization
