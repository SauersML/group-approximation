import GroupApproximation.Kourovka1759.Swap

/-!
# Piecewise-canonical permutations

`g` is piecewise canonical if for some `L ≥ 1` it maps every class `j + Lℤ` canonically onto a
box. These permutations form a subgroup containing `CT(ℤ)`, and they are exactly the
residue-class-wise affine permutations that preserve the sign of every integer.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

namespace Box

/-- A box `C` whose first point lies in `B` and whose modulus is a multiple of `B.m` is a
sub-box `place B Y`. -/
theorem eq_place {B C : Box} (hmem : B.Mem C.r) (hdiv : B.m ∣ C.m) : ∃ Y, C = place B Y := by
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨⟨C.r / B.m, q, Int.ediv_nonneg C.hr B.m_pos.le, ?_⟩, ?_⟩
  · apply Int.ediv_lt_of_lt_mul B.m_pos
    have := C.hrm; rw [hq] at this; linarith
  · ext
    · simp only [place_r]; exact (eq_of_mem hmem).symm
    · simp only [place_m]; rw [hq]; ring

theorem nonneg_iff (B : Box) (t : ℤ) : 0 ≤ B.r + t * B.m ↔ 0 ≤ t := by
  have h1 := B.hr; have h2 := B.hrm
  constructor
  · intro h; by_contra ht; push Not at ht; nlinarith
  · intro ht; have := mul_nonneg ht B.m_pos.le; linarith

theorem child_r (L : ℕ) (j : Fin L) : (child L j).r = (j : ℤ) := rfl
theorem child_m (L : ℕ) (j : Fin L) : (child L j).m = (L : ℤ) := rfl

/-- The class mod `L` containing `n`, for `L ≥ 1`. -/
def classOf (L : ℕ) (hL : 0 < L) (n : ℤ) : Fin L :=
  ⟨(n % L).toNat, by
    have h1 := Int.emod_nonneg n (show (L : ℤ) ≠ 0 by exact_mod_cast hL.ne')
    have h2 := Int.emod_lt_of_pos n (show (0 : ℤ) < L by exact_mod_cast hL)
    omega⟩

theorem mem_classOf (L : ℕ) (hL : 0 < L) (n : ℤ) : (child L (classOf L hL n)).Mem n := by
  have h1 := Int.emod_nonneg n (show (L : ℤ) ≠ 0 by exact_mod_cast hL.ne')
  unfold Mem; simp only [child_m, child_r, classOf]; omega

/-- For `A.m ∣ L`, each class mod `L` lies in `A` or is disjoint from it. -/
theorem child_sub_or_disj {A : Box} {L : ℕ} (hdiv : A.m ∣ (L : ℤ)) (j : Fin L) :
    (∃ Y, child L j = place A Y) ∨ (child L j).Disj A := by
  by_cases h : A.Mem (child L j).r
  · exact Or.inl (eq_place h hdiv)
  · right
    intro n hn ha
    apply h
    unfold Mem at hn ha ⊢
    rw [← hn, child_m, Int.emod_emod_of_dvd n hdiv]
    exact ha

end Box

/-- `g` is piecewise canonical: canonical on every class of some modulus `L ≥ 1`. -/
def IsPC (g : Perm ℤ) : Prop :=
  ∃ L : ℕ, 0 < L ∧ ∀ j : Fin L, ∃ B : Box, CanonOn g (child L j) B

theorem isPC_one : IsPC 1 := ⟨1, one_pos, fun j => ⟨child 1 j, CanonOn.one _⟩⟩

theorem isPC_mul {g h : Perm ℤ} (hg : IsPC g) (hh : IsPC h) : IsPC (g * h) := by
  obtain ⟨Lg, hLg, Bg⟩ := hg
  obtain ⟨Lh, hLh, Bh⟩ := hh
  refine ⟨Lg * Lh, Nat.mul_pos hLg hLh, fun j => ?_⟩
  let jh : Fin Lh := ⟨j % Lh, Nat.mod_lt _ hLh⟩
  let jg : Fin Lg := ⟨j / Lh, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩
  have hsplit : child (Lg * Lh) j = place (child Lh jh) (child Lg jg) := by
    ext
    · simp only [child_r, place_r, child_m, jh, jg]
      push_cast
      exact_mod_cast (Nat.mod_add_div' (j : ℕ) Lh).symm
    · simp only [child_m, place_m]; push_cast; ring
  obtain ⟨B₁, h₁⟩ := Bh jh
  have h₁' := h₁.place (child Lg jg)
  let c := classOf Lg hLg (place B₁ (child Lg jg)).r
  obtain ⟨Y, hY⟩ := eq_place (mem_classOf Lg hLg (place B₁ (child Lg jg)).r)
    (show (child Lg c).m ∣ (place B₁ (child Lg jg)).m from
      ⟨B₁.m, by simp only [place_m, child_m]⟩)
  obtain ⟨B₂, h₂⟩ := Bg c
  refine ⟨place B₂ Y, ?_⟩
  rw [hsplit]
  rw [hY] at h₁'
  exact h₁'.comp (h₂.place Y)

theorem isPC_inv {g : Perm ℤ} (hg : IsPC g) : IsPC g⁻¹ := by
  obtain ⟨L, hL, hB⟩ := hg
  choose B hB using hB
  let N : ℕ := ∏ j : Fin L, (B j).m.toNat
  have hNpos : 0 < N := Finset.prod_pos fun j _ => by have := (B j).m_pos; omega
  have hdvd : ∀ j, (B j).m ∣ (N : ℤ) := by
    intro j
    have h1 : (B j).m.toNat ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have h2 := Int.natCast_dvd_natCast.2 h1
    rwa [Int.toNat_of_nonneg (B j).m_pos.le] at h2
  refine ⟨N, hNpos, fun i => ?_⟩
  let j := classOf L hL (g⁻¹ (child N i).r)
  have hi : (B j).Mem (child N i).r := by
    have := (hB j).mem (mem_classOf L hL (g⁻¹ (child N i).r))
    simpa only [Perm.coe_inv, Equiv.apply_symm_apply] using this
  obtain ⟨Y, hY⟩ := eq_place hi (by rw [child_m]; exact hdvd j)
  refine ⟨place (child L j) Y, ?_⟩
  rw [hY]
  exact (hB j).inv.place Y

/-- The subgroup of piecewise-canonical permutations. -/
def pcGroup : Subgroup (Perm ℤ) where
  carrier := {g | IsPC g}
  mul_mem' := isPC_mul
  one_mem' := isPC_one
  inv_mem' := isPC_inv

theorem isPC_swap {A B : Box} (h : A.Disj B) : IsPC (swap A B h) := by
  have hAB : 0 < A.m * B.m := mul_pos A.m_pos B.m_pos
  have hL : (((A.m * B.m).toNat : ℕ) : ℤ) = A.m * B.m := Int.toNat_of_nonneg hAB.le
  refine ⟨(A.m * B.m).toNat, by omega, fun j => ?_⟩
  rcases child_sub_or_disj (A := A) (by rw [hL]; exact dvd_mul_right _ _) j with ⟨Y, hY⟩ | hA
  · exact ⟨place B Y, by rw [hY]; exact (swap_canon h).place Y⟩
  rcases child_sub_or_disj (A := B) (by rw [hL]; exact dvd_mul_left _ _) j with ⟨Y, hY⟩ | hB
  · exact ⟨place A Y, by rw [hY]; exact (swap_canon' h).place Y⟩
  · exact ⟨child _ j, swap_canon_of_disj h hA hB⟩

theorem ct_le_pc : classTranspositionGroup ≤ pcGroup := by
  rw [classTranspositionGroup, Subgroup.closure_le]
  intro x hx
  obtain ⟨A, B, h, rfl⟩ := IsClassTransposition.eq_swap hx
  exact isPC_swap h

theorem IsPC.rcwa {g : Perm ℤ} (hg : IsPC g) : IsResidueClassWiseAffine g := by
  obtain ⟨L, hL, hB⟩ := hg
  refine ⟨L, by exact_mod_cast hL, fun r => ?_⟩
  let j := classOf L hL r
  obtain ⟨B, hBj⟩ := hB j
  have hr : (child L j).Mem r := mem_classOf L hL r
  refine ⟨B.m, L * B.r - (j : ℤ) * B.m, L, by exact_mod_cast hL.ne', fun t => ?_⟩
  have hn : (child L j).Mem (r + t * L) := by
    unfold Mem at hr ⊢; rw [child_m] at hr ⊢; rw [Int.add_mul_emod_self_right]; exact hr
  have e2 := (child L j).eq_of_mem hn
  rw [child_r, child_m] at e2
  rw [hBj.apply hn, child_m]
  linear_combination B.m * e2

theorem IsPC.sign {g : Perm ℤ} (hg : IsPC g) (n : ℤ) : 0 ≤ n ↔ 0 ≤ g n := by
  obtain ⟨L, hL, hB⟩ := hg
  let j := classOf L hL n
  obtain ⟨B, hBj⟩ := hB j
  have hn := mem_classOf L hL n
  have e1 := (child L j).eq_of_mem hn
  rw [hBj.apply hn, B.nonneg_iff, ← (child L j).nonneg_iff (n / (child L j).m), e1]

theorem isPC_of_rcwa {g : Perm ℤ} (hg : IsResidueClassWiseAffine g)
    (hs : ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) : IsPC g := by
  obtain ⟨m, hm, haff⟩ := hg
  have hmL : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm.le
  refine ⟨m.toNat, by omega, fun j => ?_⟩
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hjm : ((j : ℕ) : ℤ) < m := by
    have : ((j : ℕ) : ℤ) < ((m.toNat : ℕ) : ℤ) := by exact_mod_cast j.isLt
    linarith
  obtain ⟨a, b, c, hc, hab⟩ := haff (j : ℤ)
  have h0 := hab 0
  have h1 := hab 1
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  obtain ⟨d, hd⟩ : ∃ d, d = g ((j : ℤ) + m) - g (j : ℤ) := ⟨_, rfl⟩
  have hcd : c * d = a * m := by rw [hd]; linear_combination h1 - h0
  have key : ∀ t : ℤ, g ((j : ℤ) + t * m) = g (j : ℤ) + t * d := by
    intro t
    apply mul_left_cancel₀ hc
    linear_combination hab t - h0 - t * hcd
  have hd0 : d ≠ 0 := by
    intro h0'
    have e := key 1
    rw [h0', one_mul, mul_zero, add_zero] at e
    have := g.injective e
    linarith
  have hg0 : 0 ≤ g (j : ℤ) := (hs _).1 hj0
  have hdpos : 0 < d := by
    by_contra hneg
    have hd1 : d ≤ -1 := by omega
    have ht : 0 ≤ (j : ℤ) + ((g (j : ℤ)).natAbs + 1 : ℤ) * m := by
      have : (0 : ℤ) ≤ (g (j : ℤ)).natAbs := by positivity
      nlinarith
    have e := (hs _).1 ht
    rw [key] at e
    have hle : g (j : ℤ) ≤ (g (j : ℤ)).natAbs := Int.le_natAbs
    have : (0 : ℤ) ≤ (g (j : ℤ)).natAbs := by positivity
    nlinarith
  have hgd : g (j : ℤ) < d := by
    have hneg : ¬ (0 ≤ (j : ℤ) + (-1) * m) := by linarith
    rw [hs, key] at hneg
    linarith
  refine ⟨⟨g (j : ℤ), d, hg0, hgd⟩, fun t => ?_⟩
  simp only [child_r, child_m, hmL]
  exact key t

end GroupApproximation.Kourovka1759
