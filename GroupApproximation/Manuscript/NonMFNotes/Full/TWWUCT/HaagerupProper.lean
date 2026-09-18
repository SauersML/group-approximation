import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HaagerupCocycle

/-!
# The Haagerup property of countable amenable groups

Lane TWWUCT (work order WO-TWWCore-2), geometric input to Higson--Kasparov
(Invent. Math. 144 (2001), Thm. 1.1) for the UCT of `C⋆_r(G)` used in
`non_mf_group_notes.tex` (L1376--1378).  We follow Bekka--Chérix--Valette,
*Proper affine isometric actions of amenable groups* (1995).

Given Følner data `(sₖ, Aₙ)` (`FolnerData`), put

  `b(g)(n, x) = √(2ⁿ / |Aₙ|) · (1_{Aₙ}(g⁻¹x) - 1_{Aₙ}(x))`   on `ℓ²(ℕ × G, ℝ)`.

* `FolnerData.memℓp_cocycleFun`: `b(g)` is square-summable.  If `g = sₖ` and
  `n > k`, the `n`-th block has mass at most `2ⁿ / |Aₙ| · 2 · 4⁻ⁿ |Aₙ| = 2 · 2⁻ⁿ`.
* `FolnerData.cocycle_mul`: `b(gh) = b(g) + π_g b(h)`.  So
  `FolnerData.affine g ξ = π_g ξ + b(g)` is an action by affine isometries
  (`affine_one`, `affine_mul`, `dist_affine`).
* `FolnerData.cocycle_proper`: `{g | ‖b(g)‖ ≤ R}` is finite.  Indeed
  `‖b(g)‖² ≥ 2ⁿ` whenever `g⁻¹Aₙ ∩ Aₙ = ∅`, which holds off the finite set
  `Aₙ Aₙ⁻¹`.
* `exists_proper_cocycle`: the Haagerup property of a countable amenable group.
-/

namespace GroupApproximation.Full.TWWUCT

open scoped ENNReal

noncomputable section

universe u

namespace FolnerData

variable {G : Type u} [Group G] (D : FolnerData G)

theorem card_pos (n : ℕ) : (0 : ℝ) < (D.sets n).card := by
  exact_mod_cast (D.nonempty n).card_pos

/-- The weight `√(2ⁿ / |Aₙ|)` of the `n`-th block. -/
def weight (n : ℕ) : ℝ :=
  Real.sqrt (2 ^ n / (D.sets n).card)

theorem weight_sq (n : ℕ) : D.weight n ^ 2 = 2 ^ n / (D.sets n).card :=
  Real.sq_sqrt (div_nonneg (by positivity) (D.card_pos n).le)

/-- The mass bound for the `n`-th block of `b(g)`. -/
theorem weight_sq_mul_boundary_le {g : G} {k n : ℕ} (hk : D.seq k = g) (hkn : k < n) :
    D.weight n ^ 2 * (((AmenableActionSofic.boundary (D.sets n) g).card : ℝ) +
        (AmenableActionSofic.boundary (D.sets n) g⁻¹).card) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  obtain ⟨h₁, h₂⟩ := D.small n k hkn
  rw [hk] at h₁ h₂
  have hc := D.card_pos n
  have hpow : (2 : ℝ) ^ n * (1 / 4) ^ n = (1 / 2) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [D.weight_sq]
  calc (2 : ℝ) ^ n / (D.sets n).card *
        (((AmenableActionSofic.boundary (D.sets n) g).card : ℝ) +
          (AmenableActionSofic.boundary (D.sets n) g⁻¹).card)
      ≤ (2 : ℝ) ^ n / (D.sets n).card *
          ((1 / 4 : ℝ) ^ n * (D.sets n).card + (1 / 4 : ℝ) ^ n * (D.sets n).card) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁.le h₂.le) (by positivity)
    _ = 2 * ((2 : ℝ) ^ n * (1 / 4) ^ n) * (((D.sets n).card : ℝ) / (D.sets n).card) := by
        ring
    _ = 2 * (1 / 2 : ℝ) ^ n := by
        rw [hpow, div_self hc.ne', mul_one]

theorem summable_weight_sq_mul_boundary (g : G) :
    Summable fun n : ℕ ↦ D.weight n ^ 2 *
      (((AmenableActionSofic.boundary (D.sets n) g).card : ℝ) +
        (AmenableActionSofic.boundary (D.sets n) g⁻¹).card) := by
  obtain ⟨k, hk⟩ := D.seq_surj g
  refine (summable_nat_add_iff (k + 1)).mp ?_
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => D.weight_sq_mul_boundary_le hk (by omega))
    ((summable_nat_add_iff (k + 1)).mpr (summable_geometric_two.mul_left 2))

/-- The coordinates of the Haagerup cocycle `b(g)`. -/
def cocycleFun (g : G) (i : ℕ × G) : ℝ :=
  D.weight i.1 * jump (D.sets i.1) g i.2

theorem memℓp_cocycleFun (g : G) : Memℓp (D.cocycleFun g) 2 := by
  refine memℓp_gen' (C := ∑' n : ℕ, D.weight n ^ 2 *
    (((AmenableActionSofic.boundary (D.sets n) g).card : ℝ) +
      (AmenableActionSofic.boundary (D.sets n) g⁻¹).card)) ?_
  intro s
  classical
  simp only [norm_rpow_two_toReal, cocycleFun]
  calc ∑ i ∈ s, (D.weight i.1 * jump (D.sets i.1) g i.2) ^ 2
      ≤ ∑ i ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
          (D.weight i.1 * jump (D.sets i.1) g i.2) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
        intro i hi
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩
    _ = ∑ n ∈ s.image Prod.fst,
          D.weight n ^ 2 * ∑ x ∈ s.image Prod.snd, jump (D.sets n) g x ^ 2 := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact mul_pow _ _ _
    _ ≤ ∑ n ∈ s.image Prod.fst, D.weight n ^ 2 *
          (((AmenableActionSofic.boundary (D.sets n) g).card : ℝ) +
            (AmenableActionSofic.boundary (D.sets n) g⁻¹).card) :=
        Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_left (sum_jump_sq_le _ _ _) (sq_nonneg _)
    _ ≤ _ :=
        (D.summable_weight_sq_mul_boundary g).sum_le_tsum _
          (fun _ _ => mul_nonneg (sq_nonneg _) (by positivity))

/-- The Haagerup cocycle `b(g) ∈ ℓ²(ℕ × G, ℝ)`. -/
def cocycle (g : G) : CocycleSpace G :=
  ⟨D.cocycleFun g, D.memℓp_cocycleFun g⟩

@[simp]
theorem cocycle_apply (g : G) (i : ℕ × G) : D.cocycle g i = D.cocycleFun g i :=
  rfl

theorem cocycle_one : D.cocycle 1 = 0 := by
  apply lp.ext
  rw [lp.coeFn_zero]
  funext i
  change D.weight i.1 * jump (D.sets i.1) 1 i.2 = 0
  rw [jump_one, mul_zero]

/-- The cocycle identity `b(gh) = b(g) + π_g b(h)`. -/
theorem cocycle_mul (g h : G) :
    D.cocycle (g * h) = D.cocycle g + translation g (D.cocycle h) := by
  apply lp.ext
  rw [lp.coeFn_add]
  funext i
  obtain ⟨n, x⟩ := i
  rw [Pi.add_apply]
  change D.weight n * jump (D.sets n) (g * h) x =
    D.weight n * jump (D.sets n) g x + D.weight n * jump (D.sets n) h (g⁻¹ * x)
  rw [jump_mul]
  ring

/-- The affine isometric action `ξ ↦ π_g ξ + b(g)`. -/
def affine (g : G) (ξ : CocycleSpace G) : CocycleSpace G :=
  translation g ξ + D.cocycle g

theorem affine_one (ξ : CocycleSpace G) : D.affine 1 ξ = ξ := by
  unfold affine
  rw [translation_one, D.cocycle_one, add_zero]

theorem affine_mul (g h : G) (ξ : CocycleSpace G) :
    D.affine (g * h) ξ = D.affine g (D.affine h ξ) := by
  unfold affine
  rw [translation_mul, D.cocycle_mul, map_add]
  abel

theorem dist_affine (g : G) (ξ η : CocycleSpace G) :
    dist (D.affine g ξ) (D.affine g η) = dist ξ η := by
  unfold affine
  rw [dist_add_right, LinearIsometryEquiv.dist_map]

/-- If `g⁻¹Aₙ` misses `Aₙ`, then `‖b(g)‖² ≥ 2ⁿ`. -/
theorem pow_le_norm_cocycle_sq {g : G} {n : ℕ}
    (hg : ∀ x ∈ D.sets n, g⁻¹ * x ∉ D.sets n) :
    (2 : ℝ) ^ n ≤ ‖D.cocycle g‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum : Summable fun i => ‖D.cocycle g i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff hp).1 (lp.memℓp (D.cocycle g))
  have hnorm : ‖D.cocycle g‖ ^ 2 = ∑' i, ‖D.cocycle g i‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [← lp.norm_rpow_eq_tsum hp (D.cocycle g), rpow_two_toReal]
  have hterm : ∀ x ∈ D.sets n,
      ‖D.cocycle g (n, x)‖ ^ (2 : ℝ≥0∞).toReal = 2 ^ n / (D.sets n).card := by
    intro x hx
    rw [norm_rpow_two_toReal]
    change (D.weight n * jump (D.sets n) g x) ^ 2 = _
    unfold jump
    rw [if_neg (hg x hx), if_pos hx, mul_pow, D.weight_sq]
    norm_num
  have hfin : ∑ i ∈ ({n} : Finset ℕ) ×ˢ D.sets n,
      ‖D.cocycle g i‖ ^ (2 : ℝ≥0∞).toReal = 2 ^ n := by
    rw [Finset.sum_product, Finset.sum_singleton, Finset.sum_congr rfl hterm,
      Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact div_mul_cancel₀ _ (D.card_pos n).ne'
  rw [hnorm]
  calc (2 : ℝ) ^ n
      = ∑ i ∈ ({n} : Finset ℕ) ×ˢ D.sets n, ‖D.cocycle g i‖ ^ (2 : ℝ≥0∞).toReal :=
        hfin.symm
    _ ≤ _ := hsum.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)

/-- **Properness.**  Every sublevel set of `g ↦ ‖b(g)‖` is finite. -/
theorem cocycle_proper (R : ℝ) : {g : G | ‖D.cocycle g‖ ≤ R}.Finite := by
  classical
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R ^ 2) (by norm_num : (1 : ℝ) < 2)
  refine (((D.sets n) ×ˢ (D.sets n)).image fun p => p.1 * p.2⁻¹).finite_toSet.subset ?_
  intro g hg
  by_contra hmem
  have hsep : ∀ x ∈ D.sets n, g⁻¹ * x ∉ D.sets n := by
    intro x hx hx'
    apply hmem
    refine Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨(x, g⁻¹ * x), Finset.mem_product.mpr ⟨hx, hx'⟩, ?_⟩)
    change x * (g⁻¹ * x)⁻¹ = g
    rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have hg' : ‖D.cocycle g‖ ≤ R := hg
  have h₁ := D.pow_le_norm_cocycle_sq hsep
  have h₂ : ‖D.cocycle g‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg' 2
  linarith

end FolnerData

/-- **Haagerup property of countable amenable groups** (Bekka--Chérix--Valette).
There is a 1-cocycle for the translation representation on `ℓ²(ℕ × G, ℝ)`
whose norm is proper. -/
theorem exists_proper_cocycle {G : Type u} [Group G] [Countable G]
    (hG : Amenability.IsAmenable G) :
    ∃ b : G → CocycleSpace G,
      (∀ g h, b (g * h) = b g + translation g (b h)) ∧
        ∀ R : ℝ, {g : G | ‖b g‖ ≤ R}.Finite := by
  obtain ⟨D⟩ := exists_folnerData hG
  exact ⟨D.cocycle, D.cocycle_mul, D.cocycle_proper⟩

end

end GroupApproximation.Full.TWWUCT
