import GroupApproximation.Leavitt.RootDetectionBinary
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.RowAnnihilatorTransvection

/-!
# Simplicity of `EL_ι(R)` without division

`Leavitt.RootDetectionBinary` finds a nonzero elementary root in every nontrivial normal
subgroup of `EL_ι(R)` from two ring inputs, neither of which is division:

* `hcentral`: the only central unit of `R` is `1`;
* `hsplit`: for every `c` and every nonzero `d` there are `a, b` with `b * c * a = 0` and
  `a * (d * b) ≠ 0`.

The repository then closes the argument with two-sided division (`a * x * b = 1`).  That
fails for the Pestov 9.1 witness `R = LC(X, 𝔽₂) ⋊ ℤ`, which is stably finite.  This module
closes it with simplicity of `R` instead, and proves `hsplit` for such crossed products.

1. `elGen_mem_of_single_root`: one root `e_{ij}(x)` in a normal subgroup puts every
   `e_{kl}(a x b)` there.  Two Steinberg commutators give `e_{mi}(a x b)`, and
   `RowAnnihilator.elGen_mem_of_mem_spread` moves it everywhere.
2. `isSimpleGroup_elementaryGroup_of_split`: with at least three indices, `IsSimpleRing R`,
   `hcentral` and `hsplit`, `EL_ι(R)` is simple.  A detected root `x ≠ 0` lies in the level
   ideal `normalLevel`, so the level is `⊤`, and `relativeElementary_top` gives `N = ⊤`.
3. `crossedProduct_split_annihilator` proves `hsplit` for a ring spanned by the
   `φ (c j) * u ^ j` with `u ^ j * φ a = φ (σ j a) * u ^ j`.  It uses the same localisation
   hypothesis `hkey` as the crossed-product simplicity theorem of the Pestov 9.1 ring lane.
   - Write `c = ∑ φ (c_j) u^j` and `d = ∑ φ (d_j) u^j` with `φ (d_{j₀}) ≠ 0`.
   - Pick `r` with `j + r ≠ 0` on the support of `c`.
   - Take `e` from `hkey` for `d_{j₀}` and `F = (S_c + r) ∪ ((S_d - j₀) \ {0})`.
   - Set `a = u^r φ e` and `b = u^{-j₀} φ e`.

   Every term of `b c a` carries `e σ_{j+r}(e) = 0`.  `a d b` collapses to
   `u^r φ (e d_{j₀} e)`, which is nonzero: `b' e d_{j₀} e = e`, and `φ e ≠ 0` by the covering
   clause of `hkey`.  Injectivity of `φ` is not used.
4. `isSimpleGroup_elementaryGroup_crossedProduct` combines 2 and 3 with the centre hypothesis
   "central elements are `0` or `1`".
-/

namespace GroupApproximation
namespace Pestov91

open ElementarySimplicity

section Commutators

variable {G : Type*} [Group G]

/-- A commutator whose left entry lies in a normal subgroup lies in it. -/
theorem commutator_mem_of_left_mem (N : Subgroup G) [hN : N.Normal] {X : G} (hX : X ∈ N)
    (Y : G) : X * Y * X⁻¹ * Y⁻¹ ∈ N := by
  have h : X * Y * X⁻¹ * Y⁻¹ = X * (Y * X⁻¹ * Y⁻¹) := by simp only [mul_assoc]
  rw [h]
  exact N.mul_mem hX (hN.conj_mem _ (N.inv_mem hX) Y)

/-- A commutator whose right entry lies in a normal subgroup lies in it. -/
theorem commutator_mem_of_right_mem (N : Subgroup G) [hN : N.Normal] (X : G) {Y : G}
    (hY : Y ∈ N) : X * Y * X⁻¹ * Y⁻¹ ∈ N :=
  N.mul_mem (hN.conj_mem _ hY X) (N.inv_mem hY)

end Commutators

section Spread

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **One root spreads.**  With at least three indices, a single root `e_{ij}(x)` in a normal
subgroup puts `e_{kl}(a x b)` in it for all `k ≠ l` and all `a, b`. -/
theorem elGen_mem_of_single_root (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {i j : ι} (hij : i ≠ j) {x : R}
    (hx : elGen i j hij x ∈ N) {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * x * b) ∈ N := by
  obtain ⟨m, hmi, hmj⟩ := exists_third_index hcard i j
  have hbase : ∀ a b : R, elGen m i hmi (a * x * b) ∈ N := by
    intro a b
    have h1 : elGen m j hmj (a * x) ∈ N := by
      rw [← elGen_commutator m i j hmi hij hmj a x]
      exact commutator_mem_of_right_mem N _ hx
    rw [← elGen_commutator m j i hmj (Ne.symm hij) hmi (a * x) b]
    exact commutator_mem_of_left_mem N h1 _
  exact RowAnnihilator.elGen_mem_of_mem_spread hcard N hmi hbase hkl a b

end Spread

section Detection

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Root detection without division.**  For at least three indices, no nontrivial central
unit and the split obligation `hsplit`, every nontrivial normal subgroup of `EL_ι(R)` contains
a nonzero root.  This is `RootDetectionBinary.rootDetection_of_leavittFamily` with the
hypothesis `hsplit` in place of its division-based discharge. -/
theorem rootDetection_of_split (hcard : 3 ≤ Fintype.card ι)
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1)
    (hsplit : ∀ c d : R, d ≠ 0 → ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0) :
    RootDetection ι R := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro N hN hbot
  haveI : N.Normal := hN
  have hex : ¬ ∀ z ∈ N, z = 1 := fun h =>
    hbot ((Subgroup.eq_bot_iff_forall N).mpr h)
  push Not at hex
  obtain ⟨g, hg, hgne⟩ := hex
  by_cases hdiag : ∀ u v : ι, u ≠ v → elMat (g⁻¹) u v = 0
  · have hgdiag : ∀ u v : ι, u ≠ v → elMat g u v = 0 := by
      intro u v huv
      have h := RootDetectionBinary.elMat_inv_offDiag (g⁻¹) hdiag huv
      rwa [inv_inv] at h
    exact RootDetectionBinary.exists_elGen_mem_of_diagonal hcentral N g hg hgne hgdiag
  · push Not at hdiag
    obtain ⟨l, p, hlp, hd⟩ := hdiag
    exact RootDetectionBinary.exists_elGen_mem_of_offDiag_inv hcard hsplit N g hg hlp hd

/-- **Simplicity of `EL_ι(R)` without division.**  For at least three indices, a simple
coefficient ring with no nontrivial central unit that satisfies `hsplit` has a simple
elementary group. -/
theorem isSimpleGroup_elementaryGroup_of_split (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1)
    (hsplit : ∀ c d : R, d ≠ 0 → ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0) :
    IsSimpleGroup (elementaryGroup ι R) := by
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i₀, j₀, hij₀⟩ := exists_pair_ne ι
  haveI : Nontrivial (elementaryGroup ι R) :=
    ⟨⟨elGen i₀ j₀ hij₀ 1, 1, LeavittMark.elGen_ne_one_of_ne_zero i₀ j₀ hij₀ one_ne_zero⟩⟩
  refine { eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  haveI : N.Normal := hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨i, j, hij, x, hx0, hxN⟩ := rootDetection_of_split hcard hcentral hsplit N hN hbot
    have hxlevel : x ∈ normalLevel hcard N :=
      (mem_normalLevel_iff hcard N).mpr fun k l hkl => by
        simpa only [one_mul, mul_one] using elGen_mem_of_single_root hcard N hij hxN hkl 1 1
    have hlevel : normalLevel hcard N = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top (normalLevel hcard N) with h | h
      · rw [h, TwoSidedIdeal.mem_bot] at hxlevel
        exact absurd hxlevel hx0
      · exact h
    have hle := relativeElementary_normalLevel_le hcard N
    rw [hlevel, relativeElementary_top] at hle
    exact top_le_iff.mp hle

/-- In a nontrivial ring whose central elements are `0` or `1`, the only central unit is `1`. -/
theorem central_unit_eq_one_of_central_zero_or_one [Nontrivial R]
    (hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1) :
    ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1 := by
  rintro lam hlam ⟨mu, hlm, -⟩
  rcases hR lam fun r => (hlam r).symm with h | h
  · rw [h, zero_mul] at hlm
    exact absurd hlm zero_ne_one
  · exact h

/-- `isSimpleGroup_elementaryGroup_of_split` with the centre hypothesis in the form
"central elements are `0` or `1`". -/
theorem isSimpleGroup_elementaryGroup_of_split_of_central_zero_or_one
    (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1)
    (hsplit : ∀ c d : R, d ≠ 0 → ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0) :
    IsSimpleGroup (elementaryGroup ι R) :=
  isSimpleGroup_elementaryGroup_of_split hcard (central_unit_eq_one_of_central_zero_or_one hR)
    hsplit

end Detection

section CrossedProduct

variable {R A : Type*} [Ring R] [CommRing A]

/-- **The split obligation for a crossed product.**  In a ring spanned by the `φ (c j) * u ^ j`,
with `u ^ j` acting on `φ` by `σ j`, the localisation hypothesis `hkey` gives, for every `c` and
every nonzero `d`, elements `a, b` with `b * c * a = 0` and `a * (d * b) ≠ 0`. -/
theorem crossedProduct_split_annihilator (φ : A →+* R) (u : Rˣ) (σ : ℤ → A → A)
    (hconj : ∀ (j : ℤ) (a : A), ((u ^ j : Rˣ) : R) * φ a = φ (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → A), x = ∑ j ∈ S, φ (c j) * ((u ^ j : Rˣ) : R))
    (hkey : ∀ a : A, a ≠ 0 → ∀ F : Finset ℤ, (0 : ℤ) ∉ F → ∃ e b : A, b * e * a * e = e ∧
      (∀ j ∈ F, e * σ j e = 0) ∧ ∃ s : Finset ℤ, ∏ i ∈ s, (1 - σ i e) = 0)
    (c d : R) (hd : d ≠ 0) :
    ∃ a b : R, b * c * a = 0 ∧ a * (d * b) ≠ 0 := by
  haveI : Nontrivial R := ⟨⟨d, 0, hd⟩⟩
  obtain ⟨S, cc, rfl⟩ := hspan c
  obtain ⟨T, dd, rfl⟩ := hspan d
  obtain ⟨j₀, hj₀T, hj₀⟩ : ∃ j₀ ∈ T, φ (dd j₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finset.sum_eq_zero fun j hj => by rw [h j hj, zero_mul])
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (S.image fun j => -j)
  have hr' : ∀ j ∈ S, j + r ≠ 0 := fun j hj h =>
    hr (Finset.mem_image.mpr ⟨j, hj, by omega⟩)
  have hF : (0 : ℤ) ∉ S.image (fun j => j + r) ∪ (T.image fun j => j - j₀).erase 0 := by
    intro h0
    rcases Finset.mem_union.mp h0 with h | h
    · obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h
      exact hr' j hj hj0
    · exact Finset.notMem_erase _ _ h
  obtain ⟨e, b', hbe, hFe, s, hs⟩ := hkey (dd j₀) (fun h => hj₀ (by rw [h, map_zero])) _ hF
  refine ⟨((u ^ r : Rˣ) : R) * φ e, ((u ^ (-j₀) : Rˣ) : R) * φ e, ?_, ?_⟩
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hmem : j + r ∈ S.image (fun j => j + r) ∪ (T.image fun j => j - j₀).erase 0 :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hu : ((u ^ j : Rˣ) : R) * ((u ^ r : Rˣ) : R) = ((u ^ (j + r) : Rˣ) : R) := by
      rw [← Units.val_mul, ← zpow_add]
    calc ((u ^ (-j₀) : Rˣ) : R) * φ e * (φ (cc j) * ((u ^ j : Rˣ) : R)) *
          (((u ^ r : Rˣ) : R) * φ e)
        = ((u ^ (-j₀) : Rˣ) : R) * φ e * φ (cc j) *
            ((((u ^ j : Rˣ) : R) * ((u ^ r : Rˣ) : R)) * φ e) := by simp only [mul_assoc]
      _ = ((u ^ (-j₀) : Rˣ) : R) * φ e * φ (cc j) *
            (φ (σ (j + r) e) * ((u ^ (j + r) : Rˣ) : R)) := by rw [hu, hconj (j + r) e]
      _ = ((u ^ (-j₀) : Rˣ) : R) * φ (cc j * (e * σ (j + r) e)) *
            ((u ^ (j + r) : Rˣ) : R) := by
          rw [show cc j * (e * σ (j + r) e) = e * cc j * σ (j + r) e by ring]
          simp only [map_mul, mul_assoc]
      _ = 0 := by rw [hFe _ hmem, mul_zero, map_zero, mul_zero, zero_mul]
  · have hsum : ((u ^ r : Rˣ) : R) * φ e *
        ((∑ j ∈ T, φ (dd j) * ((u ^ j : Rˣ) : R)) * (((u ^ (-j₀) : Rˣ) : R) * φ e))
        = ((u ^ r : Rˣ) : R) * φ (e * dd j₀ * e) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_eq_single j₀]
      · have hu : ((u ^ j₀ : Rˣ) : R) * ((u ^ (-j₀) : Rˣ) : R) = 1 := by
          rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
        calc ((u ^ r : Rˣ) : R) * φ e * (φ (dd j₀) * ((u ^ j₀ : Rˣ) : R) *
              (((u ^ (-j₀) : Rˣ) : R) * φ e))
            = ((u ^ r : Rˣ) : R) * φ e * φ (dd j₀) *
                ((((u ^ j₀ : Rˣ) : R) * ((u ^ (-j₀) : Rˣ) : R)) * φ e) := by
              simp only [mul_assoc]
          _ = ((u ^ r : Rˣ) : R) * φ (e * dd j₀ * e) := by
              rw [hu, one_mul]
              simp only [map_mul, mul_assoc]
      · intro j hjT hj
        have hmem : j - j₀ ∈ S.image (fun j => j + r) ∪ (T.image fun j => j - j₀).erase 0 :=
          Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hj, Finset.mem_image.mpr ⟨j, hjT, rfl⟩⟩)
        have hu : ((u ^ j : Rˣ) : R) * ((u ^ (-j₀) : Rˣ) : R) = ((u ^ (j - j₀) : Rˣ) : R) := by
          rw [← Units.val_mul, ← zpow_add, ← sub_eq_add_neg]
        calc ((u ^ r : Rˣ) : R) * φ e * (φ (dd j) * ((u ^ j : Rˣ) : R) *
              (((u ^ (-j₀) : Rˣ) : R) * φ e))
            = ((u ^ r : Rˣ) : R) * φ e * φ (dd j) *
                ((((u ^ j : Rˣ) : R) * ((u ^ (-j₀) : Rˣ) : R)) * φ e) := by
              simp only [mul_assoc]
          _ = ((u ^ r : Rˣ) : R) * φ e * φ (dd j) *
                (φ (σ (j - j₀) e) * ((u ^ (j - j₀) : Rˣ) : R)) := by
              rw [hu, hconj (j - j₀) e]
          _ = ((u ^ r : Rˣ) : R) * φ (dd j * (e * σ (j - j₀) e)) *
                ((u ^ (j - j₀) : Rˣ) : R) := by
              rw [show dd j * (e * σ (j - j₀) e) = e * dd j * σ (j - j₀) e by ring]
              simp only [map_mul, mul_assoc]
          _ = 0 := by rw [hFe _ hmem, mul_zero, map_zero, mul_zero, zero_mul]
      · intro h
        exact absurd hj₀T h
    rw [hsum]
    intro h0
    have h1 : φ (e * dd j₀ * e) = 0 := (Units.mul_right_eq_zero (u ^ r)).mp h0
    have h2 : φ e = 0 := by
      calc φ e = φ (b' * e * dd j₀ * e) := by rw [hbe]
        _ = φ b' * φ (e * dd j₀ * e) := by simp only [map_mul, mul_assoc]
        _ = 0 := by rw [h1, mul_zero]
    have h3 : ∀ i : ℤ, φ (σ i e) = 0 := fun i =>
      (Units.mul_left_eq_zero (u ^ i)).mp (by rw [← hconj i e, h2, mul_zero])
    have h4 : ∀ t : Finset ℤ, φ (∏ i ∈ t, (1 - σ i e)) = 1 := by
      intro t
      induction t using Finset.induction_on with
      | empty => rw [Finset.prod_empty, map_one]
      | insert i t hi ih =>
        rw [Finset.prod_insert hi, map_mul, map_sub, map_one, h3 i, sub_zero, one_mul, ih]
    have h5 := h4 s
    rw [hs, map_zero] at h5
    exact zero_ne_one h5

end CrossedProduct

section Assembly

variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [Ring R] [CommRing A]

/-- **Simplicity of `EL_ι(R)` for a simple crossed product.**  With at least three indices, a
simple ring `R` whose central elements are `0` or `1`, spanned by the `φ (c j) * u ^ j` and
satisfying the localisation hypothesis `hkey`, has a simple elementary group. -/
theorem isSimpleGroup_elementaryGroup_crossedProduct (hcard : 3 ≤ Fintype.card ι)
    [IsSimpleRing R] (hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1)
    (φ : A →+* R) (u : Rˣ) (σ : ℤ → A → A)
    (hconj : ∀ (j : ℤ) (a : A), ((u ^ j : Rˣ) : R) * φ a = φ (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → A), x = ∑ j ∈ S, φ (c j) * ((u ^ j : Rˣ) : R))
    (hkey : ∀ a : A, a ≠ 0 → ∀ F : Finset ℤ, (0 : ℤ) ∉ F → ∃ e b : A, b * e * a * e = e ∧
      (∀ j ∈ F, e * σ j e = 0) ∧ ∃ s : Finset ℤ, ∏ i ∈ s, (1 - σ i e) = 0) :
    IsSimpleGroup (elementaryGroup ι R) :=
  isSimpleGroup_elementaryGroup_of_split_of_central_zero_or_one hcard hR
    (crossedProduct_split_annihilator φ u σ hconj hspan hkey)

end Assembly

end Pestov91
end GroupApproximation
