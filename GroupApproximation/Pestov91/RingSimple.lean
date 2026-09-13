import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen

/-!
# Simplicity of the crossed product `LC(X, K) ⋊ ℤ` of a free minimal system

For Pestov's Open Question 9.1 the witness ring is `R = LC(X, 𝔽_q) ⋊ ℤ`, with `X` an infinite
minimal subshift. This module proves that `R` is a simple ring: its only two-sided ideals are
`⊥` and `⊤`. The argument is the diagonal cut of
`research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`, §1.3. It is the
case that the witness needs of the field-general simplicity criterion for Steinberg algebras
(Clark and Edie-Michell, arXiv:1403.4684, Corollary 4.6; Steinberg, arXiv:1408.6014,
Corollary 3.6), whose origin is the criterion of Brown, Clark, Farthing and Sims
(arXiv:1204.3127), stated over `ℂ`. Nothing is imported: the case needed is proved below.

1. `crossedProduct_one_mem` is the ring-theoretic core. Let `R` be a ring, `ι : A →+* R` with `A`
   commutative, and `u` a unit with `u ^ j * ι a = ι (σ j a) * u ^ j`, such that every element is
   a finite sum `∑ ι (c j) * u ^ j`. Suppose every nonzero `a : A` admits, for each finite set
   `F ∌ 0`, an element `e` with `b * e * a * e = e`, `e * σ j e = 0` for `j ∈ F`, and
   `∏ i ∈ s, (1 - σ i e) = 0` for some finite `s`. Then every nonzero two-sided ideal contains
   `1`. Cutting a nonzero element by `ι e` on both sides leaves `ι e`, and the translates
   `ι (σ i e) = u ^ i * ι e * u ^ (-i)` generate `1`.
2. `locallyConstant_cut_key` supplies that hypothesis for `A = LocallyConstant X K`, with `K` a
   field and `σ j f = f ∘ τ j`, from freeness (`τ j x ≠ x` for `j ≠ 0`) and a finite covering
   property of nonempty open sets. Take `e` the indicator of a clopen `W` on which `a` is constant
   and nonzero, with `τ j W` disjoint from `W` for `j ∈ F`.
3. `isSimpleRing_of_free_of_cover` combines the two; `isSimpleRing_of_minimal_free` derives the
   covering property from compactness and dense orbits. Neither uniqueness of the coefficients
   nor injectivity of `ι` is used.
-/

namespace GroupApproximation.Pestov91

section Abstract

variable {R A : Type*} [Ring R] [CommRing A]

/-- The diagonal cut: in a `ℤ`-graded ring over a commutative `A` satisfying the localisation and
covering hypothesis `hkey`, a two-sided ideal with a nonzero element contains `1`. -/
theorem crossedProduct_one_mem (ι : A →+* R) (u : Rˣ) (σ : ℤ → A → A)
    (hconj : ∀ (j : ℤ) (a : A), ((u ^ j : Rˣ) : R) * ι a = ι (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → A), x = ∑ j ∈ S, ι (c j) * ((u ^ j : Rˣ) : R))
    (hkey : ∀ a : A, a ≠ 0 → ∀ F : Finset ℤ, (0 : ℤ) ∉ F → ∃ e b : A, b * e * a * e = e ∧
      (∀ j ∈ F, e * σ j e = 0) ∧ ∃ s : Finset ℤ, ∏ i ∈ s, (1 - σ i e) = 0)
    (I : TwoSidedIdeal R) {x : R} (hxI : x ∈ I) (hx0 : x ≠ 0) : (1 : R) ∈ I := by
  obtain ⟨S, c, rfl⟩ := hspan x
  obtain ⟨j0, hj0S, hj0⟩ : ∃ j0 ∈ S, c j0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Finset.sum_eq_zero fun j hj => by rw [h j hj, map_zero, zero_mul])
  obtain ⟨e, b, hbe, hF, s, hs⟩ :=
    hkey (c j0) hj0 ((S.image fun j => j - j0).erase 0) (Finset.notMem_erase _ _)
  have hcut : ι b * ι e * ((∑ j ∈ S, ι (c j) * ((u ^ j : Rˣ) : R)) *
      ((u ^ (-j0) : Rˣ) : R)) * ι e = ι e := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single j0]
    · rw [mul_assoc (ι (c j0)), ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        Units.val_one, mul_one, ← map_mul ι, ← map_mul ι, ← map_mul ι, hbe]
    · intro j hjS hj
      have hk : j - j0 ∈ (S.image fun j => j - j0).erase 0 :=
        Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hj, Finset.mem_image.mpr ⟨j, hjS, rfl⟩⟩
      rw [mul_assoc (ι (c j)), ← Units.val_mul, ← zpow_add, ← sub_eq_add_neg]
      calc ι b * ι e * (ι (c j) * ((u ^ (j - j0) : Rˣ) : R)) * ι e
          = ι b * ι e * ι (c j) * (((u ^ (j - j0) : Rˣ) : R) * ι e) := by
            simp only [mul_assoc]
        _ = ι (b * e * c j * σ (j - j0) e) * ((u ^ (j - j0) : Rˣ) : R) := by
            rw [hconj]
            simp only [map_mul, mul_assoc]
        _ = 0 := by
            rw [show b * e * c j * σ (j - j0) e = b * c j * (e * σ (j - j0) e) by ring,
              hF _ hk, mul_zero, map_zero, zero_mul]
    · exact fun h => absurd hj0S h
  have heI : ι e ∈ I := by
    have h := I.mul_mem_right _ (ι e) (I.mul_mem_left (ι b * ι e) _
      (I.mul_mem_right _ ((u ^ (-j0) : Rˣ) : R) hxI))
    rwa [hcut] at h
  have hσI : ∀ i, ι (σ i e) ∈ I := fun i => by
    have h := I.mul_mem_right _ ((u ^ i)⁻¹ : Rˣ) (I.mul_mem_left ((u ^ i : Rˣ) : R) _ heI)
    rwa [hconj, Units.mul_inv_cancel_right] at h
  have hprod : ∀ t : Finset ℤ, 1 - ι (∏ i ∈ t, (1 - σ i e)) ∈ I := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one, sub_self]; exact I.zero_mem
    | insert i t hi ih =>
      have h := I.add_mem (I.mul_mem_right (ι (σ i e)) (ι (∏ k ∈ t, (1 - σ k e))) (hσI i)) ih
      have hid : ι (σ i e) * ι (∏ k ∈ t, (1 - σ k e)) + (1 - ι (∏ k ∈ t, (1 - σ k e)))
          = 1 - ι (∏ k ∈ insert i t, (1 - σ k e)) := by
        rw [Finset.prod_insert hi, map_mul, map_sub, map_one, sub_mul, one_mul]
        abel
      rwa [hid] at h
  have h1 := hprod s
  rwa [hs, map_zero, sub_zero] at h1

/-- A nontrivial `ℤ`-graded ring over a commutative `A` satisfying `hkey` is simple. -/
theorem crossedProduct_isSimpleRing [Nontrivial R] (ι : A →+* R) (u : Rˣ) (σ : ℤ → A → A)
    (hconj : ∀ (j : ℤ) (a : A), ((u ^ j : Rˣ) : R) * ι a = ι (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → A), x = ∑ j ∈ S, ι (c j) * ((u ^ j : Rˣ) : R))
    (hkey : ∀ a : A, a ≠ 0 → ∀ F : Finset ℤ, (0 : ℤ) ∉ F → ∃ e b : A, b * e * a * e = e ∧
      (∀ j ∈ F, e * σ j e = 0) ∧ ∃ s : Finset ℤ, ∏ i ∈ s, (1 - σ i e) = 0) :
    IsSimpleRing R := by
  refine IsSimpleRing.of_eq_bot_or_eq_top (R := R) fun I => ?_
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · obtain ⟨x, hxI, hx0⟩ := hI
    exact Or.inr ((TwoSidedIdeal.one_mem_iff I).mp
      (crossedProduct_one_mem ι u σ hconj hspan hkey I hxI hx0))
  · refine Or.inl (TwoSidedIdeal.ext fun x => ?_)
    push Not at hI
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨hI x, fun h => by rw [h]; exact I.zero_mem⟩

end Abstract

section LocallyConstant

variable {X K : Type*} [TopologicalSpace X] [Field K]

/-- A nonzero locally constant function is constant and nonzero on a clopen set `W` that is
disjoint from its images under `τ j` for the finitely many `j ∈ F`, when no `τ j` with `j ≠ 0`
has a fixed point. -/
theorem exists_clopen_free_nbhd [TotallySeparatedSpace X] (τ : ℤ → X → X)
    (hτ : ∀ j, Continuous (τ j)) (hfree : ∀ j : ℤ, j ≠ 0 → ∀ x, τ j x ≠ x)
    (a : LocallyConstant X K) (ha : a ≠ 0) (F : Finset ℤ) (hF : (0 : ℤ) ∉ F) :
    ∃ W : Set X, IsClopen W ∧ W.Nonempty ∧ ∃ c : K, c ≠ 0 ∧ (∀ y ∈ W, a y = c) ∧
      ∀ j ∈ F, ∀ y ∈ W, τ j y ∉ W := by
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (LocallyConstant.ext fun y => by
      simp only [h y, LocallyConstant.coe_zero, Pi.zero_apply])
  have hsep : ∀ j : ℤ, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ (j ∈ F → τ j x ∉ C) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨C, hC, hxC, hyC⟩ :=
        exists_isClopen_of_totally_separated (hfree j (by rintro rfl; exact hF hj) x).symm
      exact ⟨C, hC, hxC, fun _ => hyC⟩
    · exact ⟨Set.univ, isClopen_univ, Set.mem_univ x, fun h => absurd h hj⟩
  choose C hC hxC hτC using hsep
  refine ⟨{y | a y = a x} ∩ ⋂ j ∈ F, (C j ∩ τ j ⁻¹' (C j)ᶜ), ?_, ⟨x, ?_⟩, a x, hx,
    fun y hy => hy.1, ?_⟩
  · exact (a.isLocallyConstant.isClopen_fiber (a x)).inter
      (isClopen_biInter_finset fun j _ => (hC j).inter ((hC j).compl.preimage (hτ j)))
  · exact ⟨rfl, Set.mem_iInter₂.mpr fun j hj => ⟨hxC j, hτC j hj⟩⟩
  · intro j hj y hy hτy
    exact (Set.mem_iInter₂.mp hy.2 j hj).2 (Set.mem_iInter₂.mp hτy.2 j hj).1

/-- Dense orbits and compactness: finitely many `τ i` pull a nonempty open set over all of `X`. -/
theorem exists_finset_cover_of_dense_orbits [CompactSpace X] (τ : ℤ → X → X)
    (hτ : ∀ j, Continuous (τ j)) (hmin : ∀ x, Dense (Set.range fun j => τ j x)) {W : Set X}
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ s : Finset ℤ, ∀ y, ∃ i ∈ s, τ i y ∈ W := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i => τ i ⁻¹' W)
    (fun i => hW.preimage (hτ i)) fun y _ => by
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := (hmin y).exists_mem_open hW hne
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  exact ⟨s, fun y => by simpa using hs (Set.mem_univ y)⟩

/-- The hypothesis `hkey` of `crossedProduct_one_mem` for `LocallyConstant X K`, with
`σ j f = f ∘ τ j`, from freeness and the finite covering property of nonempty open sets. -/
theorem locallyConstant_cut_key [TotallySeparatedSpace X] (τ : ℤ → X → X)
    (hτ : ∀ j, Continuous (τ j)) (hfree : ∀ j : ℤ, j ≠ 0 → ∀ x, τ j x ≠ x)
    (hcover : ∀ W : Set X, IsOpen W → W.Nonempty → ∃ s : Finset ℤ, ∀ y, ∃ i ∈ s, τ i y ∈ W)
    (σ : ℤ → LocallyConstant X K → LocallyConstant X K) (hσ : ∀ j f x, σ j f x = f (τ j x))
    (a : LocallyConstant X K) (ha : a ≠ 0) (F : Finset ℤ) (hF : (0 : ℤ) ∉ F) :
    ∃ e b : LocallyConstant X K, b * e * a * e = e ∧ (∀ j ∈ F, e * σ j e = 0) ∧
      ∃ s : Finset ℤ, ∏ i ∈ s, (1 - σ i e) = 0 := by
  obtain ⟨W, hW, hne, c, hc, hac, hdisj⟩ := exists_clopen_free_nbhd τ hτ hfree a ha F hF
  obtain ⟨s, hs⟩ := hcover W hW.isOpen hne
  have he1 : ∀ y ∈ W, LocallyConstant.charFn K hW y = 1 := fun y hy =>
    (LocallyConstant.charFn_eq_one K y hW).mpr hy
  have he0 : ∀ y ∉ W, LocallyConstant.charFn K hW y = 0 := fun y hy =>
    (LocallyConstant.charFn_eq_zero K y hW).mpr hy
  refine ⟨LocallyConstant.charFn K hW, LocallyConstant.const X c⁻¹, ?_, ?_, s, ?_⟩
  · ext y
    by_cases hy : y ∈ W
    · simp only [LocallyConstant.mul_apply, he1 y hy, hac y hy, LocallyConstant.coe_const,
        Function.const_apply, mul_one, inv_mul_cancel₀ hc]
    · simp only [LocallyConstant.mul_apply, he0 y hy, mul_zero]
  · intro j hj
    ext y
    by_cases hy : y ∈ W
    · simp only [LocallyConstant.mul_apply, hσ, he0 _ (hdisj j hj y hy), mul_zero,
        LocallyConstant.coe_zero, Pi.zero_apply]
    · simp only [LocallyConstant.mul_apply, he0 y hy, zero_mul, LocallyConstant.coe_zero,
        Pi.zero_apply]
  · ext y
    obtain ⟨i, hi, hiy⟩ := hs y
    have hev : ∀ t : Finset ℤ, (∏ k ∈ t, (1 - σ k (LocallyConstant.charFn K hW))) y
        = ∏ k ∈ t, (1 - σ k (LocallyConstant.charFn K hW)) y := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, LocallyConstant.coe_one, Pi.one_apply]
      | insert k t hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk, LocallyConstant.mul_apply, ih]
    rw [hev s]
    show ∏ k ∈ s, (1 - σ k (LocallyConstant.charFn K hW)) y = 0
    refine Finset.prod_eq_zero hi ?_
    rw [show (1 - σ i (LocallyConstant.charFn K hW)) y
        = 1 - σ i (LocallyConstant.charFn K hW) y from rfl, hσ, he1 _ hiy, sub_self]

end LocallyConstant

/-- **Simplicity of `LC(X, K) ⋊ ℤ`, covering form.** Let `X` be totally separated and `τ j`
continuous maps with no fixed point for `j ≠ 0`, such that finitely many `τ i` pull every
nonempty open set over `X`. Let `R` be a nontrivial ring with `ι : LocallyConstant X K →+* R` and
a unit `u` implementing `σ j f = f ∘ τ j` by conjugation, such that every element is a finite sum
`∑ ι (c j) * u ^ j`. Then `R` is a simple ring. -/
theorem isSimpleRing_of_free_of_cover {R X K : Type*} [Ring R] [Nontrivial R]
    [TopologicalSpace X] [TotallySeparatedSpace X] [Field K]
    (ι : LocallyConstant X K →+* R) (u : Rˣ) (τ : ℤ → X → X) (hτ : ∀ j, Continuous (τ j))
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ x, τ j x ≠ x)
    (hcover : ∀ W : Set X, IsOpen W → W.Nonempty → ∃ s : Finset ℤ, ∀ y, ∃ i ∈ s, τ i y ∈ W)
    (σ : ℤ → LocallyConstant X K → LocallyConstant X K) (hσ : ∀ j f x, σ j f x = f (τ j x))
    (hconj : ∀ (j : ℤ) (a : LocallyConstant X K),
      ((u ^ j : Rˣ) : R) * ι a = ι (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → LocallyConstant X K),
      x = ∑ j ∈ S, ι (c j) * ((u ^ j : Rˣ) : R)) :
    IsSimpleRing R :=
  crossedProduct_isSimpleRing ι u σ hconj hspan fun a ha F hF =>
    locallyConstant_cut_key τ hτ hfree hcover σ hσ a ha F hF

/-- **Simplicity of `LC(X, K) ⋊ ℤ`, minimal form.** As `isSimpleRing_of_free_of_cover`, for `X`
compact and every orbit `{τ j x}` dense. -/
theorem isSimpleRing_of_minimal_free {R X K : Type*} [Ring R] [Nontrivial R] [TopologicalSpace X]
    [CompactSpace X] [TotallySeparatedSpace X] [Field K]
    (ι : LocallyConstant X K →+* R) (u : Rˣ) (τ : ℤ → X → X) (hτ : ∀ j, Continuous (τ j))
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ x, τ j x ≠ x) (hmin : ∀ x, Dense (Set.range fun j => τ j x))
    (σ : ℤ → LocallyConstant X K → LocallyConstant X K) (hσ : ∀ j f x, σ j f x = f (τ j x))
    (hconj : ∀ (j : ℤ) (a : LocallyConstant X K),
      ((u ^ j : Rˣ) : R) * ι a = ι (σ j a) * ((u ^ j : Rˣ) : R))
    (hspan : ∀ x : R, ∃ (S : Finset ℤ) (c : ℤ → LocallyConstant X K),
      x = ∑ j ∈ S, ι (c j) * ((u ^ j : Rˣ) : R)) :
    IsSimpleRing R :=
  isSimpleRing_of_free_of_cover ι u τ hτ hfree
    (fun _ hW hne => exists_finset_cover_of_dense_orbits τ hτ hmin hW hne) σ hσ hconj hspan

end GroupApproximation.Pestov91
