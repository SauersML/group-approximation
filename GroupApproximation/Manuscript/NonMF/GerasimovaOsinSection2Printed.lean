import GroupApproximation.Manuscript.NonMF.GerasimovaOsinCombingNorm

/-!
# Gerasimova–Osin, §2, as printed

Gerasimova–Osin (arXiv:1910.14524v3), §2:

> **Definition 2.1.** Let `G` be a group.  A generalized combing of `G` is a map
> `C : G × G → 𝒫(G)`.  We say that the combing `C` is — symmetric if `C(x,y) = C(y,x)` for
> all `x, y ∈ G`; — `G`-equivariant if `C(gx,gy) = gC(x,y)` for all `x, y, g ∈ G`.
>
> **Definition 2.2.** A map `ℓ : G → [0,+∞)` is a pseudolength function on a group `G` if it
> is symmetric and satisfies the triangle inequality; that is, `ℓ(g⁻¹) = ℓ(g)` and
> `ℓ(gh) ≤ ℓ(g) + ℓ(h)` for all `g, h ∈ G`.  We say that `ℓ` is a length function if, in
> addition, `ℓ(g) = 0` if and only if `g = 1`.
>
> … `B(n) = {g ∈ G | ℓ(g) ≤ n}`.  To each generalized combing `C` we associate two growth
> functions `γ, ρ : ℕ → ℕ ∪ {∞}` … `γ(n) = sup_{g∈G} |C(1,g) ∩ B(n)|` (2) and
> `ρ(n) = sup_{g∈B(n)} sup_{x∈C(1,g)} ℓ(x)` (3).
>
> **Lemma 2.3.** Let `C` be a generalized combing such that the functions `γ` and `ρ` take
> only finite values.  Then for any element `s ∈ B(n)`, we have `|C(1,s)| ≤ γ(ρ(n))`.
>
> **Proposition 2.4.** Let `G` be a group endowed with a pseudolength function `ℓ` and let `S`
> be a subset of `G`.  Suppose that there exists a symmetric `G`-equivariant generalized
> combing `C` such that `C(1,s) ∩ C(s,g) ∩ C(1,g) ≠ ∅` (4) for all `s ∈ S` and `g ∈ G` and
> the associated growth functions `γ` and `ρ` take only finite values.  Then for every
> `a ∈ ℂG` and `n ∈ ℕ` such that `supp(a) ⊆ S ∩ B(n)`, we have `‖a‖ ≤ γ(ρ(n))^{3/2}‖a‖₂` (5).
> In particular, if `S` is a subsemigroup of `G` and `lim_{k→∞} √[k]{γ(ρ(k))} = 1`, then
> `r(a) = r₂(a)`.
>
> **Lemma 2.5.** Under the assumptions of Proposition 2.4, suppose additionally that
> `a ∈ ℝ₊G`.  Then for every `b ∈ ℝ₊G`, we have `‖ab‖₂ ≤ γ(ρ(n))^{3/2}‖a‖₂‖b‖₂` (6).

## Repository form

* An element of `ℂG` with support in a finite set `T` is `translationSum T c`; its operator
  norm is the norm of `C*_r(G)` and its `ℓ²`-norm is `reducedTwoNorm`.
* `γ` and `ρ` are `combGrowth` and `combRadius` with values in `ℕ∞`; since `ℓ` is real
  valued, `ρ` rounds `ℓ(x)` up to a natural number, which keeps `C(1,s) ⊆ B(ρ(n))`.
  `combGrowthRadius C ℓ n` is `γ(ρ(n))` as a real number, meaningful when both are finite.
* The proofs run through `GerasimovaOsinCombingSum` (the counting of Lemma 2.5) and
  `GerasimovaOsinCombingNorm` (the truncation limit of Proposition 2.4) with `γ` and `ρ`
  themselves as the growth bounds (`printedCombing`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (the analytic half of Gerasimova–Osin's
Theorem 1.1).  Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GerasimovaOsinCombing
open Filter Topology
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

/-! ## Definitions 2.1 and 2.2, and the growth functions (2)–(3) -/

/-- **Definition 2.1**, symmetric combings. -/
def IsSymmetricCombing (C : G → G → Set G) : Prop :=
  ∀ x y : G, C x y = C y x

/-- **Definition 2.1**, `G`-equivariant combings. -/
def IsEquivariantCombing (C : G → G → Set G) : Prop :=
  ∀ g x y : G, C (g * x) (g * y) = (fun z => g * z) '' C x y

/-- **Definition 2.2**, pseudolength functions `ℓ : G → [0,+∞)`. -/
structure IsPseudolength (ℓ : G → ℝ) : Prop where
  nonneg : ∀ g : G, 0 ≤ ℓ g
  symm : ∀ g : G, ℓ g⁻¹ = ℓ g
  triangle : ∀ g h : G, ℓ (g * h) ≤ ℓ g + ℓ h

/-- **Definition 2.2**, length functions. -/
def IsLengthFunction (ℓ : G → ℝ) : Prop :=
  IsPseudolength ℓ ∧ ∀ g : G, ℓ g = 0 ↔ g = 1

/-- `B(n) = {g ∈ G | ℓ(g) ≤ n}`. -/
def lenBall (ℓ : G → ℝ) (n : ℕ) : Set G :=
  {g | ℓ g ≤ n}

/-- **(2)**: `γ(n) = sup_{g ∈ G} |C(1,g) ∩ B(n)|`. -/
noncomputable def combGrowth (C : G → G → Set G) (ℓ : G → ℝ) (n : ℕ) : ℕ∞ :=
  ⨆ g : G, (C 1 g ∩ lenBall ℓ n).encard

/-- **(3)**: `ρ(n) = sup_{g ∈ B(n)} sup_{x ∈ C(1,g)} ℓ(x)`, in `ℕ ∪ {∞}`. -/
noncomputable def combRadius (C : G → G → Set G) (ℓ : G → ℝ) (n : ℕ) : ℕ∞ :=
  ⨆ (g : G) (_ : g ∈ lenBall ℓ n) (x : G) (_ : x ∈ C 1 g), ((⌈ℓ x⌉₊ : ℕ) : ℕ∞)

/-- `γ(ρ(n))` as a real number. -/
noncomputable def combGrowthRadius (C : G → G → Set G) (ℓ : G → ℝ) (n : ℕ) : ℝ :=
  ((combGrowth C ℓ (combRadius C ℓ n).toNat).toNat : ℝ)

theorem combGrowthRadius_nonneg (C : G → G → Set G) (ℓ : G → ℝ) (n : ℕ) :
    0 ≤ combGrowthRadius C ℓ n :=
  Nat.cast_nonneg _

/-! ## Lemma 2.3 -/

section Lemma23

variable (C : G → G → Set G) (ℓ : G → ℝ)

theorem encard_inter_le_combGrowth (n : ℕ) (g : G) :
    (C 1 g ∩ lenBall ℓ n).encard ≤ combGrowth C ℓ n :=
  le_iSup (fun g : G => (C 1 g ∩ lenBall ℓ n).encard) g

theorem ceil_le_combRadius {n : ℕ} {g x : G} (hg : g ∈ lenBall ℓ n) (hx : x ∈ C 1 g) :
    ((⌈ℓ x⌉₊ : ℕ) : ℕ∞) ≤ combRadius C ℓ n := by
  unfold combRadius
  exact le_iSup₂_of_le g hg (le_iSup₂_of_le x hx le_rfl)

/-- `C(1,g) ⊆ B(ρ(n))` for `g ∈ B(n)`, when `ρ` is finite. -/
theorem len_le_combRadius (hρ : ∀ n, combRadius C ℓ n ≠ ⊤) {n : ℕ} {g x : G}
    (hg : g ∈ lenBall ℓ n) (hx : x ∈ C 1 g) : ℓ x ≤ ((combRadius C ℓ n).toNat : ℝ) := by
  have h1 := ceil_le_combRadius C ℓ hg hx
  rw [← ENat.coe_toNat (hρ n), ENat.coe_le_coe] at h1
  calc ℓ x ≤ (⌈ℓ x⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((combRadius C ℓ n).toNat : ℝ) := by exact_mod_cast h1

/-- **Gerasimova–Osin, Lemma 2.3.** -/
theorem gerasimovaOsinLemma23 (_hγ : ∀ n, combGrowth C ℓ n ≠ ⊤)
    (hρ : ∀ n, combRadius C ℓ n ≠ ⊤) {n : ℕ} {s : G} (hs : s ∈ lenBall ℓ n) :
    (C 1 s).encard ≤ combGrowth C ℓ (combRadius C ℓ n).toNat := by
  have hsub : C 1 s ⊆ C 1 s ∩ lenBall ℓ (combRadius C ℓ n).toNat := fun x hx =>
    ⟨hx, len_le_combRadius C ℓ hρ hs hx⟩
  exact (Set.encard_le_encard hsub).trans (encard_inter_le_combGrowth C ℓ _ s)

/-- The combing data of `GerasimovaOsinCombingSum`, with `γ` and `ρ` as the growth bounds. -/
noncomputable def printedCombing (hℓ : IsPseudolength ℓ) (hsymm : IsSymmetricCombing C)
    (hequiv : IsEquivariantCombing C) (hγ : ∀ n, combGrowth C ℓ n ≠ ⊤)
    (hρ : ∀ n, combRadius C ℓ n ≠ ⊤) : Combing G where
  len := ℓ
  comb := C
  growth := fun n => (combGrowth C ℓ n).toNat
  radius := fun n => (combRadius C ℓ n).toNat
  comb_symm := hsymm
  comb_equivariant := hequiv
  len_inv := hℓ.symm
  len_mul := hℓ.triangle
  ball_finite := fun n g => Set.encard_ne_top_iff.mp
    (ne_top_of_le_ne_top (hγ n) (encard_inter_le_combGrowth C ℓ n g))
  ball_card := fun n g => by
    have hfin : (C 1 g ∩ lenBall ℓ n).Finite := Set.encard_ne_top_iff.mp
      (ne_top_of_le_ne_top (hγ n) (encard_inter_le_combGrowth C ℓ n g))
    have h := encard_inter_le_combGrowth C ℓ n g
    rw [← hfin.cast_ncard_eq, ← ENat.coe_toNat (hγ n), ENat.coe_le_coe] at h
    exact h
  comb_len := fun n g hg x hx => len_le_combRadius C ℓ hρ (n := n) (g := g) hg hx

end Lemma23

/-! ## Proposition 2.4 and Lemma 2.5 -/

section Proposition24

variable (C : G → G → Set G) (ℓ : G → ℝ) (S : Set G)

theorem sqrt_combGrowthRadius_pow_three (n : ℕ) :
    Real.sqrt (combGrowthRadius C ℓ n ^ 3) = combGrowthRadius C ℓ n ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (combGrowthRadius_nonneg C ℓ n)]
  norm_num

/-- **Gerasimova–Osin, Proposition 2.4**, the estimate (5). -/
theorem gerasimovaOsinProposition24 (hℓ : IsPseudolength ℓ) (hsymm : IsSymmetricCombing C)
    (hequiv : IsEquivariantCombing C)
    (h4 : ∀ s ∈ S, ∀ g : G, (C 1 s ∩ C s g ∩ C 1 g).Nonempty)
    (hγ : ∀ n, combGrowth C ℓ n ≠ ⊤) (hρ : ∀ n, combRadius C ℓ n ≠ ⊤)
    (n : ℕ) (T : Finset G) (c : G → ℂ) (hT : ∀ s ∈ T, s ∈ S ∩ lenBall ℓ n) :
    ‖translationSum T c‖
      ≤ combGrowthRadius C ℓ n ^ ((3 : ℝ) / 2) * reducedTwoNorm (translationSum T c) := by
  have h := norm_translationSum_le (printedCombing C ℓ hℓ hsymm hequiv hγ hρ) S h4 (n := n) T
    (fun s hs => (hT s hs).1) (fun s hs => (hT s hs).2) c
  rw [← sqrt_combGrowthRadius_pow_three]
  exact h

/-- **Gerasimova–Osin, Lemma 2.5**, the estimate (6). -/
theorem gerasimovaOsinLemma25 (hℓ : IsPseudolength ℓ) (hsymm : IsSymmetricCombing C)
    (hequiv : IsEquivariantCombing C)
    (h4 : ∀ s ∈ S, ∀ g : G, (C 1 s ∩ C s g ∩ C 1 g).Nonempty)
    (hγ : ∀ n, combGrowth C ℓ n ≠ ⊤) (hρ : ∀ n, combRadius C ℓ n ≠ ⊤)
    (n : ℕ) (T Y : Finset G) (α β : G → ℝ) (_hα : ∀ s, 0 ≤ α s) (_hβ : ∀ t, 0 ≤ β t)
    (hT : ∀ s ∈ T, s ∈ S ∩ lenBall ℓ n) :
    reducedTwoNorm (translationSum T (fun s => (α s : ℂ)) *
        translationSum Y (fun t => (β t : ℂ)))
      ≤ combGrowthRadius C ℓ n ^ ((3 : ℝ) / 2) *
          reducedTwoNorm (translationSum T (fun s => (α s : ℂ))) *
          reducedTwoNorm (translationSum Y (fun t => (β t : ℂ))) := by
  classical
  have hcoord : ∀ g : G,
      ((translationSum Y (fun t => (β t : ℂ)) : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) g
        = if g ∈ Y then (β g : ℂ) else 0 := by
    intro g
    rw [translationSum_apply]
    simp only [deltaOne_apply, inv_mul_eq_one, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  have hξY : ∀ t, t ∉ Y →
      ((translationSum Y (fun t => (β t : ℂ)) : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) t = 0 :=
    fun t ht => by rw [hcoord, if_neg ht]
  have hsq := norm_translationSum_apply_sq_le_of_support
    (printedCombing C ℓ hℓ hsymm hequiv hγ hρ) S h4 (n := n) T
    (fun s hs => (hT s hs).1) (fun s hs => (hT s hs).2) (fun s => (α s : ℂ)) _ Y hξY
  rw [← reducedTwoNorm_translationSum_sq T (fun s => (α s : ℂ))] at hsq
  have hbnorm : ‖((translationSum Y (fun t => (β t : ℂ)) : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖
        = reducedTwoNorm (translationSum Y (fun t => (β t : ℂ))) := rfl
  rw [hbnorm] at hsq
  have hK : (0 : ℝ) ≤ combGrowthRadius C ℓ n := combGrowthRadius_nonneg C ℓ n
  have hrhs : combGrowthRadius C ℓ n ^ 3 *
      reducedTwoNorm (translationSum T (fun s => (α s : ℂ))) ^ 2 *
        reducedTwoNorm (translationSum Y (fun t => (β t : ℂ))) ^ 2
      = (Real.sqrt (combGrowthRadius C ℓ n ^ 3) *
          reducedTwoNorm (translationSum T (fun s => (α s : ℂ))) *
          reducedTwoNorm (translationSum Y (fun t => (β t : ℂ)))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (pow_nonneg hK 3)]
  have hsq' : ‖((translationSum T (fun s => (α s : ℂ)) : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G)
        (((translationSum Y (fun t => (β t : ℂ)) : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))‖ ^ 2
      ≤ (Real.sqrt (combGrowthRadius C ℓ n ^ 3) *
          reducedTwoNorm (translationSum T (fun s => (α s : ℂ))) *
          reducedTwoNorm (translationSum Y (fun t => (β t : ℂ)))) ^ 2 := by
    rw [← hrhs]
    exact hsq
  have hab : reducedTwoNorm (translationSum T (fun s => (α s : ℂ)) *
        translationSum Y (fun t => (β t : ℂ)))
      = ‖((translationSum T (fun s => (α s : ℂ)) : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G)
        (((translationSum Y (fun t => (β t : ℂ)) : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))‖ := by
    rw [reducedTwoNorm, MulMemClass.coe_mul, mul_apply_eq_comp]
  rw [hab, ← sqrt_combGrowthRadius_pow_three]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (reducedTwoNorm_nonneg _))
      (reducedTwoNorm_nonneg _)) two_ne_zero).mp hsq'

/-- The exponent bookkeeping of the "in particular" clause. -/
theorem rpow_sq_inv_eq_pow {M : ℝ} (hM : 0 ≤ M) {k n₁ : ℕ} (_hk : 1 ≤ k) (hn : 1 ≤ n₁) :
    (M ^ 2) ^ ((k : ℝ)⁻¹) = (M ^ (((k * n₁ : ℕ) : ℝ)⁻¹)) ^ (2 * n₁) := by
  have e : ((2 : ℕ) : ℝ) * (k : ℝ)⁻¹ = (((k * n₁ : ℕ) : ℝ))⁻¹ * (((2 * n₁ : ℕ)) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_inv]
    have hn0 : (n₁ : ℝ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
    calc ((2 : ℕ) : ℝ) * (k : ℝ)⁻¹
        = ((2 : ℕ) : ℝ) * (k : ℝ)⁻¹ * ((n₁ : ℝ)⁻¹ * n₁) := by
          rw [inv_mul_cancel₀ hn0, mul_one]
      _ = (k : ℝ)⁻¹ * (n₁ : ℝ)⁻¹ * (((2 : ℕ) : ℝ) * n₁) := by ring
  rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM,
    ← Real.rpow_natCast (M ^ (((k * n₁ : ℕ) : ℝ)⁻¹)) (2 * n₁), ← Real.rpow_mul hM, e]

/-- **Gerasimova–Osin, Proposition 2.4**, "in particular": if `S` is a subsemigroup and
`γ(ρ(k))^{1/k} → 1`, then `r(a) = r₂(a)`. -/
theorem gerasimovaOsinProposition24_spectralRadius (S : Subsemigroup G)
    (hℓ : IsPseudolength ℓ) (hsymm : IsSymmetricCombing C) (hequiv : IsEquivariantCombing C)
    (h4 : ∀ s ∈ (S : Set G), ∀ g : G, (C 1 s ∩ C s g ∩ C 1 g).Nonempty)
    (hγ : ∀ n, combGrowth C ℓ n ≠ ⊤) (hρ : ∀ n, combRadius C ℓ n ≠ ⊤)
    (hlim : Tendsto (fun k : ℕ => combGrowthRadius C ℓ k ^ ((k : ℝ)⁻¹)) atTop (𝓝 1))
    (n : ℕ) (T : Finset G) (c : G → ℂ) (hT : ∀ s ∈ T, s ∈ (S : Set G) ∩ lenBall ℓ n) :
    HasL2SpectralRadiusProperty (translationSum T c) := by
  classical
  set n₁ : ℕ := max n 1 with hn₁
  have hn₁pos : 1 ≤ n₁ := le_max_right _ _
  have hnn₁ : (n : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast le_max_left n 1
  have hpow : ∀ k, 1 ≤ k → ∀ x ∈ T ^ k, x ∈ (S : Set G) ∧ ℓ x ≤ ((k * n₁ : ℕ) : ℝ) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro x hx
      rw [pow_one] at hx
      obtain ⟨hxS, hxB⟩ := hT x hx
      have hxB' : ℓ x ≤ (n : ℝ) := hxB
      refine ⟨hxS, ?_⟩
      rw [one_mul]
      exact le_trans hxB' hnn₁
    | succ k hk ih =>
      intro x hx
      rw [pow_succ] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
      obtain ⟨hyS, hyB⟩ := ih y hy
      obtain ⟨hzS, hzB⟩ := hT z hz
      have hzB' : ℓ z ≤ (n : ℝ) := hzB
      refine ⟨S.mul_mem hyS hzS, ?_⟩
      calc ℓ (y * z) ≤ ℓ y + ℓ z := hℓ.triangle y z
        _ ≤ ((k * n₁ : ℕ) : ℝ) + n₁ := add_le_add hyB (le_trans hzB' hnn₁)
        _ = (((k + 1) * n₁ : ℕ) : ℝ) := by push_cast; ring
  have hbound : ∀ k, ‖translationSum T c ^ k‖
      ≤ (max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 2 *
          reducedTwoNorm (translationSum T c ^ k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h1 : reducedTwoNorm (1 : ReducedGroupCStar G) = 1 := by
        unfold reducedTwoNorm
        rw [OneMemClass.coe_one, one_apply_eq_self, GroupVonNeumann.norm_deltaOne]
      rw [pow_zero, CStarRing.norm_one, h1, mul_one]
      have hM1 := le_max_right (combGrowthRadius C ℓ (0 * n₁)) 1
      nlinarith
    · obtain ⟨d, hd⟩ := exists_translationSum_pow T c k
      have hTk := hpow k hk
      have h := norm_translationSum_le (printedCombing C ℓ hℓ hsymm hequiv hγ hρ) (S : Set G) h4
        (n := k * n₁) (T ^ k) (fun x hx => (hTk x hx).1) (fun x hx => (hTk x hx).2) d
      rw [← hd] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (reducedTwoNorm_nonneg _))
      rw [Real.sqrt_le_left (by positivity)]
      have hK0 := combGrowthRadius_nonneg C ℓ (k * n₁)
      have hM : combGrowthRadius C ℓ (k * n₁) ≤ max (combGrowthRadius C ℓ (k * n₁)) 1 :=
        le_max_left _ _
      have hM1 : 1 ≤ max (combGrowthRadius C ℓ (k * n₁)) 1 := le_max_right _ _
      have h3 : combGrowthRadius C ℓ (k * n₁) ^ 3
          ≤ (max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 3 := pow_le_pow_left₀ hK0 hM 3
      have h4' : (0 : ℝ) ≤ (max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 3 := by positivity
      have hgoal : combGrowthRadius C ℓ (k * n₁) ^ 3
          ≤ ((max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 2) ^ 2 := by
        nlinarith
      exact hgoal
  have hmax : Tendsto (fun m : ℕ => (max (combGrowthRadius C ℓ m) 1) ^ ((m : ℝ)⁻¹)) atTop
      (𝓝 1) := by
    have h := hlim.max (tendsto_const_nhds (x := (1 : ℝ)))
    rw [max_self] at h
    refine h.congr fun m => ?_
    have hm0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
    rcases le_total (combGrowthRadius C ℓ m) 1 with hle | hle
    · rw [max_eq_right hle, Real.one_rpow,
        max_eq_right (Real.rpow_le_one (combGrowthRadius_nonneg C ℓ m) hle hm0)]
    · rw [max_eq_left hle, max_eq_left (Real.one_le_rpow hle hm0)]
  have hsub : Tendsto (fun k : ℕ => k * n₁) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha =>
      le_trans ha (by simpa using Nat.mul_le_mul_left a hn₁pos)⟩
  have hc1 : Tendsto (fun k : ℕ => ((max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 2) ^ ((k : ℝ)⁻¹))
      atTop (𝓝 1) := by
    have h := (hmax.comp hsub).pow (2 * n₁)
    rw [one_pow] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact (rpow_sq_inv_eq_pow (le_trans zero_le_one (le_max_right _ _)) hk hn₁pos).symm
  rw [hasL2SpectralRadiusProperty_iff]
  exact limsup_rpow_le_of_le_mul (u := fun k => ‖translationSum T c ^ k‖)
    (v := fun k => reducedTwoNorm (translationSum T c ^ k))
    (c := fun k => (max (combGrowthRadius C ℓ (k * n₁)) 1) ^ 2)
    (fun k => norm_nonneg _) (fun k => reducedTwoNorm_nonneg _) (fun k => by positivity)
    hbound hc1
    (isCoboundedUnder_le_of_le atTop fun k => Real.rpow_nonneg (norm_nonneg _) _)
    ((isBoundedUnder_operatorSpectralRadius (translationSum T c)).mono_le
      (Eventually.of_forall fun k => reducedTwoNorm_pow_rpow_le (translationSum T c) k))

end Proposition24

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms gerasimovaOsinLemma23
#audit_axioms gerasimovaOsinProposition24
#audit_axioms gerasimovaOsinLemma25
#audit_axioms gerasimovaOsinProposition24_spectralRadius
