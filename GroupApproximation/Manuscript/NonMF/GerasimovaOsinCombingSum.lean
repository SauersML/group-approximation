import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Gerasimova–Osin, Lemma 2.5: the combinatorial estimate behind the combing norm bound

Gerasimova–Osin (arXiv:1910.14524v3), §2.  A *generalized combing* of a group `G` is a
map `C : G × G → 𝒫(G)`; it is symmetric if `C(x,y) = C(y,x)` and `G`-equivariant if
`C(gx,gy) = gC(x,y)`.  With a pseudolength `ℓ`, `B(n) = {g | ℓ(g) ≤ n}` and the growth
functions (2), (3):

    γ(n) = sup_g |C(1,g) ∩ B(n)|,     ρ(n) = sup_{g ∈ B(n)} sup_{x ∈ C(1,g)} ℓ(x).

> **Lemma 2.5.** Under the assumptions of Proposition 2.4 [a subset `S ⊆ G` with
> `C(1,s) ∩ C(s,g) ∩ C(1,g) ≠ ∅` for all `s ∈ S`, `g ∈ G`, and finite growth], suppose
> additionally that `a ∈ ℝ₊G`.  Then for every `b ∈ ℝ₊G`, `‖ab‖₂ ≤ γ(ρ(n))^{3/2}‖a‖₂‖b‖₂`.

`sum_sq_conv_le` is that inequality squared, for `a` supported in a finite `T ⊆ S ∩ B(n)`
and `b` supported in a finite `Y`, with `growth` and `radius` upper bounds for `γ` and `ρ`.

## The argument

It follows Gerasimova–Osin with one simplification: instead of covering `supp(a)` by
the sets `S_{g,x}`, a point `σ_g(s) ∈ C(1,s) ∩ C(s,g) ∩ C(1,g)` is chosen for each `s`, which
partitions `supp(a)` by the value of `σ_g`.

1. For fixed `g`, the values `σ_g(s)` lie in `X_g = C(1,g) ∩ B(ρ(n))`, of size at most
   `γ(ρ(n))`.  Grouping by `x = σ_g(s)`, Cauchy–Schwarz twice gives
   `(∑_s α_s β_{s⁻¹g})² ≤ γ(ρ(n)) ∑_{s'} A(σ_g s') β_{s'⁻¹g}²`, with
   `A(x) = ∑_{s : x ∈ C(1,s)} α_s²`.
2. Substituting `g = s't`, the total is `∑_s α_s² ∑_t β_t² · #{s' : σ_{s't}(s') ∈ C(1,s)}`.
3. The count is at most `γ(ρ(n))²`: `s' ↦ (x, s'⁻¹x)` with `x = σ_{s't}(s')` is injective,
   `x ∈ C(1,s) ∩ B(ρ(n))`, and `s'⁻¹x ∈ C(1,t) ∩ B(ρ(n))` by symmetry and equivariance
   (their `C_{s,t} ≤ γ(ρ(n))²`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 2.4).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GerasimovaOsinCombing

open Classical
open scoped Pointwise

/-- **A symmetric `G`-equivariant generalized combing** with a pseudolength and upper
bounds `growth` for `γ` and `radius` for `ρ` (Gerasimova–Osin, Definitions 2.1–2.2, (2), (3)). -/
structure Combing (G : Type*) [Group G] where
  /-- The pseudolength `ℓ`. -/
  len : G → ℝ
  /-- The generalized combing `C`. -/
  comb : G → G → Set G
  /-- An upper bound for `γ`. -/
  growth : ℕ → ℕ
  /-- An upper bound for `ρ`. -/
  radius : ℕ → ℕ
  comb_symm : ∀ x y : G, comb x y = comb y x
  comb_equivariant : ∀ g x y : G, comb (g * x) (g * y) = (fun z => g * z) '' comb x y
  len_inv : ∀ g : G, len g⁻¹ = len g
  len_mul : ∀ g h : G, len (g * h) ≤ len g + len h
  ball_finite : ∀ (n : ℕ) (g : G), (comb 1 g ∩ {x | len x ≤ n}).Finite
  ball_card : ∀ (n : ℕ) (g : G), (comb 1 g ∩ {x | len x ≤ n}).ncard ≤ growth n
  comb_len : ∀ (n : ℕ) (g : G), len g ≤ n → ∀ x ∈ comb 1 g, len x ≤ radius n

variable {G : Type*} [Group G]

namespace Combing

variable (D : Combing G)

/-- `x ∈ C(s, s·t)` gives `s⁻¹x ∈ C(1, t)`. -/
theorem inv_mul_mem_comb_of_mem {s t x : G} (hx : x ∈ D.comb s (s * t)) :
    s⁻¹ * x ∈ D.comb 1 t := by
  have h := D.comb_equivariant s 1 t
  rw [mul_one] at h
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [inv_mul_cancel_left]

/-- `x ∈ C(1, s)` gives `s⁻¹x ∈ C(1, s⁻¹)`. -/
theorem inv_mul_mem_comb_inv_of_mem {s x : G} (hx : x ∈ D.comb 1 s) :
    s⁻¹ * x ∈ D.comb 1 s⁻¹ := by
  have h := D.comb_equivariant s⁻¹ 1 s
  rw [mul_one, inv_mul_cancel, D.comb_symm] at h
  rw [h]
  exact ⟨x, hx, rfl⟩

/-- The finite set `C(1,g) ∩ B(m)`. -/
noncomputable def ball (m : ℕ) (g : G) : Finset G :=
  (D.ball_finite m g).toFinset

theorem mem_ball {m : ℕ} {g x : G} : x ∈ D.ball m g ↔ x ∈ D.comb 1 g ∧ D.len x ≤ m := by
  rw [ball, Set.Finite.mem_toFinset]
  rfl

theorem card_ball_le (m : ℕ) (g : G) : (D.ball m g).card ≤ D.growth m := by
  rw [ball, ← Set.ncard_eq_toFinset_card _ (D.ball_finite m g)]
  exact D.ball_card m g

end Combing

variable (D : Combing G) (S : Set G)
  (htri : ∀ s ∈ S, ∀ g : G, (D.comb 1 s ∩ D.comb s g ∩ D.comb 1 g).Nonempty)

/-- The chosen point `σ_g(s) ∈ C(1,s) ∩ C(s,g) ∩ C(1,g)`. -/
noncomputable def sigma (g s : G) : G :=
  if h : s ∈ S then (htri s h g).some else 1

theorem sigma_mem {g s : G} (hs : s ∈ S) :
    sigma D S htri g s ∈ D.comb 1 s ∩ D.comb s g ∩ D.comb 1 g := by
  rw [sigma, dif_pos hs]
  exact (htri s hs g).some_mem

/-- **Step 3: the multiplicity bound `C_{s,t} ≤ γ(ρ(n))²`.** -/
theorem card_filter_sigma_le {n : ℕ} (T : Finset G) (hTS : ∀ s ∈ T, s ∈ S)
    (hTn : ∀ s ∈ T, D.len s ≤ n) (s t : G) :
    (T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s).card
      ≤ D.growth (D.radius n) * D.growth (D.radius n) := by
  set m := D.radius n
  let f : G → G × G := fun s' =>
    (sigma D S htri (s' * t) s', s'⁻¹ * sigma D S htri (s' * t) s')
  have hmaps : Set.MapsTo f
      ((T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s : Finset G) : Set G)
      ((D.ball m s ×ˢ D.ball m t : Finset (G × G)) : Set (G × G)) := by
    intro s' hs'
    rw [Finset.mem_coe, Finset.mem_filter] at hs'
    obtain ⟨hs'T, hcond⟩ := hs'
    obtain ⟨⟨h1, h2⟩, -⟩ := sigma_mem D S htri (g := s' * t) (hTS s' hs'T)
    have hlen : D.len (sigma D S htri (s' * t) s') ≤ m :=
      D.comb_len n s' (hTn s' hs'T) _ h1
    rw [Finset.mem_coe, Finset.mem_product, D.mem_ball, D.mem_ball]
    refine ⟨⟨hcond, hlen⟩, D.inv_mul_mem_comb_of_mem h2, ?_⟩
    have hinv := D.inv_mul_mem_comb_inv_of_mem h1
    exact D.comb_len n s'⁻¹ (by rw [D.len_inv]; exact hTn s' hs'T) _ hinv
  have hinj : Set.InjOn f
      ((T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s : Finset G) : Set G) := by
    intro a _ b _ hab
    have h1 : sigma D S htri (a * t) a = sigma D S htri (b * t) b := congrArg Prod.fst hab
    have h2 : a⁻¹ * sigma D S htri (a * t) a = b⁻¹ * sigma D S htri (b * t) b :=
      congrArg Prod.snd hab
    rw [h1] at h2
    exact inv_injective (mul_right_cancel h2)
  calc (T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s).card
      ≤ (D.ball m s ×ˢ D.ball m t).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = (D.ball m s).card * (D.ball m t).card := Finset.card_product _ _
    _ ≤ D.growth m * D.growth m := Nat.mul_le_mul (D.card_ball_le m s) (D.card_ball_le m t)

/-- The weight `A_g(s') = ∑_{s ∈ T, σ_g(s') ∈ C(1,s)} α_s²`. -/
noncomputable def weight (T : Finset G) (α : G → ℝ) (g s' : G) : ℝ :=
  ∑ s ∈ T.filter fun s => sigma D S htri g s' ∈ D.comb 1 s, α s ^ 2

/-- **Step 1, at one point `g`.** -/
theorem sq_sum_le_growth_mul {n : ℕ} (T : Finset G) (hTS : ∀ s ∈ T, s ∈ S)
    (hTn : ∀ s ∈ T, D.len s ≤ n) (α β : G → ℝ) (_hα : ∀ s, 0 ≤ α s) (g : G) :
    (∑ s ∈ T, α s * β (s⁻¹ * g)) ^ 2
      ≤ (D.growth (D.radius n) : ℝ) *
          ∑ s' ∈ T, weight D S htri T α g s' * β (s'⁻¹ * g) ^ 2 := by
  set m := D.radius n
  set X := D.ball m g
  have hmaps : ∀ s ∈ T, sigma D S htri g s ∈ X := by
    intro s hs
    obtain ⟨⟨h1, -⟩, h3⟩ := sigma_mem D S htri (g := g) (hTS s hs)
    exact D.mem_ball.mpr ⟨h3, D.comb_len n s (hTn s hs) _ h1⟩
  have hsplit : ∑ s ∈ T, α s * β (s⁻¹ * g)
      = ∑ x ∈ X, ∑ s ∈ T.filter (fun s => sigma D S htri g s = x), α s * β (s⁻¹ * g) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hcs1 : (∑ x ∈ X, ∑ s ∈ T.filter (fun s => sigma D S htri g s = x),
        α s * β (s⁻¹ * g)) ^ 2
      ≤ (D.growth m : ℝ) * ∑ x ∈ X, (∑ s ∈ T.filter (fun s => sigma D S htri g s = x),
        α s * β (s⁻¹ * g)) ^ 2 := by
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast D.card_ball_le m g)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hcs2 : ∀ x ∈ X, (∑ s ∈ T.filter (fun s => sigma D S htri g s = x),
        α s * β (s⁻¹ * g)) ^ 2
      ≤ (∑ s ∈ T.filter (fun s => x ∈ D.comb 1 s), α s ^ 2) *
          ∑ s ∈ T.filter (fun s => sigma D S htri g s = x), β (s⁻¹ * g) ^ 2 := by
    intro x _
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hsT, hsx⟩ := hs
    refine ⟨hsT, ?_⟩
    rw [← hsx]
    exact (sigma_mem D S htri (g := g) (hTS s hsT)).1.1
  have hcollapse : ∑ x ∈ X, (∑ s ∈ T.filter (fun s => x ∈ D.comb 1 s), α s ^ 2) *
        ∑ s ∈ T.filter (fun s => sigma D S htri g s = x), β (s⁻¹ * g) ^ 2
      = ∑ s' ∈ T, weight D S htri T α g s' * β (s'⁻¹ * g) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    rw [← (Finset.mem_filter.mp hs').2, weight]
  rw [hsplit]
  calc _ ≤ _ := hcs1
    _ ≤ (D.growth m : ℝ) * ∑ x ∈ X, (∑ s ∈ T.filter (fun s => x ∈ D.comb 1 s), α s ^ 2) *
          ∑ s ∈ T.filter (fun s => sigma D S htri g s = x), β (s⁻¹ * g) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcs2) (Nat.cast_nonneg _)
    _ = _ := by rw [hcollapse]

include htri in
/-- **Gerasimova–Osin, Lemma 2.5**, squared, for finitely supported nonnegative
coefficients. -/
theorem sum_sq_conv_le {n : ℕ} (T : Finset G) (hTS : ∀ s ∈ T, s ∈ S)
    (hTn : ∀ s ∈ T, D.len s ≤ n) (Y : Finset G) (α β : G → ℝ) (hα : ∀ s, 0 ≤ α s)
    (hβY : ∀ t, t ∉ Y → β t = 0) :
    ∑ g ∈ T * Y, (∑ s ∈ T, α s * β (s⁻¹ * g)) ^ 2
      ≤ (D.growth (D.radius n) : ℝ) ^ 3 * (∑ s ∈ T, α s ^ 2) * ∑ t ∈ Y, β t ^ 2 := by
  set K : ℝ := (D.growth (D.radius n) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  -- Step 1, summed over `g`
  have h1 : ∑ g ∈ T * Y, (∑ s ∈ T, α s * β (s⁻¹ * g)) ^ 2
      ≤ K * ∑ g ∈ T * Y, ∑ s' ∈ T, weight D S htri T α g s' * β (s'⁻¹ * g) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun g _ => sq_sum_le_growth_mul D S htri T hTS hTn α β hα g
  -- Step 2: substitute `g = s' t`
  have h2 : ∑ g ∈ T * Y, ∑ s' ∈ T, weight D S htri T α g s' * β (s'⁻¹ * g) ^ 2
      = ∑ s' ∈ T, ∑ t ∈ Y, weight D S htri T α (s' * t) s' * β t ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have himage : Y.image (fun t => s' * t) ⊆ T * Y := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mul_mem_mul hs' ht
    rw [← Finset.sum_subset himage ?_,
      Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [inv_mul_cancel_left]
    · intro g _ hg
      have ht : s'⁻¹ * g ∉ Y := by
        intro hmem
        apply hg
        exact Finset.mem_image.mpr ⟨s'⁻¹ * g, hmem, mul_inv_cancel_left s' g⟩
      rw [hβY _ ht]
      simp
  -- Step 3: exchange and count
  have h3 : ∑ s' ∈ T, ∑ t ∈ Y, weight D S htri T α (s' * t) s' * β t ^ 2
      ≤ K * K * ((∑ s ∈ T, α s ^ 2) * ∑ t ∈ Y, β t ^ 2) := by
    have hexpand : ∑ s' ∈ T, ∑ t ∈ Y, weight D S htri T α (s' * t) s' * β t ^ 2
        = ∑ s ∈ T, ∑ t ∈ Y, α s ^ 2 * β t ^ 2 *
            ((T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s).card : ℝ) := by
      simp only [weight, Finset.sum_filter, Finset.sum_mul, Finset.card_filter, Nat.cast_sum,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext t; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
        Finset.sum_congr rfl fun s' _ => ?_
      split_ifs <;> simp
    rw [hexpand, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    have hcount := card_filter_sigma_le D S htri T hTS hTn s t
    have hcount' : ((T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s).card : ℝ)
        ≤ K * K := by rw [hK]; exact_mod_cast hcount
    have hnn : 0 ≤ α s ^ 2 * β t ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc α s ^ 2 * β t ^ 2 *
          ((T.filter fun s' => sigma D S htri (s' * t) s' ∈ D.comb 1 s).card : ℝ)
        ≤ α s ^ 2 * β t ^ 2 * (K * K) := mul_le_mul_of_nonneg_left hcount' hnn
      _ = K * K * (α s ^ 2 * β t ^ 2) := by ring
  calc ∑ g ∈ T * Y, (∑ s ∈ T, α s * β (s⁻¹ * g)) ^ 2
      ≤ K * ∑ g ∈ T * Y, ∑ s' ∈ T, weight D S htri T α g s' * β (s'⁻¹ * g) ^ 2 := h1
    _ = K * ∑ s' ∈ T, ∑ t ∈ Y, weight D S htri T α (s' * t) s' * β t ^ 2 := by rw [h2]
    _ ≤ K * (K * K * ((∑ s ∈ T, α s ^ 2) * ∑ t ∈ Y, β t ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hK0
    _ = K ^ 3 * (∑ s ∈ T, α s ^ 2) * ∑ t ∈ Y, β t ^ 2 := by ring

end GerasimovaOsinCombing
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.GerasimovaOsinCombing.card_filter_sigma_le
#audit_axioms GroupApproximation.GerasimovaOsinCombing.sq_sum_le_growth_mul
#audit_axioms GroupApproximation.GerasimovaOsinCombing.sum_sq_conv_le
