import GroupApproximation.Leavitt.ExchangePrerequisite

/-!
# Finite one-sided exchange refinement

`ExchangePrerequisite.lean` proves the one-element right exchange property
`ExchangePrerequisite.HasRightExchange` for the binary Leavitt algebra and names the
remaining step in its module docstring: promoting the two-term witness to a
simultaneous orthogonal refinement of an arbitrary finite decomposition of `1`.
This file carries out that step, and therefore discharges
`ExchangePrerequisite.HasFiniteRightExchangePartitions` for `L_k(1,2)`.

## The obstruction and how it is removed

The naive induction passes to the corner ring `w R w` cut out by the complementary
idempotent produced at the first step.  Inside that corner one obtains idempotents
`g i` lying in `w * x i * R`, *not* in `x i * R`: the stray left factor `w` is exactly
the orientation defect that makes the two-sided partition
`ExchangePrerequisite.exists_finite_twoSidedIdeal_partition` useless for this purpose.

The defect is removed without any unit or conjugation machinery.  Writing
`g i = w * x i * q i` and `h i = x i * q i * g i`, the identity `g i * w = g i` gives
`g i * (x j * q j) = g i * g j`, whence the `h i` are idempotent, pairwise orthogonal,
and genuinely lie in `x i * R`.  They satisfy `w * h i = g i` and `f * h i = h i`, so
with `H = ∑ i, h i` one has `w * H = w` and `f * H = H`; replacing the head idempotent
`u` by `u - u * H` then repairs orthogonality and the sum at once, and `u - u * H`
still lies in `x 0 * R` because it equals `u * (1 - H)`.

## Main results

* `ExchangePrerequisite.exists_corner_split` — the corner form of the one-element
  exchange property.
* `ExchangePrerequisite.exists_corner_partition` — the induction on the number of
  summands, stated relative to an arbitrary idempotent `f` so that it can be applied
  inside a corner without ever leaving the ambient ring.
* `ExchangePrerequisite.hasFiniteRightExchangePartitions_of_hasRightExchange` — the
  target implication.
* `ExchangePrerequisite.exists_orthogonal_refinement` — the same statement re-indexed
  along an arbitrary `Fintype`.
* `BinaryLeavitt.hasFiniteRightExchangePartitions` — the specialization to `L_k(1,2)`.

No hypothesis beyond `HasRightExchange R` is used: the results below hold for an
arbitrary unital associative ring with that property, with no nontriviality,
commutativity or finiteness assumption.  In particular the degenerate case `n = 0`
is honest, since `∑ i : Fin 0, x i = 1` forces `f = 0` in the relative statement.

This is the classical passage from two-term to finite exchange (Nicholson, Warfield);
the argument is reproduced here in elementary element-wise form because mathlib has no
exchange-ring API.
-/

namespace GroupApproximation

namespace ExchangePrerequisite

variable {R : Type*} [Ring R]

/-! ### Orthogonal families -/

/-- In a family of orthogonal idempotents summing to `W`, each member is fixed by `W`
on the left. -/
theorem mul_left_of_orthogonalFamily {n : ℕ} {g : Fin n → R} {W : R}
    (hidem : ∀ i, IsIdempotentElem (g i)) (horth : ∀ i j, i ≠ j → g i * g j = 0)
    (hsum : (∑ i, g i) = W) (i : Fin n) : W * g i = g i := by
  have hpick : (∑ j, g j * g i) = g i * g i :=
    Finset.sum_eq_single_of_mem (f := fun j => g j * g i) i (Finset.mem_univ i)
      (fun b _ hb => horth b i hb)
  rw [← hsum, Finset.sum_mul, hpick]
  exact hidem i

/-- In a family of orthogonal idempotents summing to `W`, each member is fixed by `W`
on the right. -/
theorem mul_right_of_orthogonalFamily {n : ℕ} {g : Fin n → R} {W : R}
    (hidem : ∀ i, IsIdempotentElem (g i)) (horth : ∀ i j, i ≠ j → g i * g j = 0)
    (hsum : (∑ i, g i) = W) (i : Fin n) : g i * W = g i := by
  have hpick : (∑ j, g i * g j) = g i * g i :=
    Finset.sum_eq_single_of_mem (f := fun j => g i * g j) i (Finset.mem_univ i)
      (fun b _ hb => horth i b hb.symm)
  rw [← hsum, Finset.mul_sum, hpick]
  exact hidem i

/-! ### The corner form of the one-element exchange property -/

/-- The corner form of the one-element right exchange property.  If `f` is an
idempotent and `a + y = f` with `a` and `y` fixed by `f` on the left, then `f` splits
as a sum of two orthogonal idempotents, one a right multiple of `a` and the other a
right multiple of `y`.

The proof applies the ambient exchange property at `a + 1 - f`, whose complement is
`y`; the resulting idempotent is then compressed into the corner by `e ↦ f * e * f`.
Only the left-hand corner conditions `f * a = a` and `f * y = y` are needed. -/
theorem exists_corner_split (hex : HasRightExchange R) {f a y : R}
    (hf : IsIdempotentElem f) (hfa : f * a = a) (hfy : f * y = y) (hay : a + y = f) :
    ∃ u w r s : R,
      IsIdempotentElem u ∧ IsIdempotentElem w ∧
      u + w = f ∧ u * w = 0 ∧ w * u = 0 ∧
      u = a * r ∧ w = y * s := by
  have hff : f * f = f := hf
  obtain ⟨e, r, s, he, her, hcomp⟩ := hex (a + 1 - f)
  have hee : e * e = e := he
  have hone : (1 : R) - (a + 1 - f) = y := by
    rw [← hay]; abel
  rw [hone] at hcomp
  -- `f` fixes the complementary idempotent `1 - e` on the left.
  have hfe1 : f * (1 - e) = 1 - e := by
    rw [hcomp, ← mul_assoc, hfy]
  -- Consequently `e * f` already lies in the corner.
  have hfef : f * e * f = e * f := by
    have hL : f * ((1 : R) - e) * f = f - f * e * f := by
      rw [mul_sub, mul_one, sub_mul, hff]
    have hR : ((1 : R) - e) * f = f - e * f := by
      rw [sub_mul, one_mul]
    have hkey : f - f * e * f = f - e * f := by
      rw [← hL, hfe1, hR]
    calc f * e * f = f - (f - f * e * f) := by abel
      _ = f - (f - e * f) := by rw [hkey]
      _ = e * f := by abel
  have hfz : f * (a + 1 - f) = a := by
    rw [mul_sub, mul_add, mul_one, hfa, hff]
    abel
  have hfe : f * e = a * r := by
    rw [her, ← mul_assoc, hfz]
  refine ⟨e * f, (1 - e) * f, r * f, s * f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show e * f * (e * f) = e * f
    calc e * f * (e * f) = e * (f * e * f) := by simp only [mul_assoc]
      _ = e * (e * f) := by rw [hfef]
      _ = e * e * f := (mul_assoc _ _ _).symm
      _ = e * f := by rw [hee]
  · have h1e : (1 - e) * (1 - e) = 1 - e := one_sub_isIdempotent he
    show (1 - e) * f * ((1 - e) * f) = (1 - e) * f
    calc (1 - e) * f * ((1 - e) * f) = (1 - e) * (f * (1 - e)) * f := by simp only [mul_assoc]
      _ = (1 - e) * (1 - e) * f := by rw [hfe1]
      _ = (1 - e) * f := by rw [h1e]
  · noncomm_ring
  · calc e * f * ((1 - e) * f) = e * (f * (1 - e)) * f := by simp only [mul_assoc]
      _ = e * (1 - e) * f := by rw [hfe1]
      _ = 0 := by rw [mul_one_sub_eq_zero he, zero_mul]
  · calc (1 - e) * f * (e * f) = (1 - e) * (f * e * f) := by simp only [mul_assoc]
      _ = (1 - e) * (e * f) := by rw [hfef]
      _ = (1 - e) * e * f := (mul_assoc _ _ _).symm
      _ = 0 := by rw [one_sub_mul_eq_zero he, zero_mul]
  · rw [← hfef, hfe, mul_assoc]
  · rw [hcomp, mul_assoc]

/-! ### The finite refinement -/

/-- The finite orthogonal right-ideal refinement, stated relative to an idempotent `f`.

Given an idempotent `f` and a finite family `x` of elements fixed by `f` on the left
and summing to `f`, there are orthogonal idempotents `e i ∈ x i * R` summing to `f`.
The relative form is what makes the induction go through: the inductive step applies
the statement again inside the corner cut out by the complementary idempotent, and the
relative form lets that happen without introducing a corner ring as a type. -/
theorem exists_corner_partition (hex : HasRightExchange R) :
    ∀ (n : ℕ) (f : R), IsIdempotentElem f → ∀ x : Fin n → R,
      (∀ i, f * x i = x i) → (∑ i, x i) = f →
      ∃ e c : Fin n → R,
        (∀ i, IsIdempotentElem (e i)) ∧
        (∀ i j, i ≠ j → e i * e j = 0) ∧
        (∀ i, e i = x i * c i) ∧
        (∑ i, e i) = f := by
  intro n
  induction n with
  | zero =>
    intro f _ x _ hsum
    rw [Fin.sum_univ_zero] at hsum
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_⟩
    rw [Fin.sum_univ_zero]
    exact hsum
  | succ n ih =>
    intro f hf x hfx hsum
    have hay : x 0 + (∑ i : Fin n, x i.succ) = f := by
      rw [← Fin.sum_univ_succ]
      exact hsum
    have hfy : f * (∑ i : Fin n, x i.succ) = ∑ i : Fin n, x i.succ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hfx i.succ
    obtain ⟨u, w, r, s, hu, hw, huw_sum, _huw, hwu, hur, hws⟩ :=
      exists_corner_split hex hf (hfx 0) hfy hay
    have hww : w * w = w := hw
    -- The tail, compressed into the corner cut out by `w`.
    have hwx : ∀ i : Fin n, w * (w * x i.succ * s * w) = w * x i.succ * s * w := by
      intro i
      calc w * (w * x i.succ * s * w) = w * w * x i.succ * s * w := by simp only [mul_assoc]
        _ = w * x i.succ * s * w := by rw [hww]
    have hzsum : (∑ i : Fin n, w * x i.succ * s * w) = w := by
      have h1 : (∑ i : Fin n, w * x i.succ * s * w)
          = w * (∑ i : Fin n, x i.succ) * s * w := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      rw [h1, mul_assoc w, ← hws, hww]
      exact hww
    obtain ⟨g, c, hg_idem, hg_orth, hg_eq, hg_sum⟩ :=
      ih w hw (fun i => w * x i.succ * s * w) hwx hzsum
    -- Repackage the corner witnesses so that the stray left factor `w` is visible.
    obtain ⟨q, hq⟩ : ∃ q : Fin n → R, ∀ i, g i = w * x i.succ * q i :=
      ⟨fun i => s * w * c i, fun i => by
        show g i = w * x i.succ * (s * w * c i)
        have hgi : g i = w * x i.succ * s * w * c i := hg_eq i
        rw [hgi]
        simp only [mul_assoc]⟩
    have hgw : ∀ i, g i * w = g i :=
      mul_right_of_orthogonalFamily hg_idem hg_orth hg_sum
    have hgu : ∀ i, g i * u = 0 := by
      intro i
      calc g i * u = g i * w * u := by rw [hgw i]
        _ = g i * (w * u) := mul_assoc _ _ _
        _ = 0 := by rw [hwu, mul_zero]
    have hgg : ∀ i j, g i * (x j.succ * q j) = g i * g j := by
      intro i j
      calc g i * (x j.succ * q j) = g i * w * (x j.succ * q j) := by rw [hgw i]
        _ = g i * (w * x j.succ * q j) := by simp only [mul_assoc]
        _ = g i * g j := by rw [← hq j]
    -- The corrected family, genuinely inside the principal right ideals.
    obtain ⟨h, hh⟩ : ∃ h : Fin n → R, ∀ i, h i = x i.succ * q i * g i :=
      ⟨fun i => x i.succ * q i * g i, fun _ => rfl⟩
    have hmul : ∀ i j, h i * h j = x i.succ * q i * (g i * g j) * g j := by
      intro i j
      have hstep : h i * h j = x i.succ * q i * (g i * (x j.succ * q j)) * g j := by
        rw [hh i, hh j]
        simp only [mul_assoc]
      rw [hstep, hgg i j]
    have hh_idem : ∀ i, IsIdempotentElem (h i) := by
      intro i
      have hgi : g i * g i = g i := hg_idem i
      show h i * h i = h i
      calc h i * h i = x i.succ * q i * (g i * g i) * g i := hmul i i
        _ = x i.succ * q i * (g i * (g i * g i)) := by simp only [mul_assoc]
        _ = x i.succ * q i * g i := by rw [hgi, hgi]
        _ = h i := (hh i).symm
    have hh_orth : ∀ i j, i ≠ j → h i * h j = 0 := by
      intro i j hij
      rw [hmul i j, hg_orth i j hij]
      simp
    have hwh : ∀ i, w * h i = g i := by
      intro i
      calc w * h i = w * x i.succ * q i * g i := by rw [hh i]; simp only [mul_assoc]
        _ = g i * g i := by rw [← hq i]
        _ = g i := hg_idem i
    have hfh : ∀ i, f * h i = h i := by
      intro i
      calc f * h i = f * x i.succ * q i * g i := by rw [hh i]; simp only [mul_assoc]
        _ = x i.succ * q i * g i := by rw [hfx i.succ]
        _ = h i := (hh i).symm
    have hhu : ∀ i, h i * u = 0 := by
      intro i
      calc h i * u = x i.succ * q i * (g i * u) := by rw [hh i]; simp only [mul_assoc]
        _ = 0 := by rw [hgu i, mul_zero]
    obtain ⟨H, hH⟩ : ∃ H : R, H = ∑ i, h i := ⟨_, rfl⟩
    have hHh : ∀ i, H * h i = h i :=
      mul_left_of_orthogonalFamily hh_idem hh_orth hH.symm
    have hwH : w * H = w := by
      have h1 : (∑ i, w * h i) = ∑ i, g i := Finset.sum_congr rfl fun i _ => hwh i
      rw [hH, Finset.mul_sum, h1, hg_sum]
    have hfH : f * H = H := by
      have h1 : (∑ i, f * h i) = ∑ i, h i := Finset.sum_congr rfl fun i _ => hfh i
      rw [hH, Finset.mul_sum, h1]
    have hHu : H * u = 0 := by
      rw [hH, Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => hhu i
    have hfu_sub : f - u = w := by
      rw [← huw_sum]; abel
    have hH_sub : H - u * H = w := by
      calc H - u * H = f * H - u * H := by rw [hfH]
        _ = (f - u) * H := by rw [sub_mul]
        _ = w * H := by rw [hfu_sub]
        _ = w := hwH
    -- The repaired head idempotent.
    have he0_idem : IsIdempotentElem (u - u * H) := by
      have huu : u * u = u := hu
      have h1 : u * H * u = 0 := by rw [mul_assoc, hHu, mul_zero]
      have h2 : u * H * (u * H) = 0 := by
        calc u * H * (u * H) = u * H * u * H := by simp only [mul_assoc]
          _ = 0 := by rw [h1, zero_mul]
      have hexp : (u - u * H) * (u - u * H)
          = u * u - u * u * H - u * H * u + u * H * (u * H) := by noncomm_ring
      show (u - u * H) * (u - u * H) = u - u * H
      rw [hexp, huu, h1, h2]
      abel
    have he0_eq : u - u * H = x 0 * (r * (1 - H)) := by
      rw [hur]; noncomm_ring
    have he0h : ∀ i, (u - u * H) * h i = 0 := by
      intro i
      calc (u - u * H) * h i = u * h i - u * (H * h i) := by noncomm_ring
        _ = u * h i - u * h i := by rw [hHh i]
        _ = 0 := sub_self _
    have hhe0 : ∀ i, h i * (u - u * H) = 0 := by
      intro i
      calc h i * (u - u * H) = h i * u - h i * u * H := by noncomm_ring
        _ = 0 := by rw [hhu i]; simp
    refine ⟨Fin.cons (u - u * H) h, Fin.cons (r * (1 - H)) (fun i => q i * g i),
      ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact he0_idem
      | succ j =>
        simp only [Fin.cons_succ]
        exact hh_idem j
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro j
        induction j using Fin.cases with
        | zero =>
          intro hij
          exact absurd rfl hij
        | succ l =>
          intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact he0h l
      | succ k =>
        intro j
        induction j using Fin.cases with
        | zero =>
          intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact hhe0 k
        | succ l =>
          intro hij
          simp only [Fin.cons_succ]
          exact hh_orth k l (fun hkl => hij (by rw [hkl]))
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact he0_eq
      | succ j =>
        simp only [Fin.cons_succ]
        rw [hh j]
        exact mul_assoc _ _ _
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hH]
      calc u - u * H + H = u + (H - u * H) := by abel
        _ = u + w := by rw [hH_sub]
        _ = f := huw_sum

/-- The one-element right exchange property refines every finite decomposition of `1`
into orthogonal idempotents lying in the corresponding principal right ideals.  This
is the step named as remaining in the `ExchangePrerequisite` module docstring. -/
theorem hasFiniteRightExchangePartitions_of_hasRightExchange
    (hex : HasRightExchange R) : HasFiniteRightExchangePartitions R := by
  intro n x hsum
  exact exists_corner_partition hex n 1 IsIdempotentElem.one x (fun i => one_mul (x i)) hsum

/-- The finite refinement re-indexed along an arbitrary `Fintype`.  The matrix
calculus indexes rows by a general `Fintype`, while `HasFiniteRightExchangePartitions`
is stated for `Fin n`; this bridges the two. -/
theorem exists_orthogonal_refinement {κ : Type*} [Fintype κ]
    (hex : HasFiniteRightExchangePartitions R) (x : κ → R) (hsum : (∑ p, x p) = 1) :
    ∃ e r : κ → R,
      (∀ p, IsIdempotentElem (e p)) ∧
      (∀ p q, p ≠ q → e p * e q = 0) ∧
      (∀ p, e p = x p * r p) ∧
      (∑ p, e p) = 1 := by
  obtain ⟨ε⟩ : Nonempty (κ ≃ Fin (Fintype.card κ)) := ⟨Fintype.equivFin κ⟩
  have hsum' : (∑ i : Fin (Fintype.card κ), x (ε.symm i)) = 1 := by
    rw [Equiv.sum_comp ε.symm x]
    exact hsum
  obtain ⟨e, r, hidem, horth, heq, hesum⟩ :=
    hex (Fintype.card κ) (fun i => x (ε.symm i)) hsum'
  refine ⟨fun p => e (ε p), fun p => r (ε p), fun p => hidem _, ?_, ?_, ?_⟩
  · intro p q hpq
    exact horth _ _ fun hcontra => hpq (ε.injective hcontra)
  · intro p
    have hp := heq (ε p)
    simp only [Equiv.symm_apply_apply] at hp
    exact hp
  · rw [← hesum]
    exact Equiv.sum_comp ε fun i => e i

end ExchangePrerequisite

namespace BinaryLeavitt

variable (k : Type) [Field k]

/-- Every finite decomposition of `1` in the binary Leavitt algebra admits a
simultaneous orthogonal refinement by idempotents in the principal *right* ideals of
its entries.  This is the exact input Preusser's partition step consumes, and it
upgrades `BinaryLeavitt.exists_finite_twoSidedIdeal_partition`, whose witness is
concentrated at a single index. -/
theorem hasFiniteRightExchangePartitions :
    ExchangePrerequisite.HasFiniteRightExchangePartitions (BinaryLeavittAlgebra k) :=
  ExchangePrerequisite.hasFiniteRightExchangePartitions_of_hasRightExchange
    (BinaryLeavitt.hasRightExchange k)

/-- The binary Leavitt form of the refinement, indexed by an arbitrary `Fintype`. -/
theorem exists_orthogonal_refinement {κ : Type*} [Fintype κ]
    (x : κ → BinaryLeavittAlgebra k) (hsum : (∑ p, x p) = 1) :
    ∃ e r : κ → BinaryLeavittAlgebra k,
      (∀ p, IsIdempotentElem (e p)) ∧
      (∀ p q, p ≠ q → e p * e q = 0) ∧
      (∀ p, e p = x p * r p) ∧
      (∑ p, e p) = 1 :=
  ExchangePrerequisite.exists_orthogonal_refinement
    (BinaryLeavitt.hasFiniteRightExchangePartitions k) x hsum

end BinaryLeavitt

end GroupApproximation
