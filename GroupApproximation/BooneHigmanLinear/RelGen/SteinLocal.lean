import GroupApproximation.BooneHigmanLinear.RelGen.SteinRank1
import GroupApproximation.BooneHigmanLinear.RelGen.Statements
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 2: the rank-one identity over a local ring

Lane bh-pal-wire, k2-poly H.L3 (towards L–S Theorem 4.8). `A` is a local ring with maximal
ideal `M`.

* `unitsOneAdd_inv`, `unitsOneAdd_mul`: `(1 + J)ˣ` is closed under inverses and products.
* `h_mem_hBar`, `csym_mem_hBar_right`: generators of `H̄(A, J)`.
* **`gl1`**: for `s ∈ M`, `t ∈ A` and `u = 1 + s t`,
  `x_ji(t) x_ij(s) = x_ij(s u⁻¹) · H · x_ji(t u⁻¹)` with `H ∈ H̄(A, M)`. If `t` is a unit, this is
  `rank1_unit` on the transposed pair, inverted. If `t ∈ M`, write `x_ij(s) = x_ij(s + 1) x_ij(-1)`
  and apply `rank1_unit` twice. The units `s + 1` and `1 + (s + 1) t` are congruent to `1`, and
  the torus factor of the first step is moved past `x_ij(-u₂⁻¹)` by `cr_h_conj_self`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)
open GroupApproximation.BooneHigmanLinear.K2Poly (csym csym_commute)
open IsLocalRing

section UnitsOneAdd

variable {R : Type*} [CommRing R] {J : Ideal R}

theorem one_mem_unitsOneAdd : (1 : Rˣ) ∈ unitsOneAdd J := by
  show ((1 : Rˣ) : R) - 1 ∈ J
  rw [Units.val_one, sub_self]
  exact J.zero_mem

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.one_mem_unitsOneAdd

theorem unitsOneAdd_inv {u : Rˣ} (hu : u ∈ unitsOneAdd J) : u⁻¹ ∈ unitsOneAdd J := by
  show ((u⁻¹ : Rˣ) : R) - 1 ∈ J
  have e : ((u⁻¹ : Rˣ) : R) - 1 = -((u⁻¹ : Rˣ) : R) * ((u : R) - 1) := by
    linear_combination Units.inv_mul u
  rw [e]
  exact J.mul_mem_left _ hu

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.unitsOneAdd_inv

theorem unitsOneAdd_mul {u v : Rˣ} (hu : u ∈ unitsOneAdd J) (hv : v ∈ unitsOneAdd J) :
    u * v ∈ unitsOneAdd J := by
  show ((u * v : Rˣ) : R) - 1 ∈ J
  have e : ((u * v : Rˣ) : R) - 1 = (u : R) * ((v : R) - 1) + ((u : R) - 1) := by
    rw [Units.val_mul]
    ring
  rw [e]
  exact J.add_mem (J.mul_mem_left _ hv) hu

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.unitsOneAdd_mul

end UnitsOneAdd

section HBarGens

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] {J : Ideal R}

theorem h_mem_hBar {i j : I} (hij : i ≠ j) {u : Rˣ} (hu : u ∈ unitsOneAdd J) :
    h i j hij u ∈ hBar I J :=
  Subgroup.subset_closure (Or.inl ⟨i, j, hij, u, hu, rfl⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_mem_hBar

theorem csym_mem_hBar_right {i j : I} (hij : i ≠ j) (u : Rˣ) {v : Rˣ}
    (hv : v ∈ unitsOneAdd J) : csym i j hij u v ∈ hBar I J :=
  Subgroup.subset_closure (Or.inr ⟨i, j, hij, u, v, Or.inr hv, rfl⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.csym_mem_hBar_right

theorem csym_mem_hBar_left {i j : I} (hij : i ≠ j) {u : Rˣ} (hu : u ∈ unitsOneAdd J)
    (v : Rˣ) : csym i j hij u v ∈ hBar I J :=
  Subgroup.subset_closure (Or.inr ⟨i, j, hij, u, v, Or.inl hu, rfl⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.csym_mem_hBar_left

end HBarGens

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- In a local ring, `a ≡ 1 mod M` makes `a` a unit. -/
theorem isUnit_of_sub_one_mem {a : A} (h : a - 1 ∈ maximalIdeal A) : IsUnit a := by
  refine notMem_maximalIdeal.mp fun ha => ?_
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have e : (1 : A) = a - (a - 1) := by ring
    rw [e]
    exact (maximalIdeal A).sub_mem ha h
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.isUnit_of_sub_one_mem

/-- In a local ring every element is a unit or lies in `M`. -/
theorem isUnit_or_mem (a : A) : IsUnit a ∨ a ∈ maximalIdeal A := by
  by_cases h : IsUnit a
  · exact Or.inl h
  · exact Or.inr ((mem_maximalIdeal a).mpr h)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.isUnit_or_mem

end Local

section GL1

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] [IsLocalRing A]

/-- The case `t` a unit of `gl1`. -/
theorem gl1_unit (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {s : A}
    (hs : s ∈ maximalIdeal A) (t' u : Aˣ) (hu : (u : A) = 1 + s * (t' : A)) :
    ∃ H ∈ hBar I (maximalIdeal A), x j i hij.symm (t' : A) * x i j hij s =
      x i j hij (s * ((u⁻¹ : Aˣ) : A)) * H * x j i hij.symm ((t' : A) * ((u⁻¹ : Aˣ) : A)) := by
  have huM : u ∈ unitsOneAdd (maximalIdeal A) := by
    show (u : A) - 1 ∈ maximalIdeal A
    rw [hu, add_sub_cancel_left]
    exact (maximalIdeal A).mul_mem_right _ hs
  have hu' : (u : A) = 1 + ((-t' : Aˣ) : A) * (-s) := by
    rw [hu, Units.val_neg]
    ring
  have E := rank1_unit j i k hij.symm hjk hik (-t') u (-s) hu'
  refine ⟨(csym j i hij.symm (-(-t')) u⁻¹ * h j i hij.symm u⁻¹)⁻¹, Subgroup.inv_mem _
    (Subgroup.mul_mem _ (csym_mem_hBar_right _ _ (unitsOneAdd_inv huM))
      (h_mem_hBar _ (unitsOneAdd_inv huM))), ?_⟩
  have e1 : x j i hij.symm (t' : A) * x i j hij s =
      (x i j hij.symm.symm (-s) * x j i hij.symm ((-t' : Aˣ) : A))⁻¹ := by
    rw [mul_inv_rev, ← x_neg, ← x_neg, Units.val_neg, neg_neg, neg_neg]
  have c1 : (x i j hij.symm.symm (-s * ((u⁻¹ : Aˣ) : A)))⁻¹ = x i j hij (s * ((u⁻¹ : Aˣ) : A)) := by
    rw [← x_neg, neg_mul, neg_neg]
  have c2 : (x j i hij.symm (((-t' : Aˣ) : A) * ((u⁻¹ : Aˣ) : A)))⁻¹ =
      x j i hij.symm ((t' : A) * ((u⁻¹ : Aˣ) : A)) := by
    rw [← x_neg, Units.val_neg, neg_mul, neg_neg]
  rw [e1, E, ← c1, ← c2]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.gl1_unit

/-- The case `s, t ∈ M` of `gl1`: split `x_ij(s) = x_ij(s + 1) x_ij(-1)`. -/
theorem gl1_mem (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {s t : A}
    (hs : s ∈ maximalIdeal A) (ht : t ∈ maximalIdeal A) (u : Aˣ) (hu : (u : A) = 1 + s * t) :
    ∃ H ∈ hBar I (maximalIdeal A), x j i hij.symm t * x i j hij s =
      x i j hij (s * ((u⁻¹ : Aˣ) : A)) * H * x j i hij.symm (t * ((u⁻¹ : Aˣ) : A)) := by
  have huM : u ∈ unitsOneAdd (maximalIdeal A) := by
    show (u : A) - 1 ∈ maximalIdeal A
    rw [hu, add_sub_cancel_left]
    exact (maximalIdeal A).mul_mem_right _ hs
  -- The units `s₁ = s + 1` and `u₁ = 1 + (s + 1) t`.
  have hs1 : IsUnit (s + 1) := isUnit_of_sub_one_mem (by rw [add_sub_cancel_right]; exact hs)
  have hu1 : IsUnit (1 + (s + 1) * t) :=
    isUnit_of_sub_one_mem (by rw [add_sub_cancel_left]; exact (maximalIdeal A).mul_mem_left _ ht)
  obtain ⟨s1, hs1v⟩ : ∃ s1 : Aˣ, (s1 : A) = s + 1 := ⟨hs1.unit, hs1.unit_spec⟩
  obtain ⟨u1, hu1v⟩ : ∃ u1 : Aˣ, (u1 : A) = 1 + (s + 1) * t := ⟨hu1.unit, hu1.unit_spec⟩
  have hu1M : u1 ∈ unitsOneAdd (maximalIdeal A) := by
    show (u1 : A) - 1 ∈ maximalIdeal A
    rw [hu1v, add_sub_cancel_left]
    exact (maximalIdeal A).mul_mem_left _ ht
  obtain ⟨u2, hu2def⟩ : ∃ u2 : Aˣ, u2 = u1⁻¹ * u := ⟨_, rfl⟩
  have Hu1 : (u1 : A) * ((u1⁻¹ : Aˣ) : A) = 1 := Units.mul_inv u1
  have Hu : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := Units.mul_inv u
  have hu2v : ((u2⁻¹ : Aˣ) : A) = ((u⁻¹ : Aˣ) : A) * (u1 : A) := by
    rw [hu2def, mul_inv_rev, inv_inv, Units.val_mul]
  have hu2 : (u2 : A) = 1 + ((-1 : Aˣ) : A) * (t * ((u1⁻¹ : Aˣ) : A)) := by
    rw [hu2def, Units.val_mul, Units.val_neg, Units.val_one]
    linear_combination ((u1⁻¹ : Aˣ) : A) * hu + (-((u1⁻¹ : Aˣ) : A)) * hu1v + Hu1
  have hu2M : u2⁻¹ ∈ unitsOneAdd (maximalIdeal A) := by
    rw [hu2def]
    exact unitsOneAdd_inv (unitsOneAdd_mul (unitsOneAdd_inv hu1M) huM)
  have E1 := rank1_unit i j k hij hik hjk s1 u1 t (by rw [hu1v, hs1v])
  have E2 := rank1_unit i j k hij hik hjk (-1) u2 (t * ((u1⁻¹ : Aˣ) : A)) hu2
  -- Move the torus of the first step past `x_ij(-u₂⁻¹)`.
  have hmove : ∀ r : A, (csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) * x i j hij r =
      x i j hij (((u1⁻¹ : Aˣ) : A) * r * ((u1⁻¹ : Aˣ) : A)) *
        (csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) := by
    intro r
    have hh := cr_h_conj_self i j k hij hik hjk u1⁻¹ r
    calc (csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) * x i j hij r
        = csym i j hij (-s1) u1⁻¹ * (h i j hij u1⁻¹ * x i j hij r * (h i j hij u1⁻¹)⁻¹) *
            h i j hij u1⁻¹ := by group
      _ = csym i j hij (-s1) u1⁻¹ * x i j hij (((u1⁻¹ : Aˣ) : A) * r * ((u1⁻¹ : Aˣ) : A)) *
            h i j hij u1⁻¹ := by rw [hh]
      _ = _ := by rw [(csym_commute i j hij ⟨k, hik, hjk⟩ (-s1) u1⁻¹ _).eq]; group
  have hsplit : x i j hij s = x i j hij (s1 : A) * x i j hij ((-1 : Aˣ) : A) := by
    rw [x_mul, hs1v, Units.val_neg, Units.val_one]
    congr 1
    ring
  refine ⟨(csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) *
    (csym i j hij (-(-1)) u2⁻¹ * h i j hij u2⁻¹), Subgroup.mul_mem _
      (Subgroup.mul_mem _ (csym_mem_hBar_right _ _ (unitsOneAdd_inv hu1M))
        (h_mem_hBar _ (unitsOneAdd_inv hu1M)))
      (Subgroup.mul_mem _ (csym_mem_hBar_right _ _ hu2M) (h_mem_hBar _ hu2M)), ?_⟩
  have ecoef1 : (s1 : A) * ((u1⁻¹ : Aˣ) : A) +
      ((u1⁻¹ : Aˣ) : A) * (((-1 : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A)) * ((u1⁻¹ : Aˣ) : A) =
        s * ((u⁻¹ : Aˣ) : A) := by
    rw [hs1v, hu2v, Units.val_neg, Units.val_one]
    linear_combination (((u⁻¹ : Aˣ) : A) * ((u1⁻¹ : Aˣ) : A) * (s + 1)) * hu +
      (-(((u⁻¹ : Aˣ) : A) * ((u1⁻¹ : Aˣ) : A) * s)) * hu1v +
      (-((s + 1) * ((u1⁻¹ : Aˣ) : A))) * Hu +
      (s * ((u⁻¹ : Aˣ) : A) - ((u⁻¹ : Aˣ) : A) * ((u1⁻¹ : Aˣ) : A)) * Hu1
  have ecoef2 : t * ((u1⁻¹ : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A) = t * ((u⁻¹ : Aˣ) : A) := by
    rw [hu2v]
    linear_combination (t * ((u⁻¹ : Aˣ) : A)) * Hu1
  calc x j i hij.symm t * x i j hij s
      = (x j i hij.symm t * x i j hij (s1 : A)) * x i j hij ((-1 : Aˣ) : A) := by
        rw [hsplit, mul_assoc]
    _ = x i j hij ((s1 : A) * ((u1⁻¹ : Aˣ) : A)) * (csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) *
          (x j i hij.symm (t * ((u1⁻¹ : Aˣ) : A)) * x i j hij ((-1 : Aˣ) : A)) := by
        rw [E1]; group
    _ = x i j hij ((s1 : A) * ((u1⁻¹ : Aˣ) : A)) *
          ((csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) *
            x i j hij (((-1 : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A))) *
          (csym i j hij (-(-1)) u2⁻¹ * h i j hij u2⁻¹) *
          x j i hij.symm (t * ((u1⁻¹ : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A)) := by
        rw [E2]; group
    _ = x i j hij ((s1 : A) * ((u1⁻¹ : Aˣ) : A)) *
          x i j hij (((u1⁻¹ : Aˣ) : A) * (((-1 : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A)) *
            ((u1⁻¹ : Aˣ) : A)) *
          ((csym i j hij (-s1) u1⁻¹ * h i j hij u1⁻¹) *
            (csym i j hij (-(-1)) u2⁻¹ * h i j hij u2⁻¹)) *
          x j i hij.symm (t * ((u1⁻¹ : Aˣ) : A) * ((u2⁻¹ : Aˣ) : A)) := by
        rw [hmove]; group
    _ = _ := by rw [x_mul, ecoef1, ecoef2]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.gl1_mem

/-- **The local rank-one identity.** For `s ∈ M`, `t ∈ A` and `u = 1 + s t`,
`x_ji(t) x_ij(s) = x_ij(s u⁻¹) · H · x_ji(t u⁻¹)` with `H ∈ H̄(A, M)`. -/
theorem gl1 (third : ThirdIndex I) {i j : I} (hij : i ≠ j) {s t : A} (hs : s ∈ maximalIdeal A)
    (u : Aˣ) (hu : (u : A) = 1 + s * t) :
    ∃ H ∈ hBar I (maximalIdeal A), x j i hij.symm t * x i j hij s =
      x i j hij (s * ((u⁻¹ : Aˣ) : A)) * H * x j i hij.symm (t * ((u⁻¹ : Aˣ) : A)) := by
  obtain ⟨k, hik, hjk⟩ := third i j
  rcases isUnit_or_mem t with ht | ht
  · obtain ⟨t', rfl⟩ := ht
    exact gl1_unit i j k hij hik hjk hs t' u hu
  · exact gl1_mem i j k hij hik hjk hs ht u hu

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.gl1

end GL1

end GroupApproximation.BooneHigmanLinear.RelGen
