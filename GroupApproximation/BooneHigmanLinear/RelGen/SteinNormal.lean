import GroupApproximation.BooneHigmanLinear.RelGen.SteinLocal
import GroupApproximation.BooneHigmanLinear.RelGen.Tits
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 3: `St̄(A, M) = ⟨St(Φ, M), H̄(A, M)⟩` over a local ring

Lane bh-pal-wire, k2-poly H.L3 (the form of L–S Theorem 4.8 that Proposition 4.9 uses).

* `ringMap_w`, `ringMap_h`, `h_one`: functoriality of `w` and `h`.
* `hBar_le_relKer`: `H̄(R, J) ≤ St̄(R, J)`. Generators map to `h(1) = 1` and `{1, v} = {v, 1} = 1`.
* `hBar_conj_x`: every `g ∈ H̄(R, J)` acts on each root by a scalar: `g x_kl(r) g⁻¹ = x_kl(c r)`,
  with `c ≡ 1 mod J` (`hBar_conj_x_sub_one`, by applying `St(R) → St(R/J)` and injectivity of
  `x_kl`).
* **`relKer_eq_sup_hBar`**: over a local ring, `St̄(A, M) = St(Φ, M) ⊔ H̄(A, M)`. The right side is
  normal. Conjugating `x_lk(m)` by `x_kl(ξ)` is `gl1`. Conjugating `g ∈ H̄` by `x_kl(ξ)` gives
  `g x_kl((c⁻¹ - 1) ξ)`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)
open GroupApproximation.BooneHigmanLinear.K2Poly (csym csym_commute hconj_exists)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan_induction
  mem_rootSpan_true)
open IsLocalRing

variable {I : Type*} [Fintype I] [DecidableEq I]

section Functoriality

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ringMap_w (f : R →+* S) {i j : I} (hij : i ≠ j) (u : Rˣ) :
    ringMap f (w i j hij u) = w i j hij (Units.map f.toMonoidHom u) := by
  have e1 : ((Units.map f.toMonoidHom u : Sˣ) : S) = f (u : R) := rfl
  have e2 : (((Units.map f.toMonoidHom u)⁻¹ : Sˣ) : S) = f ((u⁻¹ : Rˣ) : R) := rfl
  simp only [w, map_mul, ringMap_x, e1, e2, map_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_w

theorem ringMap_h (f : R →+* S) {i j : I} (hij : i ≠ j) (u : Rˣ) :
    ringMap f (h i j hij u) = h i j hij (Units.map f.toMonoidHom u) := by
  have e : Units.map f.toMonoidHom (-1 : Rˣ) = -1 :=
    Units.ext (show f (-(1 : R)) = -(1 : S) by rw [map_neg, map_one])
  rw [h, h, map_mul, ringMap_w, ringMap_w, e]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_h

theorem h_one {i j : I} (hij : i ≠ j) : h (R := R) i j hij 1 = 1 := by
  rw [h, ← w_inv, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_one

end Functoriality

section HBarKer

variable {R : Type*} [CommRing R] {J : Ideal R}

theorem units_map_mk_eq_one {u : Rˣ} (hu : u ∈ unitsOneAdd J) :
    Units.map (Ideal.Quotient.mk J).toMonoidHom u = 1 := by
  apply Units.ext
  rw [Units.coe_map, Units.val_one]
  show Ideal.Quotient.mk J (u : R) = 1
  rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
  exact hu

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.units_map_mk_eq_one

/-- `H̄(R, J) ≤ St̄(R, J)`. -/
theorem hBar_le_relKer : hBar I J ≤ relKer I J := by
  refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
  · rintro _ ⟨i, j, hij, u, hu, rfl⟩
    refine K2Found.mem_relSt.mpr ?_
    rw [ringMap_h, units_map_mk_eq_one hu, h_one]
  · rintro _ ⟨i, j, hij, u, v, huv, rfl⟩
    refine K2Found.mem_relSt.mpr ?_
    simp only [map_mul, map_inv, ringMap_h, map_mul]
    rcases huv with hu | hv
    · rw [units_map_mk_eq_one hu, one_mul, h_one]
      group
    · rw [units_map_mk_eq_one hv, mul_one, h_one]
      group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.hBar_le_relKer

/-- Every `g ∈ H̄(R, J)` acts on the root `(k, l)` by a unit scalar. -/
theorem hBar_conj_x (third : ThirdIndex I) {k l : I} (hkl : k ≠ l) {g : SteinbergGroup I R}
    (hg : g ∈ hBar I J) : ∃ c : Rˣ, ∀ r : R, g * x k l hkl r * g⁻¹ = x k l hkl ((c : R) * r) := by
  rw [hBar] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨i, j, hij, u, -, rfl⟩ | ⟨i, j, hij, u, v, -, rfl⟩
    · obtain ⟨χ, hχ⟩ := hconj_exists i j k l hij hkl (third i j) (R := R)
      exact ⟨χ u, hχ u⟩
    · refine ⟨1, fun r => ?_⟩
      have hc := (csym_commute i j hij (third i j) u v (x k l hkl r)).eq
      simp only [csym] at hc
      rw [hc, Units.val_one, one_mul]
      group
  | one => exact ⟨1, fun r => by simp only [Units.val_one, one_mul, inv_one, mul_one]⟩
  | mul g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁⟩ := h₁
    obtain ⟨c₂, hc₂⟩ := h₂
    refine ⟨c₁ * c₂, fun r => ?_⟩
    rw [show g₁ * g₂ * x k l hkl r * (g₁ * g₂)⁻¹ =
      g₁ * (g₂ * x k l hkl r * g₂⁻¹) * g₁⁻¹ by group, hc₂, hc₁, Units.val_mul, mul_assoc]
  | inv g _ h₁ =>
    obtain ⟨c, hc⟩ := h₁
    refine ⟨c⁻¹, fun r => ?_⟩
    have e := hc (((c⁻¹ : Rˣ) : R) * r)
    rw [← mul_assoc, Units.mul_inv, one_mul] at e
    rw [← e]
    group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.hBar_conj_x

/-- The scalar of an element of `St̄(R, J)` acting diagonally on a root is `≡ 1 mod J`. -/
theorem scalar_sub_one_mem {k l : I} (hkl : k ≠ l) {g : SteinbergGroup I R} (hg : g ∈ relKer I J)
    {c : R} (hc : g * x k l hkl 1 * g⁻¹ = x k l hkl (c * 1)) : c - 1 ∈ J := by
  have hmk := congrArg (ringMap (I := I) (Ideal.Quotient.mk J)) hc
  rw [map_mul, map_mul, map_inv, K2Found.mem_relSt.mp hg, one_mul, inv_one, mul_one, ringMap_x,
    ringMap_x, mul_one] at hmk
  have := x_injective (R := R ⧸ J) k l hkl hmk
  exact Ideal.Quotient.eq.mp this.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.scalar_sub_one_mem

end HBarKer

section LocalSup

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- `St(Φ, M) ⊔ H̄(A, M)` as a closure. -/
theorem sup_hBar_eq_closure :
    xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A) =
      Subgroup.closure (xSet I (maximalIdeal A) ∪ (hBar I (maximalIdeal A) : Set _)) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, xGroup]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.sup_hBar_eq_closure

/-- Conjugating `x_lk(m)`, `m ∈ M`, by `x_kl(ξ)` stays in `St(Φ, M) ⊔ H̄(A, M)` (`gl1`). -/
theorem conj_opp_mem_sup (third : ThirdIndex I) {k l : I} (hkl : k ≠ l) (ξ : A) {m : A}
    (hm : m ∈ maximalIdeal A) :
    x k l hkl ξ * x l k hkl.symm m * (x k l hkl ξ)⁻¹ ∈
      xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A) := by
  have hu : IsUnit (1 + m * ξ) :=
    isUnit_of_sub_one_mem (by rw [add_sub_cancel_left]; exact (maximalIdeal A).mul_mem_right _ hm)
  obtain ⟨u, huv⟩ : ∃ u : Aˣ, (u : A) = 1 + m * ξ := ⟨hu.unit, hu.unit_spec⟩
  have huM : u ∈ unitsOneAdd (maximalIdeal A) := by
    show (u : A) - 1 ∈ maximalIdeal A
    rw [huv, add_sub_cancel_left]
    exact (maximalIdeal A).mul_mem_right _ hm
  obtain ⟨H, hH, E⟩ := gl1 third hkl.symm hm u huv
  have hc : ξ * ((u⁻¹ : Aˣ) : A) + -ξ ∈ maximalIdeal A := by
    have e : ξ * ((u⁻¹ : Aˣ) : A) + -ξ = ξ * (((u⁻¹ : Aˣ) : A) - 1) := by ring
    rw [e]
    exact (maximalIdeal A).mul_mem_left _ (unitsOneAdd_inv huM)
  have e2 : x k l hkl ξ * x l k hkl.symm m * (x k l hkl ξ)⁻¹ =
      x l k hkl.symm (m * ((u⁻¹ : Aˣ) : A)) * H *
        x k l hkl (ξ * ((u⁻¹ : Aˣ) : A) + -ξ) := by
    rw [E, ← x_mul, x_neg]
    group
  rw [e2]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right hH)) ?_
  · exact Subgroup.mem_sup_left (x_mem_xGroup hkl.symm ((maximalIdeal A).mul_mem_right _ hm))
  · exact Subgroup.mem_sup_left (x_mem_xGroup hkl hc)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_opp_mem_sup

/-- Conjugating `g ∈ H̄(A, M)` by `x_kl(ξ)` gives `g x_kl((c - 1) ξ)`. -/
theorem conj_hBar_mem_sup (third : ThirdIndex I) {k l : I} (hkl : k ≠ l) (ξ : A)
    {g : SteinbergGroup I A} (hg : g ∈ hBar I (maximalIdeal A)) :
    x k l hkl ξ * g * (x k l hkl ξ)⁻¹ ∈ xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A) := by
  obtain ⟨c, hc⟩ := hBar_conj_x third hkl (Subgroup.inv_mem _ hg)
  have hc1 : (c : A) - 1 ∈ maximalIdeal A :=
    scalar_sub_one_mem hkl (hBar_le_relKer (Subgroup.inv_mem _ hg)) (hc 1)
  have e : x k l hkl ξ * g * (x k l hkl ξ)⁻¹ = g * x k l hkl (((c : A) - 1) * ξ) := by
    have h1 := hc ξ
    rw [inv_inv] at h1
    calc x k l hkl ξ * g * (x k l hkl ξ)⁻¹
        = g * (g⁻¹ * x k l hkl ξ * g) * (x k l hkl ξ)⁻¹ := by group
      _ = g * x k l hkl (((c : A) - 1) * ξ) := by
        rw [h1, ← x_neg, mul_assoc, x_mul]
        congr 2
        ring
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hg)
    (Subgroup.mem_sup_left (x_mem_xGroup hkl ((maximalIdeal A).mul_mem_right _ hc1)))

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_hBar_mem_sup

/-- Conjugation by a root element preserves `St(Φ, M) ⊔ H̄(A, M)`. -/
theorem conj_x_mem_sup (third : ThirdIndex I) {k l : I} (hkl : k ≠ l) (ξ : A)
    {g : SteinbergGroup I A} (hg : g ∈ xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A)) :
    x k l hkl ξ * g * (x k l hkl ξ)⁻¹ ∈ xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A) := by
  rw [sup_hBar_eq_closure] at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rw [← sup_hBar_eq_closure]
    rcases hg with ⟨c, d, hcd, m, hm, rfl⟩ | hg
    · by_cases hc : c = l ∧ d = k
      · obtain ⟨rfl, rfl⟩ := hc
        exact conj_opp_mem_sup third hkl ξ hm
      · exact Subgroup.mem_sup_left (conj_x_mem_xGroup hkl hcd ξ hm hc)
    · exact conj_hBar_mem_sup third hkl ξ hg
  | one => simp only [mul_one, mul_inv_cancel, Subgroup.one_mem]
  | mul g₁ g₂ _ _ h₁ h₂ =>
    rw [show x k l hkl ξ * (g₁ * g₂) * (x k l hkl ξ)⁻¹ =
      (x k l hkl ξ * g₁ * (x k l hkl ξ)⁻¹) * (x k l hkl ξ * g₂ * (x k l hkl ξ)⁻¹) by group]
    exact Subgroup.mul_mem _ h₁ h₂
  | inv g _ h₁ =>
    rw [show x k l hkl ξ * g⁻¹ * (x k l hkl ξ)⁻¹ = (x k l hkl ξ * g * (x k l hkl ξ)⁻¹)⁻¹ by
      group]
    exact Subgroup.inv_mem _ h₁

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_x_mem_sup

/-- **`St̄(A, M) = St(Φ, M) ⊔ H̄(A, M)`** over a local ring (the generation half of L–S 4.8). -/
theorem relKer_eq_sup_hBar (third : ThirdIndex I) :
    relKer I (maximalIdeal A) = xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A) := by
  have hN : (xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine rootSpan_induction (p := fun _ _ => True)
      (Q := fun g => ∀ n ∈ xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A),
        g * n * g⁻¹ ∈ xGroup I (maximalIdeal A) ⊔ hBar I (maximalIdeal A))
      (fun i j hij a _ n hn => conj_x_mem_sup third hij a hn)
      (fun n hn => by simpa only [one_mul, inv_one, mul_one] using hn)
      (fun g₁ g₂ _ _ h₁ h₂ n hn => by
        rw [show g₁ * g₂ * n * (g₁ * g₂)⁻¹ = g₁ * (g₂ * n * g₂⁻¹) * g₁⁻¹ by group]
        exact h₁ _ (h₂ n hn))
      (mem_rootSpan_true g) n hn
  refine le_antisymm ?_ (sup_le ?_ hBar_le_relKer)
  · rw [relKer, K2Found.relSt_eq_normalClosure (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨i, j, hij, a, ha, rfl⟩
    exact Subgroup.mem_sup_left (x_mem_xGroup hij (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, j, hij, s, hs, rfl⟩
    exact mem_relKer_of_x hij hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.relKer_eq_sup_hBar

end LocalSup

end GroupApproximation.BooneHigmanLinear.RelGen
