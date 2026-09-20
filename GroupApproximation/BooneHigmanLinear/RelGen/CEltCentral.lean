import GroupApproximation.BooneHigmanLinear.RelGen.TitsCases
import GroupApproximation.BooneHigmanLinear.RelGen.Statements
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoRootSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# `c_ij(a, b)` is central when `a b = 0` (towards L–S Proposition 4.9)

Lane bh-pal-wire, k2-poly H.L3. Over a commutative ring, with a third index for every pair:

* `cElt_commute_x_of_mul_eq_zero`: if `a b = 0`, then `c_ij(a, b) = ⁅x_ij(a), x_ji(b)⁆` commutes
  with every root element `x_kl(ξ)` with `(k, l) ≠ (i, j), (j, i)`. This is the case `st = 0` of
  L–S Lemma 4.6 (1)–(3). In each of the five positions of `(k, l)`, conjugation by `x_kl(ξ)`
  changes one of `x_ij(a)`, `x_ji(b)` by a root element `e` whose commutator with the other has
  coefficient `± ξ a b = 0`, and `e` commutes with `c_ij(a, b)`.
* `cElt_central_of_mul_eq_zero`: `c_ij(a, b)` is central. The roots `± (i, j)` are commutators of
  roots through a third index.

In the application, the ring is `A[X] / X·M[X]`, where `s t = 0` for `s ∈ M[X]`, `t ∈ X·A[X]`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan_induction
  mem_rootSpan_true)

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- An element commuting with `x_ij(a)` and `x_ji(b)` commutes with `c_ij(a, b)`. -/
theorem commute_cElt_of {i j : I} (hij : i ≠ j) {a b : R} {e : SteinbergGroup I R}
    (h1 : Commute e (x i j hij a)) (h2 : Commute e (x j i hij.symm b)) :
    Commute e (cElt i j hij a b) := by
  rw [cElt, commutatorElement_def]
  exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_cElt_of

theorem commute_of_commutator_eq_one {G : Type*} [Group G] {a b : G} (h : ⁅a, b⁆ = 1) :
    Commute a b := by
  rw [commutatorElement_def] at h
  have e : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  exact e

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_of_commutator_eq_one

theorem commutator_mul_left' {G : Type*} [Group G] (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_mul_left'

theorem commutator_mul_right' {G : Type*} [Group G] (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_mul_right'

theorem conj_commutator_eq {G : Type*} [Group G] (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_commutator_eq

variable {i j : I} (hij : i ≠ j) {a b : R} (hab : a * b = 0)
include hab

/-- Position `l = i`, `k ∉ {i, j}`. -/
theorem cElt_conj_row_in {k : I} (hki : k ≠ i) (hkj : k ≠ j) (ξ : R) :
    x k i hki ξ * cElt i j hij a b * (x k i hki ξ)⁻¹ = cElt i j hij a b := by
  have hy : x k i hki ξ * x j i hij.symm b * (x k i hki ξ)⁻¹ = x j i hij.symm b := by
    rw [(x_commute_of_ne k i j i hki hij.symm hij (fun e => hki e.symm) ξ b).eq,
      mul_inv_cancel_right]
  have hx : x k i hki ξ * x i j hij a * (x k i hki ξ)⁻¹ = x k j hkj (ξ * a) * x i j hij a := by
    rw [conj_eq_commutator_mul, x_commutator k i j hki hij hkj]
  have hey : ⁅x k j hkj (ξ * a), x j i hij.symm b⁆ = 1 := by
    rw [x_commutator k j i hkj hij.symm hki, mul_assoc, hab, mul_zero, x_zero]
  have hce : Commute (x k j hkj (ξ * a)) (cElt i j hij a b) :=
    commute_cElt_of hij (x_commute_of_ne k j i j hkj hij hij.symm hkj.symm _ _)
      (commute_of_commutator_eq_one hey)
  rw [cElt, conj_commutator_eq, hx, hy, commutator_mul_left', hey, mul_one, ← cElt, hce.eq,
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_row_in

/-- Position `k = i`, `l ∉ {i, j}`. -/
theorem cElt_conj_row_out {l : I} (hil : i ≠ l) (hjl : j ≠ l) (ξ : R) :
    x i l hil ξ * cElt i j hij a b * (x i l hil ξ)⁻¹ = cElt i j hij a b := by
  have hx : x i l hil ξ * x i j hij a * (x i l hil ξ)⁻¹ = x i j hij a := by
    rw [(x_commute_of_ne i l i j hil hij (fun e => hil e.symm) (fun e => hij e.symm) ξ a).eq,
      mul_inv_cancel_right]
  have hy : x i l hil ξ * x j i hij.symm b * (x i l hil ξ)⁻¹ =
      x j l hjl (-(b * ξ)) * x j i hij.symm b := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator j i l hij.symm hil hjl,
      ← x_neg]
  have hxe : ⁅x i j hij a, x j l hjl (-(b * ξ))⁆ = 1 := by
    rw [x_commutator i j l hij hjl hil,
      show a * -(b * ξ) = 0 by rw [mul_neg, ← mul_assoc, hab, zero_mul, neg_zero], x_zero]
  have hce : Commute (x j l hjl (-(b * ξ))) (cElt i j hij a b) :=
    commute_cElt_of hij (commute_of_commutator_eq_one hxe).symm
      (x_commute_of_ne j l j i hjl hij.symm (fun e => hjl e.symm) hij _ _)
  rw [cElt, conj_commutator_eq, hx, hy, commutator_mul_right', hxe, one_mul, ← cElt, hce.eq,
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_row_out

/-- Position `l = j`, `k ∉ {i, j}`. -/
theorem cElt_conj_col_in {k : I} (hki : k ≠ i) (hkj : k ≠ j) (ξ : R) :
    x k j hkj ξ * cElt i j hij a b * (x k j hkj ξ)⁻¹ = cElt i j hij a b := by
  have hx : x k j hkj ξ * x i j hij a * (x k j hkj ξ)⁻¹ = x i j hij a := by
    rw [(x_commute_of_ne k j i j hkj hij hij.symm (fun e => hkj e.symm) ξ a).eq,
      mul_inv_cancel_right]
  have hy : x k j hkj ξ * x j i hij.symm b * (x k j hkj ξ)⁻¹ =
      x k i hki (ξ * b) * x j i hij.symm b := by
    rw [conj_eq_commutator_mul, x_commutator k j i hkj hij.symm hki]
  have hxe : ⁅x i j hij a, x k i hki (ξ * b)⁆ = 1 := by
    rw [← commutatorElement_inv, x_commutator k i j hki hij hkj,
      show ξ * b * a = 0 by rw [mul_assoc, mul_comm b a, hab, mul_zero], x_zero, inv_one]
  have hce : Commute (x k i hki (ξ * b)) (cElt i j hij a b) :=
    commute_cElt_of hij (commute_of_commutator_eq_one hxe).symm
      (x_commute_of_ne k i j i hki hij.symm hij (fun e => hki e.symm) _ _)
  rw [cElt, conj_commutator_eq, hx, hy, commutator_mul_right', hxe, one_mul, ← cElt, hce.eq,
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_col_in

/-- Position `k = j`, `l ∉ {i, j}`. -/
theorem cElt_conj_col_out {l : I} (hil : i ≠ l) (hjl : j ≠ l) (ξ : R) :
    x j l hjl ξ * cElt i j hij a b * (x j l hjl ξ)⁻¹ = cElt i j hij a b := by
  have hy : x j l hjl ξ * x j i hij.symm b * (x j l hjl ξ)⁻¹ = x j i hij.symm b := by
    rw [(x_commute_of_ne j l j i hjl hij.symm (fun e => hjl e.symm) hij ξ b).eq,
      mul_inv_cancel_right]
  have hx : x j l hjl ξ * x i j hij a * (x j l hjl ξ)⁻¹ =
      x i l hil (-(a * ξ)) * x i j hij a := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator i j l hij hjl hil, ← x_neg]
  have hey : ⁅x i l hil (-(a * ξ)), x j i hij.symm b⁆ = 1 := by
    rw [← commutatorElement_inv, x_commutator j i l hij.symm hil hjl,
      show b * -(a * ξ) = 0 by rw [mul_neg, ← mul_assoc, mul_comm b a, hab, zero_mul, neg_zero],
      x_zero, inv_one]
  have hce : Commute (x i l hil (-(a * ξ))) (cElt i j hij a b) :=
    commute_cElt_of hij
      (x_commute_of_ne i l i j hil hij (fun e => hil e.symm) (fun e => hij e.symm) _ _)
      (commute_of_commutator_eq_one hey)
  rw [cElt, conj_commutator_eq, hx, hy, commutator_mul_left', hey, mul_one, ← cElt, hce.eq,
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_conj_col_out

/-- **`c_ij(a, b)` commutes with every root element off `± (i, j)`** when `a b = 0`. -/
theorem cElt_commute_x_of_ne {k l : I} (hkl : k ≠ l) (hne : ¬(k = i ∧ l = j))
    (hne' : ¬(k = j ∧ l = i)) (ξ : R) : Commute (cElt i j hij a b) (x k l hkl ξ) := by
  suffices h : x k l hkl ξ * cElt i j hij a b * (x k l hkl ξ)⁻¹ = cElt i j hij a b from
    (mul_inv_eq_iff_eq_mul.mp h).symm
  by_cases hki : k = i
  · subst hki
    have hlj : l ≠ j := fun e => hne ⟨rfl, e⟩
    exact cElt_conj_row_out hij hab hkl (fun e => hlj e.symm) ξ
  · by_cases hkj : k = j
    · subst hkj
      have hli : l ≠ i := fun e => hne' ⟨rfl, e⟩
      exact cElt_conj_col_out hij hab (fun e => hli e.symm) hkl ξ
    · by_cases hli : l = i
      · subst hli
        exact cElt_conj_row_in hij hab hki hkj ξ
      · by_cases hlj : l = j
        · subst hlj
          exact cElt_conj_col_in hij hab hki hkj ξ
        · have h1 := x_commute_of_ne k l i j hkl hij (fun e => hli e) (fun e => hkj e.symm) ξ a
          have h2 := x_commute_of_ne k l j i hkl hij.symm (fun e => hlj e) (fun e => hki e.symm) ξ b
          rw [(commute_cElt_of hij h1 h2).eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_commute_x_of_ne

omit hab in
/-- A root element `x_ij(ξ)` as a commutator of two roots off `± (i, j)`. -/
theorem x_eq_commutator_third {m : I} (him : i ≠ m) (hjm : j ≠ m) (ξ : R) :
    x i j hij ξ = ⁅x i m him ξ, x m j (fun e => hjm e.symm) 1⁆ := by
  rw [x_commutator i m j him (fun e => hjm e.symm) hij, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_eq_commutator_third

omit hab in
/-- `Commute c p → Commute c q → Commute c ⁅p, q⁆`. -/
theorem commute_commutatorElement {G : Type*} [Group G] {c p q : G} (hp : Commute c p)
    (hq : Commute c q) : Commute c ⁅p, q⁆ := by
  rw [commutatorElement_def]
  exact ((hp.mul_right hq).mul_right hp.inv_right).mul_right hq.inv_right

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_commutatorElement

/-- `c_ij(a, b)` commutes with `x_ij(ξ)` (`a b = 0`). -/
theorem cElt_commute_x_self (third : ThirdIndex I) (ξ : R) :
    Commute (cElt i j hij a b) (x i j hij ξ) := by
  obtain ⟨m, him, hjm⟩ := third i j
  have hmi : m ≠ i := fun e => him e.symm
  have hmj : m ≠ j := fun e => hjm e.symm
  rw [x_eq_commutator_third hij him hjm ξ]
  exact commute_commutatorElement
    (cElt_commute_x_of_ne hij hab him (fun h => hmj h.2) (fun h => hij h.1) ξ)
    (cElt_commute_x_of_ne hij hab hmj (fun h => hmi h.1) (fun h => hmj h.1) 1)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_commute_x_self

/-- `c_ij(a, b)` commutes with `x_ji(ξ)` (`a b = 0`). -/
theorem cElt_commute_x_opp (third : ThirdIndex I) (ξ : R) :
    Commute (cElt i j hij a b) (x j i hij.symm ξ) := by
  obtain ⟨m, hjm, him⟩ := third j i
  have hmi : m ≠ i := fun e => him e.symm
  have hmj : m ≠ j := fun e => hjm e.symm
  rw [x_eq_commutator_third hij.symm hjm him ξ]
  exact commute_commutatorElement
    (cElt_commute_x_of_ne hij hab hjm (fun h => hij h.1.symm) (fun h => hmi h.2) ξ)
    (cElt_commute_x_of_ne hij hab hmi (fun h => hmi h.1) (fun h => hmj h.1) 1)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_commute_x_opp

/-- **`c_ij(a, b)` is central when `a b = 0`**, given a third index for every pair. -/
theorem cElt_central_of_mul_eq_zero (third : ThirdIndex I) (g : SteinbergGroup I R) :
    Commute (cElt i j hij a b) g := by
  have hroot : ∀ (k l : I) (hkl : k ≠ l) (ξ : R), Commute (cElt i j hij a b) (x k l hkl ξ) := by
    intro k l hkl ξ
    by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      exact cElt_commute_x_self hij hab third ξ
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        exact cElt_commute_x_opp hij hab third ξ
      · exact cElt_commute_x_of_ne hij hab hkl h1 h2 ξ
  exact rootSpan_induction (p := fun _ _ => True) (Q := fun g => Commute (cElt i j hij a b) g)
    (fun k l hkl ξ _ => hroot k l hkl ξ) (Commute.one_right _)
    (fun g₁ g₂ _ _ h₁ h₂ => h₁.mul_right h₂) (mem_rootSpan_true g)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_central_of_mul_eq_zero

end GroupApproximation.BooneHigmanLinear.RelGen
