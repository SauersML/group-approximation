import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner map `St_J(k) → St_J(R)`, `x_ij(λ) ↦ x_ij(λ p)` (lane `sk-cohn-02`, module 2)

Let `R` be a `k`-algebra and `p = p²` an idempotent.  The map `λ ↦ λ p` is additive and
multiplicative on `k`: `(a p)(b p) = a b p`.  It is not unital, but the Steinberg relations use
only sums and products, so it still induces a homomorphism `relKer_psi k p hp`.

The vector actions are intertwined.  Put `ι v = (m ↦ v m · p)` (`relKer_iota`); then
`act (ψ z) (ι v) = ι (act z v)` (`relKer_act_psi`).  For `k = 𝔽₂` and `p ≠ 0`, `ι` is
injective (`relKer_iota_injective`).  So an element of the image of `ψ` that acts trivially
on `R`-vectors comes from an element that acts trivially on `𝔽₂`-vectors.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

/-- `(a p)(b p) = (a b) p` for an idempotent `p`. -/
theorem relKer_algMap_mul (p : R) (hp : p * p = p) (a b : k) :
    algebraMap k R a * p * (algebraMap k R b * p) = algebraMap k R (a * b) * p := by
  calc algebraMap k R a * p * (algebraMap k R b * p)
      = algebraMap k R a * (p * algebraMap k R b) * p := by simp only [mul_assoc]
    _ = algebraMap k R a * (algebraMap k R b * p) * p := by rw [← Algebra.commutes b p]
    _ = algebraMap k R (a * b) * p := by rw [map_mul]; simp only [mul_assoc, hp]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_algMap_mul

/-- The image of a generator: `x_ij(λ) ↦ x_ij(λ p)`. -/
def relKer_psiGen (p : R) (g : SteinbergGenerator J k) : SteinbergGroup J R :=
  x g.row g.column g.row_ne_column (algebraMap k R g.coefficient * p)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_psiGen

/-- `relKer_psiGen` kills the Steinberg relators. -/
theorem relKer_psiGen_kills (p : R) (hp : p * p = p) (w : FreeGroup (SteinbergGenerator J k))
    (hw : w ∈ relations (I := J) (R := k)) : FreeGroup.lift (relKer_psiGen p) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, relKer_psiGen]
      change x i j hij (algebraMap k R a * p) * x i j hij (algebraMap k R b * p) *
        (x i j hij (algebraMap k R (a + b) * p))⁻¹ = 1
      rw [x_mul, map_add, add_mul, mul_inv_cancel]
  | commute i j k' l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, relKer_psiGen]
      change ⁅x i j hij (algebraMap k R a * p), x k' l hkl (algebraMap k R b * p)⁆ = 1
      exact (x_commute_of_ne i j k' l hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k' hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        relKer_psiGen]
      change ⁅x i j hij (algebraMap k R a * p), x j k' hjk (algebraMap k R b * p)⁆ *
        (x i k' hik (algebraMap k R (a * b) * p))⁻¹ = 1
      rw [x_commutator i j k' hij hjk hik, relKer_algMap_mul p hp, mul_inv_cancel]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_psiGen_kills

variable (k) in
/-- The corner homomorphism `ψ : St_J(k) → St_J(R)`, `x_ij(λ) ↦ x_ij(λ p)`. -/
def relKer_psi (p : R) (hp : p * p = p) : SteinbergGroup J k →* SteinbergGroup J R :=
  PresentedGroup.toGroup (f := relKer_psiGen p) (relKer_psiGen_kills p hp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_psi

theorem relKer_psi_x (p : R) (hp : p * p = p) (i j : J) (hij : i ≠ j) (a : k) :
    relKer_psi k p hp (x i j hij a) = x i j hij (algebraMap k R a * p) := by
  exact PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_psi_x

/-- The embedding of `k`-vectors into `R`-vectors, `v ↦ (m ↦ v m · p)`. -/
def relKer_iota (p : R) (v : J → k) : J → R := fun m => algebraMap k R (v m) * p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_iota

/-- Intertwining on a generator. -/
theorem relKer_act_psi_x (p : R) (hp : p * p = p) (i j : J) (hij : i ≠ j) (a : k)
    (v : J → k) :
    FieldTwo.act (x i j hij (algebraMap k R a * p)) (relKer_iota p v) =
      relKer_iota p (FieldTwo.act (x i j hij a) v) := by
  funext m
  rw [FieldTwo.act_x_apply]
  simp only [relKer_iota]
  rw [FieldTwo.act_x_apply]
  split_ifs
  · rw [relKer_algMap_mul p hp, map_add, add_mul]
  · simp only [add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_act_psi_x

/-- **Intertwining.**  `act (ψ z) (ι v) = ι (act z v)`. -/
theorem relKer_act_psi (p : R) (hp : p * p = p) (z : SteinbergGroup J k) (v : J → k) :
    FieldTwo.act (relKer_psi k p hp z) (relKer_iota p v) =
      relKer_iota p (FieldTwo.act z v) := by
  have hz : z ∈ Subgroup.closure
      (Set.range (PresentedGroup.of (rels := relations (I := J) (R := k)))) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top z
  induction hz using Subgroup.closure_induction generalizing v with
  | mem g hg =>
      obtain ⟨⟨i, j, hij, a⟩, rfl⟩ := hg
      change FieldTwo.act (relKer_psi k p hp (x i j hij a)) (relKer_iota p v) =
        relKer_iota p (FieldTwo.act (x i j hij a) v)
      rw [relKer_psi_x]
      exact relKer_act_psi_x p hp i j hij a v
  | one => rw [map_one, FieldTwo.act_one, FieldTwo.act_one]
  | mul g h _ _ hg hh => rw [map_mul, FieldTwo.act_mul, FieldTwo.act_mul, hh, hg]
  | inv g _ hg =>
      have h1 := hg (FieldTwo.act g⁻¹ v)
      rw [← FieldTwo.act_mul, mul_inv_cancel, FieldTwo.act_one] at h1
      rw [← h1, ← FieldTwo.act_mul, ← map_mul (relKer_psi k p hp), inv_mul_cancel, map_one,
        FieldTwo.act_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_act_psi

/-- Over `𝔽₂`, `ι` is injective once `p ≠ 0`. -/
theorem relKer_iota_injective {S : Type*} [Ring S] [Algebra (ZMod 2) S] (p : S) (hp0 : p ≠ 0) :
    Function.Injective (relKer_iota (J := J) (k := ZMod 2) p) := by
  have key : ∀ c : ZMod 2, algebraMap (ZMod 2) S c * p = 0 → c = 0 := by
    intro c hc
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with h | h
    · exact h
    · rw [h, map_one, one_mul] at hc
      exact absurd hc hp0
  intro v w hvw
  funext m
  have hm := congrFun hvw m
  simp only [relKer_iota] at hm
  have hsub : algebraMap (ZMod 2) S (v m - w m) * p = 0 := by
    rw [map_sub, sub_mul, hm, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_iota_injective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
