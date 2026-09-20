import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXa4
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Naturality of Tulenbaev's elements under ring maps

Let `f : B →+* C`, with van der Kallen's elements `hB`, `hC` over `B`, `C`. If they are natural
(`EltNatural hB hC f`), then so are the elementary `X_r(v, w)` (`ex_natural`), the `X(v, x)`
(`tx_natural`), and Tulenbaev's `X_{v,w}(a)` (`Xa_natural`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements IsUnimodular)

variable {I B C : Type*} [Fintype I] [DecidableEq I] [CommRing B] [CommRing C]

section Comp

variable (f : B →+* C)

omit [Fintype I] in
theorem comp_single (r : I) : f ∘ Pi.single r (1 : B) = Pi.single r 1 := by
  funext i
  by_cases h : i = r
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

omit [Fintype I] [DecidableEq I] in
theorem comp_smul (c : B) (w : I → B) : f ∘ (c • w) = f c • (f ∘ w) := by
  funext i
  simp

omit [Fintype I] [DecidableEq I] in
theorem comp_add (v w : I → B) : f ∘ (v + w) = f ∘ v + f ∘ w := by
  funext i
  simp

omit [Fintype I] [DecidableEq I] in
theorem comp_sub (v w : I → B) : f ∘ (v - w) = f ∘ v - f ∘ w := by
  funext i
  simp

omit [Fintype I] in
theorem pc_natural (v w u : I → B) (p q : I) :
    f ∘ pc v w u p q = pc (f ∘ v) (f ∘ w) (f ∘ u) p q := by
  rw [pc, pc, comp_smul, comp_sub, comp_smul, comp_smul, comp_single, comp_single]
  simp only [Function.comp_apply, map_mul]

end Comp

variable (hB : Elements I B) (hC : Elements I C) (f : B →+* C)

/-- **Naturality of van der Kallen's elements** under `f : B →+* C`. -/
def EltNatural : Prop :=
  ∀ (v w : I → B), (v, w) ∈ U I B → ringMap f (E hB v w) = E hC (f ∘ v) (f ∘ w)

theorem ex_natural (hnat : EltNatural hB hC f) {r : I} {v w : I → B} (hr : w r = 0)
    (hw : w ⬝ᵥ v = 0) : ringMap f (ex hB r v w) = ex hC r (f ∘ v) (f ∘ w) := by
  have hq1 : (Pi.single r (1 : B), (v r - 1) • w) ∈ U I B :=
    memU (isUnimodular_single r) (smul_dot _ (dot_single hr))
  have hq2 : (v + (1 - v r) • Pi.single r (1 : B), w) ∈ U I B :=
    memU (isUnimodular_of_apply (tl_apply v r)) (dot_tl hr hw _)
  rw [ex, ex, map_mul, hnat _ _ hq1, hnat _ _ hq2, comp_single, comp_smul, comp_add, comp_smul,
    comp_single]
  simp only [Function.comp_apply, map_sub, map_one]

#audit_axioms ex_natural

theorem tx_natural (hnat : EltNatural hB hC f) {v y : I → B} (hy : ∃ r, y r = 0)
    (hyv : y ⬝ᵥ v = 0) : ringMap f (tx hB v y) = tx hC (f ∘ v) (f ∘ y) := by
  obtain ⟨r, hr⟩ := hy
  have hr' : (f ∘ y) r = 0 := by rw [Function.comp_apply, hr, map_zero]
  have hyv' : (f ∘ y) ⬝ᵥ (f ∘ v) = 0 := by rw [← RingHom.map_dotProduct, hyv, map_zero]
  rw [tx_eq hB hr hyv, tx_eq hC hr' hyv', ex_natural hB hC f hnat hr hyv]

#audit_axioms tx_natural

/-- A homomorphism carries a product in `Cv v` to the product of the images in `Cv v'`. -/
theorem hom_prod [Fact (IsLocal hB)] [Fact (IsLocal hC)]
    (φ : SteinbergGroup I B →* SteinbergGroup I C) {v : I → B} {v' : I → C} {ι : Type*}
    (s : Finset ι) (F : ι → Cv hB v) (G : ι → Cv hC v')
    (h : ∀ k, φ (F k : SteinbergGroup I B) = G k) :
    φ ((∏ k ∈ s, F k : Cv hB v) : SteinbergGroup I B) =
      ((∏ k ∈ s, G k : Cv hC v') : SteinbergGroup I C) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subgroup.coe_mul, Subgroup.coe_mul,
      map_mul, h a, ih]

/-- **Naturality of `X_{v,w}(a)`**. -/
theorem Xa_natural [Fact (IsLocal hB)] [Fact (IsLocal hC)] (hnat : EltNatural hB hC f)
    (h4 : 4 ≤ Fintype.card I) (v w u : I → B) :
    ringMap f (Xa hB h4 v w u) = Xa hC h4 (f ∘ v) (f ∘ w) (f ∘ u) := by
  rw [Xa, Xa]
  refine hom_prod hB hC (ringMap f) Finset.univ _ _ fun pq => ?_
  obtain ⟨l, -, -, hl, -⟩ := pc_twoZ h4 v w u pq.1 pq.2
  rw [coe_txc, coe_txc, tx_natural hB hC f hnat ⟨l, hl⟩ (pc_dot v w u pq.1 pq.2), pc_natural]

#audit_axioms Xa_natural

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
