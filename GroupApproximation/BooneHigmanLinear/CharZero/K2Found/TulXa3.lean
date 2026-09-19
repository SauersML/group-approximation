import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXaConj2
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TwoZero
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# More relations of Tulenbaev's `X_{v,w}(a)`: parameter, projection, columns (T 1.1, 1.3(c))

Continuing `TulXa2` (`|I| ≥ 4`, under `IsLocal`). Let `w` lie in the span of the rows `⊥ v` with
two zeros (`w ∈ span (two0 v)`); this is where Tulenbaev's `X_{v,w}(a)` is defined. Then:
* `Xa_indep`: `Xa v w u` depends only on `u v`;
* `Xa_add_u`: `X_{v,w}(a) X_{v,w}(a') = X_{v,w}(a + a')`;
* `pm_Xa`: `π(X_{v,w}(a)) = 1 + a v w`, for any `w ⊥ v`;
* `Xa_smul_col` (from T 1.1(d)): `X_{cv,w}(a) = X_{v,w}(ca)`;
* `Xa_single`: `X_{e_k, e_l}(a) = x_kl(a)`;
* `Xa_col_add` (T 1.3(c)): `X_{v+cv',w}(a) = X_{v,w}(a) X_{v',w}(ca)` for `w` in the span of
  `TwoZero.twoZeroSet v v'`. This uses T 1.1(a), (d), and (e) across the two columns.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)
  [Fact (IsLocal hX)]

/-- The rows `⊥ v` with two zeros. -/
def two0 (v : I → A) : Set (I → A) :=
  {x | x ⬝ᵥ v = 0 ∧ TwoZ x}

omit [DecidableEq I] in
theorem exists_family {v w : I → A} (h : w ∈ Submodule.span A (two0 v)) :
    ∃ (n : ℕ) (f : Fin n → I → A), (∀ k, f k ⬝ᵥ v = 0) ∧ (∀ k, TwoZ (f k)) ∧ w = ∑ k, f k := by
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp h
  exact ⟨n, fun k => c k • (g k : I → A), fun k => smul_dot (c k) (g k).2.1,
    fun k => (g k).2.2.smul (c k), hg.symm⟩

/-- Products in different `Cv` agree when their factors agree in `St(A)`. -/
theorem coe_prod_congr {v v' : I → A} {ι : Type*} (s : Finset ι) (F : ι → Cv hX v)
    (G : ι → Cv hX v') (h : ∀ k, (F k : SteinbergGroup I A) = G k) :
    ((∏ k ∈ s, F k : Cv hX v) : SteinbergGroup I A) = ((∏ k ∈ s, G k : Cv hX v') : _) := by
  have e := conj_prod hX 1 s F G fun k => by rw [one_mul, inv_one, mul_one, h k]
  rwa [one_mul, inv_one, mul_one] at e

/-- `Xa v w u` depends only on `u v`. -/
theorem Xa_indep (h4 : 4 ≤ Fintype.card I) {v w : I → A} (hw : w ∈ Submodule.span A (two0 v))
    {u u' : I → A} (huv : u ⬝ᵥ v = u' ⬝ᵥ v) : Xa hX h4 v w u = Xa hX h4 v w u' := by
  obtain ⟨n, f, hv, h2, rfl⟩ := exists_family hw
  rw [Xa_eq_prod hX h4 v u _ f hv h2, Xa_eq_prod hX h4 v u' _ f hv h2]
  exact coe_prod_congr hX _ _ _ fun k => by rw [coe_txc, coe_txc, huv]

#audit_axioms Xa_indep

/-- `X_{v,w}(a) X_{v,w}(a') = X_{v,w}(a + a')`. -/
theorem Xa_add_u (h4 : 4 ≤ Fintype.card I) {v w : I → A} (hw : w ∈ Submodule.span A (two0 v))
    (u u' : I → A) : Xa hX h4 v w u * Xa hX h4 v w u' = Xa hX h4 v w (u + u') := by
  obtain ⟨n, f, hv, h2, rfl⟩ := exists_family hw
  rw [Xa_eq_prod hX h4 v u _ f hv h2, Xa_eq_prod hX h4 v u' _ f hv h2,
    Xa_eq_prod hX h4 v (u + u') _ f hv h2, ← Subgroup.coe_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨r, -, -, hr, -⟩ := h2 k
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_txc, coe_txc, coe_txc, add_dotProduct, add_smul,
    tx_add hX (r := r) (by rw [Pi.smul_apply, hr, smul_zero]) (by rw [Pi.smul_apply, hr, smul_zero])
      (smul_dot _ (hv k)) (smul_dot _ (hv k))]

#audit_axioms Xa_add_u

omit [Fact (IsLocal hX)] in
theorem pm_tx {v y : I → A} (hy : ∃ r, y r = 0) (hyv : y ⬝ᵥ v = 0) :
    pm (tx hX v y) = 1 + vecMulVec v y := by
  obtain ⟨r, hr⟩ := hy
  rw [tx_eq hX hr hyv, pm, pm_ex hX hr hyv, VdK.eUnit_val]

theorem pm_coe_prod {v : I → A} {ι : Type*} (s : Finset ι) (F : ι → Cv hX v) (ys : ι → I → A)
    (hF : ∀ k, pm (F k : SteinbergGroup I A) = 1 + vecMulVec v (ys k))
    (hys : ∀ k, ys k ⬝ᵥ v = 0) :
    pm ((∏ k ∈ s, F k : Cv hX v) : SteinbergGroup I A) = 1 + vecMulVec v (∑ k ∈ s, ys k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, OneMemClass.coe_one, pm_one, Finset.sum_empty,
      vecMulVec_zero, add_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subgroup.coe_mul, pm_mul, hF a, ih, Finset.sum_insert ha,
      vecMulVec_add, add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, hys a,
      zero_smul, vecMulVec_zero, add_zero]
    abel

/-- `π(X_{v,w}(a)) = 1 + (u v) v w` for `w ⊥ v`. -/
theorem pm_Xa (h4 : 4 ≤ Fintype.card I) {v w : I → A} (u : I → A) (hw : w ⬝ᵥ v = 0) :
    pm (Xa hX h4 v w u) = 1 + (u ⬝ᵥ v) • vecMulVec v w := by
  rw [Xa, pm_coe_prod hX Finset.univ
      (fun pq => txc hX (pc_dot v w u pq.1 pq.2) (pc_twoZ h4 v w u pq.1 pq.2))
      (fun pq => pc v w u pq.1 pq.2)
      (fun pq => by
        obtain ⟨l, -, -, hl, -⟩ := pc_twoZ h4 v w u pq.1 pq.2
        simp only [coe_txc]
        rw [pm_tx hX ⟨l, hl⟩ (pc_dot v w u pq.1 pq.2)])
      (fun pq => pc_dot v w u pq.1 pq.2),
    pc_sum_all u hw, vecMulVec_smul]

#audit_axioms pm_Xa

/-- `X_{cv,w}(a) = X_{v,w}(ca)` (from T 1.1(d)): `Xa (c v) w u = Xa v w u'` if
`u' v = c (u (c v))`. -/
theorem Xa_smul_col (h4 : 4 ≤ Fintype.card I) {v w : I → A}
    (hw : w ∈ Submodule.span A (two0 v)) (c : A) {u u' : I → A}
    (hu : u' ⬝ᵥ v = c * (u ⬝ᵥ (c • v))) : Xa hX h4 (c • v) w u = Xa hX h4 v w u' := by
  obtain ⟨n, f, hv, h2, rfl⟩ := exists_family hw
  have hv' : ∀ k, f k ⬝ᵥ (c • v) = 0 := fun k => dot_smul_zero c (hv k)
  rw [Xa_eq_prod hX h4 (c • v) u _ f hv' h2, Xa_eq_prod hX h4 v u' _ f hv h2]
  refine coe_prod_congr hX _ _ _ fun k => ?_
  obtain ⟨r, s, hrs, hr, hs⟩ := h2 k
  have hr' : ((u ⬝ᵥ (c • v)) • f k) r = 0 := by rw [Pi.smul_apply, hr, smul_zero]
  have hs' : ((u ⬝ᵥ (c • v)) • f k) s = 0 := by rw [Pi.smul_apply, hs, smul_zero]
  rw [coe_txc, coe_txc, tx_eq hX hr' (smul_dot _ (hv' k)),
    ex_smul_left hX hrs hr' hs' (smul_dot _ (hv k)), smul_smul, ← hu,
    tx_eq hX (r := r) (v := v) (x := (u' ⬝ᵥ v) • f k) (by rw [Pi.smul_apply, hr, smul_zero])
      (smul_dot _ (hv k))]

#audit_axioms Xa_smul_col

/-- `X_{e_k, e_l}(a) = x_kl(a)`, with `a = u e_k`. -/
theorem Xa_single (h4 : 4 ≤ Fintype.card I) {k l : I} (hkl : k ≠ l) (u : I → A) :
    Xa hX h4 (Pi.single k 1) (Pi.single l 1) u = x k l hkl (u ⬝ᵥ Pi.single k 1) := by
  obtain ⟨p, q, hpq, hpl, -, hql, -⟩ := exists_two_ne h4 l l
  have hv : ∀ _ : Unit, (Pi.single l (1 : A)) ⬝ᵥ Pi.single k 1 = 0 := fun _ => by
    rw [dotProduct_single_one, Pi.single_eq_of_ne hkl]
  have h2 : ∀ _ : Unit, TwoZ (Pi.single l (1 : A)) := fun _ =>
    ⟨p, q, hpq, Pi.single_eq_of_ne hpl 1, Pi.single_eq_of_ne hql 1⟩
  have e := Xa_eq_prod hX h4 (Pi.single k 1) u {()} (fun _ => Pi.single l (1 : A)) hv h2
  rw [Finset.sum_singleton, Finset.prod_singleton] at e
  have hk : ((u ⬝ᵥ Pi.single k 1) • Pi.single l (1 : A)) k = 0 := by
    rw [Pi.smul_apply, Pi.single_eq_of_ne hkl, smul_zero]
  rw [e, coe_txc, tx_eq hX hk (smul_dot _ (hv ())), ex_of_apply_one hX (Pi.single_eq_same k 1),
    x_eq_E hX hkl, ← Pi.single_smul', smul_eq_mul, mul_one]

#audit_axioms Xa_single

theorem commute_coe_prod {v : I → A} {ι : Type*} (s : Finset ι) (F : ι → Cv hX v)
    (g : SteinbergGroup I A) (h : ∀ k, Commute g (F k : SteinbergGroup I A)) :
    Commute g ((∏ k ∈ s, F k : Cv hX v) : SteinbergGroup I A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, OneMemClass.coe_one]
    exact Commute.one_right g
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subgroup.coe_mul]
    exact (h a).mul_right ih

/-- A product of `F_k G_k` splits as `(∏ F_k)(∏ G_k)` when every `G_k` commutes with every `F_l`. -/
theorem coe_prod_mul {v v₁ v₂ : I → A} {ι : Type*} (s : Finset ι) (H : ι → Cv hX v)
    (F : ι → Cv hX v₁) (G : ι → Cv hX v₂)
    (hH : ∀ k, (H k : SteinbergGroup I A) = F k * G k)
    (hc : ∀ k l, Commute (G k : SteinbergGroup I A) (F l)) :
    ((∏ k ∈ s, H k : Cv hX v) : SteinbergGroup I A) =
      ((∏ k ∈ s, F k : Cv hX v₁) : SteinbergGroup I A) * ((∏ k ∈ s, G k : Cv hX v₂) : _) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_mul, hH a, ih]
    simp only [mul_assoc]
    rw [(commute_coe_prod hX s F _ fun l => hc a l).left_comm]


end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
