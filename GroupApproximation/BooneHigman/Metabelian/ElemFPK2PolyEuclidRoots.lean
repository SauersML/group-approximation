import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyEuclidGen
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal forms for `K₂(F_p[X])`: every root of `G` is good once a small set is

Lane `bh-met-92h`, part 2.  Fix `m ∈ K`, `m ≠ L`, and a third index `n ∉ {m, L}`.  Suppose
the following are good (`k2PolyEuclid_Good`) for a set map `σ`:
`x_im(1)` and `x_mi(1)` (`i ∈ K \ {m}`), `x_mL(1)`, and `x_Lm(f)` for every `f`.
Then every root `x_ij(a)` with `i, j ∈ K ∪ {L}` is good (`k2PolyEuclid_good_all`).

1. `W = w_mL(1) = x_mL(1) x_Lm(-1) x_mL(1)` is good (`k2PolyEuclid_good_W`).
2. `x_mL(f) = W x_Lm(-f) W⁻¹` (`k2PolyDeg_w_conj_self_symm_eq`, `u = 1`, `t = -f`)
   (`k2PolyEuclid_good_mL`).
3. `x_iL(f) = ⁅x_im(1), x_mL(f)⁆` (`k2PolyEuclid_good_iL`).
4. `x_Lj(f) = ⁅x_Lm(f), x_mj(1)⁆` (`k2PolyEuclid_good_Lj`).
5. `x_ij(f) = ⁅x_iL(f), x_Lj(1)⁆` for `i, j ∈ K` (`k2PolyEuclid_good_ij`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w x_congr)

variable {I : Type} [Fintype I] [DecidableEq I]
variable {p : ℕ} [Fact p.Prime]

/-- Step 1: the Weyl element `W = w_mL(1)` is good. -/
theorem k2PolyEuclid_good_W {K : Finset I} {L m : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f)) :
    k2PolyEuclid_Good p K L σ (w m L hmL (1 : (Polynomial (ZMod p))ˣ)) := by
  have e1 : ((1 : (Polynomial (ZMod p))ˣ) : Polynomial (ZMod p)) = 1 := Units.val_one
  have e2 : (((1 : (Polynomial (ZMod p))ˣ)⁻¹ : (Polynomial (ZMod p))ˣ) :
      Polynomial (ZMod p)) = 1 := by
    rw [inv_one, Units.val_one]
  rw [w, e1, e2]
  exact k2PolyEuclid_good_mul (k2PolyEuclid_good_mul hy (hLm (-1))) hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_W

/-- Step 2: `x_mL(f) = W x_Lm(-f) W⁻¹` is good. -/
theorem k2PolyEuclid_good_mL {K : Finset I} {L m n : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f))
    (f : Polynomial (ZMod p)) : k2PolyEuclid_Good p K L σ (x m L hmL f) := by
  have e : x m L hmL f = w m L hmL (1 : (Polynomial (ZMod p))ˣ) * x L m hmL.symm (-f) *
      (w m L hmL (1 : (Polynomial (ZMod p))ˣ))⁻¹ := by
    rw [k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn (1 : (Polynomial (ZMod p))ˣ) (-f)]
    simp only [Units.val_one, one_mul, mul_one, neg_neg]
  rw [e]
  exact k2PolyEuclid_good_mul (k2PolyEuclid_good_mul (k2PolyEuclid_good_W hmL hy hLm)
    (hLm (-f))) (k2PolyEuclid_good_inv (k2PolyEuclid_good_W hmL hy hLm))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_mL

/-- Step 3: `x_iL(f) = ⁅x_im(1), x_mL(f)⁆` is good, for `i ∈ K`. -/
theorem k2PolyEuclid_good_iL {K : Finset I} {L m n : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hS : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f))
    {i : I} (hiK : i ∈ K) (hiL : i ≠ L) (f : Polynomial (ZMod p)) :
    k2PolyEuclid_Good p K L σ (x i L hiL f) := by
  by_cases him : i = m
  · rw [x_congr hiL hmL him rfl (rfl : f = f)]
    exact k2PolyEuclid_good_mL hmL hmn hLn hy hLm f
  · have e : x i L hiL f = ⁅x i m him (1 : Polynomial (ZMod p)), x m L hmL f⁆ := by
      rw [x_commutator i m L him hmL hiL, one_mul]
    rw [e]
    exact k2PolyEuclid_good_comm (hS i him hiK).1 (k2PolyEuclid_good_mL hmL hmn hLn hy hLm f)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_iL

/-- Step 4: `x_Lj(f) = ⁅x_Lm(f), x_mj(1)⁆` is good, for `j ∈ K`. -/
theorem k2PolyEuclid_good_Lj {K : Finset I} {L m : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hS : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f))
    {j : I} (hjK : j ∈ K) (hLj : L ≠ j) (f : Polynomial (ZMod p)) :
    k2PolyEuclid_Good p K L σ (x L j hLj f) := by
  by_cases hjm : j = m
  · rw [x_congr hLj hmL.symm rfl hjm (rfl : f = f)]
    exact hLm f
  · have e : x L j hLj f =
        ⁅x L m hmL.symm f, x m j (Ne.symm hjm) (1 : Polynomial (ZMod p))⁆ := by
      rw [x_commutator L m j hmL.symm (Ne.symm hjm) hLj, mul_one]
    rw [e]
    exact k2PolyEuclid_good_comm (hLm f) (hS j hjm hjK).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_Lj

/-- Step 5: `x_ij(f) = ⁅x_iL(f), x_Lj(1)⁆` is good, for `i, j ∈ K`. -/
theorem k2PolyEuclid_good_ij {K : Finset I} {L m n : I} (hLK : L ∉ K)
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hS : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f))
    {i j : I} (hiK : i ∈ K) (hjK : j ∈ K) (hij : i ≠ j) (f : Polynomial (ZMod p)) :
    k2PolyEuclid_Good p K L σ (x i j hij f) := by
  have hiL : i ≠ L := fun e => hLK (e ▸ hiK)
  have hLj : L ≠ j := fun e => hLK (e ▸ hjK)
  have e : x i j hij f = ⁅x i L hiL f, x L j hLj (1 : Polynomial (ZMod p))⁆ := by
    rw [x_commutator i L j hiL hLj hij, mul_one]
  rw [e]
  exact k2PolyEuclid_good_comm (k2PolyEuclid_good_iL hmL hmn hLn hS hy hLm hiK hiL f)
    (k2PolyEuclid_good_Lj hmL hS hLm hjK hLj 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_ij

/-- **Generation.**  If the small generating set is good, every root of `G` is good. -/
theorem k2PolyEuclid_good_all {K : Finset I} {L m n : I} (hLK : L ∉ K)
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hS : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))))
    (hy : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))))
    (hLm : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f))
    (i j : I) (hij : i ≠ j) (a : Polynomial (ZMod p)) (hi : i ∈ insert L K)
    (hj : j ∈ insert L K) : k2PolyEuclid_Good p K L σ (x i j hij a) := by
  by_cases hiL : i = L
  · have hjK : j ∈ K :=
      (Finset.mem_insert.1 hj).resolve_left (fun h => hij (hiL.trans h.symm))
    have hLj : L ≠ j := fun e => hij (hiL.trans e)
    rw [x_congr hij hLj hiL rfl (rfl : a = a)]
    exact k2PolyEuclid_good_Lj hmL hS hLm hjK hLj a
  · have hiK : i ∈ K := (Finset.mem_insert.1 hi).resolve_left hiL
    by_cases hjL : j = L
    · rw [x_congr hij (Ne.intro hiL) rfl hjL (rfl : a = a)]
      exact k2PolyEuclid_good_iL hmL hmn hLn hS hy hLm hiK (Ne.intro hiL) a
    · exact k2PolyEuclid_good_ij hLK hmL hmn hLn hS hy hLm hiK
        ((Finset.mem_insert.1 hj).resolve_left hjL) hij a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_all

end GroupApproximation.BooneHigman.Metabelian.ElemFP
