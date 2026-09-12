import GroupApproximation.CharClass.OddPEvalMultilinear
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Rotating the slots of the tensor evaluation, and expanding a sum in every slot

Two tuple-level facts the additivity of the odd-primary reduced powers consumes (plan R9).

* **The rotated E5**, `tupEval_tupT_rotate`.  E5 (`tupEval_tupT_const`) says a *constant* tuple of
  single-degree cochains does not see the cyclic operator.  At a general tuple the operator moves the
  cochains instead: `tupEval φ (T x) = tupEval (φ ∘ (finRotate r).symm) x`, provided every slot is
  concentrated in one degree `q` and the arity is odd.  The direction is forced by
  `tupRot t = t ∘ finRotate r`: the product over the rotated tuple reindexes along `finRotate r`, and
  the cochain that meets slot `j` of `t` is the one that sat in slot `(finRotate r).symm j`.  The
  Koszul sign is `q · (r − 1) q` on the support, even because `r − 1` is.
* **The expansion**, `tupEval_add_expand`: evaluating the tuple whose every slot is `a + b` is the sum,
  over all assignments `ε : Fin r → Bool`, of the evaluations of the tuples with `a` in the slots
  `ε` marks and `b` in the others.  On a basis tuple this is `Fintype.prod_sum` over `Bool`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] {X : TopCat.{0}} {r : ℕ}

/-! ## 1. The rotated E5 -/

/-- **(E5, rotated) The cyclic operator moves the cochains.**  For a tuple of graded cochains every one
of which is concentrated in degree `q`, at odd arity. -/
theorem tupEval_tupT_rotate (hr : Odd r) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (q : ℕ)
    (hq : ∀ l n, n ≠ q → φ l n = 0) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k φ (tupT K X r k x)
      = tupEval K X r k (fun l => φ ((finRotate r).symm l)) x := by
  have hL : (tupEval K X r k φ).comp (tupT K X r k)
      = tupEval K X r k (fun l => φ ((finRotate r).symm l)) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupT_single, map_smul, tupEval_single, tupEval_single, smul_eq_mul, tupRotIdx_val]
    have hre : ∏ j, tagEvalG K (φ j) (tupRot t.1 j)
        = ∏ j, tagEvalG K (φ ((finRotate r).symm j)) (t.1 j) := by
      have h := Equiv.prod_comp (finRotate r)
        (fun j => tagEvalG K (φ ((finRotate r).symm j)) (t.1 j))
      refine Eq.trans ?_ h
      refine Finset.prod_congr rfl fun j _ => ?_
      show tagEvalG K (φ j) (t.1 (finRotate r j))
        = tagEvalG K (φ ((finRotate r).symm (finRotate r j))) (t.1 (finRotate r j))
      rw [Equiv.symm_apply_apply]
    rw [hre]
    by_cases hall : ∀ l, (t.1 l).1 = q
    · have hr0 : 0 < r := by
        obtain ⟨m, hm⟩ := hr
        omega
      have hd0 : tupDeg t.1 0 = q := by
        unfold tupDeg
        rw [dif_pos hr0]
        exact hall _
      have hsum : ∑ j : Fin r, (t.1 j).1 = r * q := by
        rw [Finset.sum_congr rfl fun j _ => hall j, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      have hexp : Even (rotExp X t.1) := by
        unfold rotExp
        rw [hd0, hsum]
        obtain ⟨m, hm⟩ := hr
        have h2 : (2 * m + 1) * q - q = 2 * (m * q) := by
          rw [Nat.add_mul, one_mul, Nat.add_sub_cancel, Nat.mul_assoc]
        rw [hm, h2]
        exact (even_two_mul (m * q)).mul_left q
      rw [hexp.neg_one_pow, one_mul]
    · obtain ⟨l, hl⟩ := not_forall.mp hall
      have h0 : ∏ j, tagEvalG K (φ ((finRotate r).symm j)) (t.1 j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l)
          (tagEvalG_of_eq_zero K _ (t.1 l) (hq _ _ hl))
      rw [h0, mul_zero]
  exact LinearMap.congr_fun hL x

/-- **(E5, rotated and iterated)** `T ^ i` moves the cochains along `((finRotate r).symm) ^ i`. -/
theorem tupEval_tupT_pow_rotate (hr : Odd r) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (q : ℕ) (hq : ∀ l n, n ≠ q → φ l n = 0) (k i : ℕ) (x : tupMod K X r k) :
    tupEval K X r k φ ((tupT K X r k ^ i) x)
      = tupEval K X r k (fun l => φ (((finRotate r).symm ^ i) l)) x := by
  induction i generalizing x with
  | zero => simp only [pow_zero, Module.End.one_apply, Equiv.Perm.one_apply]
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, ih,
      tupEval_tupT_rotate K hr (fun l => φ (((finRotate r).symm ^ i) l)) q
        (fun l n hn => hq _ n hn)]
    refine congrArg (fun ψ => tupEval K X r k ψ x) (funext fun l => ?_)
    simp only [pow_succ, Equiv.Perm.mul_apply]

/-! ## 2. The expansion of a sum in every slot -/

/-- **The expansion.**  The tuple with `a + b` in every slot evaluates to the sum over assignments
`ε`, the slots `ε` marks carrying `a` and the others `b`. -/
theorem tupEval_add_expand (a b : ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ)
    (x : tupMod K X r k) :
    tupEval K X r k (fun _ => a + b) x
      = ∑ ε : Fin r → Bool, tupEval K X r k (fun l => bif ε l then a else b) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | add x y hx hy =>
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ε _ => (map_add _ x y).symm
  | single t c =>
    have hs : Finsupp.single t c = c • Finsupp.single t (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [hs, map_smul, smul_eq_mul]
    rw [← Finset.mul_sum, tupEval_single]
    congr 1
    have h1 : ∏ j, tagEvalG K ((fun _ : Fin r => a + b) j) (t.1 j)
        = ∏ j, ∑ β : Bool, (bif β then tagEvalG K a (t.1 j) else tagEvalG K b (t.1 j)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fintype.sum_bool]
      exact tagEvalG_add K a b (t.1 j)
    rw [h1, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [tupEval_single]
    refine Finset.prod_congr rfl fun j _ => ?_
    cases ε j <;> rfl

/-- Every slot of an assignment tuple built from two single-degree cochains is concentrated in that
degree. -/
theorem bif_concentrated (a b : ∀ n : ℕ, singularCochainGroup K X n) (q : ℕ)
    (ha : ∀ n, n ≠ q → a n = 0) (hb : ∀ n, n ≠ q → b n = 0) (ε : Fin r → Bool) :
    ∀ l n, n ≠ q → (bif ε l then a else b) n = 0 := by
  intro l n hn
  cases ε l
  · exact hb n hn
  · exact ha n hn

/-- Permuting the slots of an assignment tuple is permuting the assignment. -/
theorem bif_comp (a b : ∀ n : ℕ, singularCochainGroup K X n) (ε : Fin r → Bool) (π : Fin r → Fin r) :
    (fun l => bif ε (π l) then a else b) = (fun l => bif (fun l' => ε (π l')) l then a else b) :=
  rfl

#audit_axioms tupEval_tupT_rotate
#audit_axioms tupEval_tupT_pow_rotate
#audit_axioms tupEval_add_expand

end

end GroupApproximation.CharClass
