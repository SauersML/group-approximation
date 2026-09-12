import GroupApproximation.CharClass.OddPTupleAction
-- `cochainCoboundary` and its evaluation formula; `OddPTuple`'s closure reaches `CupProduct` and
-- `AlexanderWhitneyFaceMaps` but not this file
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Evaluating a tuple of graded cochains on the flat `r`-fold tensor power

The evaluation layer of `sp-steenrod`'s plan §5.1: the pairing between the `r`-fold tensor power
`tupMod K X r k` of `OddPTuple.lean` and `r` cochains, one per slot, the evaluation carrying **no
sign** (the inter-lane sign contract, plan §11a item 3).

## Design

* **Cochains are graded.**  A slot's cochain is a whole family `φ : ∀ n, C^n(X; K)`, and a slot
  holding a simplex of degree `n` reads `φ n`.  So no degree ever has to be cast; a single-degree
  `u ∈ C^q` enters as `Pi.single q u`.
* **The coboundary is graded too.**  `gCoboundary φ` is `δ` in every degree, `0` in degree `0`.  With
  that, the evaluation of a boundary is one formula at every tuple, `tupEval_tupD_single`: the
  Koszul prefix sign of each slot times the evaluation with that slot's cochain replaced by its
  coboundary.  There is no degree case split in the statement; it happens once inside
  `tupEval_lc_tupUpdate`, where a `0`-simplex has no boundary and a graded cochain's coboundary has
  no degree-`0` part.
* **The cyclic operator is invisible to a constant tuple of single-degree cochains at odd arity.**
  The product is supported on tuples whose slots all have degree `q`, where `tupT`'s Koszul
  exponent is `q · (r − 1) q`, even because `r − 1` is.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The three definitions -/

/-- **A graded cochain evaluated on a tagged simplex**: the degree-`n` component on an
`n`-simplex. -/
def tagEvalG (K : Type) [CommRing K] {X : TopCat.{0}} (φ : ∀ n : ℕ, singularCochainGroup K X n)
    (τ : TagSimp X) : K :=
  cochainEval τ.1 (φ τ.1) τ.2

/-- **The evaluation of `r` graded cochains on the `r`-fold tensor power**: on a basis tuple, the
product of the slot evaluations, with no sign. -/
def tupEval (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ)
    (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) : tupMod K X r k →ₗ[K] K :=
  Finsupp.linearCombination K (fun t : TupIdx X r k => ∏ j, tagEvalG K (φ j) (t.1 j))

/-- **The graded coboundary**: `δ` in every positive degree, `0` in degree `0`. -/
def gCoboundary (K : Type) [CommRing K] (X : TopCat.{0})
    (φ : ∀ n : ℕ, singularCochainGroup K X n) : ∀ n : ℕ, singularCochainGroup K X n
  | 0 => 0
  | n + 1 => cochainCoboundary K X n (φ n)

variable (K : Type) [CommRing K] {X : TopCat.{0}} {r : ℕ}

@[simp] theorem gCoboundary_zero (φ : ∀ n : ℕ, singularCochainGroup K X n) :
    gCoboundary K X φ 0 = 0 := rfl

@[simp] theorem gCoboundary_succ (φ : ∀ n : ℕ, singularCochainGroup K X n) (n : ℕ) :
    gCoboundary K X φ (n + 1) = cochainCoboundary K X n (φ n) := rfl

theorem tagEvalG_of_eq_zero (φ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X)
    (h : φ τ.1 = 0) : tagEvalG K φ τ = 0 := by
  unfold tagEvalG
  rw [h, cochainEval_zero]

theorem tagEvalG_zero (τ : TagSimp X) :
    tagEvalG K (0 : ∀ n : ℕ, singularCochainGroup K X n) τ = 0 :=
  tagEvalG_of_eq_zero K 0 τ rfl

theorem tupEval_single (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) {k : ℕ}
    (t : TupIdx X r k) :
    tupEval K X r k φ (Finsupp.single t (1 : K)) = ∏ j, tagEvalG K (φ j) (t.1 j) := by
  rw [tupEval, Finsupp.linearCombination_single, one_smul]

/-! ## 2. Splitting a product at one slot -/

/-- A product over the slots is the value at slot `j` times the product of the other slots, each
of which may be rewritten. -/
theorem oddPEval_prod_split {M : Type} [CommMonoid M] (F G : Fin r → M) (j : Fin r) (a : M)
    (hj : F j = a) (hne : ∀ l, l ≠ j → F l = G l) :
    ∏ l, F l = a * ∏ l ∈ Finset.univ.erase j, G l := by
  rw [← hj, ← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ j)]
  exact congrArg (fun z => F j * z)
    (Finset.prod_congr rfl fun l hl => hne l (Finset.ne_of_mem_erase hl))

/-! ## 3. The evaluation of a boundary -/

/-- A replaced slot that lands in the target degree evaluates to the product over the updated
tuple. -/
theorem tupEval_tupUpdate_of_eq (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ)
    (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (h : ∑ l, (Function.update t j τ l).1 = k) :
    tupEval K X r k φ (tupUpdate K k t j τ) = ∏ l, tagEvalG K (φ l) (Function.update t j τ l) := by
  rw [tupUpdate, dif_pos h]
  exact tupEval_single K φ ⟨Function.update t j τ, h⟩

/-- **One slot of the boundary, evaluated.**  Differentiating slot `j` of a tuple of total degree
`k + 1` and evaluating is evaluating with slot `j`'s cochain replaced by its graded coboundary. -/
theorem tupEval_lc_tupUpdate (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ)
    (t : Fin r → TagSimp X) (j : Fin r) (s : TagSimp X) (hs : t j = s)
    (ht : ∑ l, (t l).1 = k + 1) :
    tupEval K X r k φ
        (Finsupp.linearCombination K (fun τ : TagSimp X => tupUpdate K k t j τ) (tagBd K X s))
      = tagEvalG K (gCoboundary K X (φ j)) s * ∏ l ∈ Finset.univ.erase j, tagEvalG K (φ l) (t l) := by
  obtain ⟨_ | n, σ⟩ := s
  · rw [tagBd_zero, map_zero, map_zero]
    have h0 : tagEvalG K (gCoboundary K X (φ j)) (⟨0, σ⟩ : TagSimp X) = 0 := cochainEval_zero 0 σ
    rw [h0, zero_mul]
  · have hR : tagEvalG K (gCoboundary K X (φ j)) (⟨n + 1, σ⟩ : TagSimp X)
        = ∑ i : Fin (n + 2), (-1 : K) ^ (i : ℕ) * cochainEval n (φ j n) (faceSimplex X n i σ) :=
      cochainCoboundary_eval K X n (φ j n) σ
    rw [tagBd_succ_eq_sum, map_sum, map_sum, hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdeg : ∑ l, (Function.update t j (⟨n, faceSimplex X n i σ⟩ : TagSimp X) l).1 = k := by
      have h := tupTot_update_succ t j (⟨n, faceSimplex X n i σ⟩ : TagSimp X)
        (congrArg Sigma.fst hs).symm
      omega
    have hev : tagEvalG K (φ j) (⟨n, faceSimplex X n i σ⟩ : TagSimp X)
        = cochainEval n (φ j n) (faceSimplex X n i σ) := rfl
    have hsplit : ∏ l, tagEvalG K (φ l) (Function.update t j (⟨n, faceSimplex X n i σ⟩ : TagSimp X) l)
        = cochainEval n (φ j n) (faceSimplex X n i σ)
            * ∏ l ∈ Finset.univ.erase j, tagEvalG K (φ l) (t l) :=
      -- `F`, `G` and `a` given explicitly: left as `_`, the `hne` lambda would be elaborated
      -- first and try to solve `?F l` with metavariables created under the binder `l`
      oddPEval_prod_split
        (fun l => tagEvalG K (φ l) (Function.update t j (⟨n, faceSimplex X n i σ⟩ : TagSimp X) l))
        (fun l => tagEvalG K (φ l) (t l)) j (cochainEval n (φ j n) (faceSimplex X n i σ))
        ((congrArg (tagEvalG K (φ j)) (Function.update_self j _ t)).trans hev)
        (fun l hl => congrArg (tagEvalG K (φ l)) (Function.update_of_ne hl _ t))
    rw [map_zsmul, map_zsmul, Finsupp.linearCombination_single, one_smul,
      tupEval_tupUpdate_of_eq K φ k t j _ hdeg, hsplit, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, mul_assoc]

/-- **(E4) The evaluation of a boundary.**  The Koszul prefix sign of each slot times the evaluation
with that slot's cochain replaced by its graded coboundary. -/
theorem tupEval_tupD_single (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ)
    (t : TupIdx X r (k + 1)) :
    tupEval K X r k φ (tupD K X r k (Finsupp.single t 1))
      = ∑ j : Fin r, (-1 : K) ^ tupPre t.1 j
          * ∏ l, tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t.1 l) := by
  rw [tupD_single, tupDGen, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, tupEval_lc_tupUpdate K φ k t.1 j (t.1 j) rfl t.2]
  congr 1
  exact (oddPEval_prod_split
    (fun l => tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t.1 l))
    (fun l => tagEvalG K (φ l) (t.1 l)) j (tagEvalG K (gCoboundary K X (φ j)) (t.1 j))
    (congrArg (fun ψ => tagEvalG K ψ (t.1 j)) (Function.update_self j _ φ))
    (fun l hl => congrArg (fun ψ => tagEvalG K ψ (t.1 l)) (Function.update_of_ne hl _ φ))).symm

/-- **(E4') Cocycles evaluate to zero on boundaries.** -/
theorem tupEval_tupD_eq_zero (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (hφ : ∀ j, gCoboundary K X (φ j) = 0) (k : ℕ) (x : tupMod K X r (k + 1)) :
    tupEval K X r k φ (tupD K X r k x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single t a =>
      have hs : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hz : ∀ j : Fin r, (-1 : K) ^ tupPre t.1 j
          * ∏ l, tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t.1 l) = 0 := by
        intro j
        have hj0 : tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) j) (t.1 j) = 0 := by
          rw [Function.update_self, hφ j]
          exact tagEvalG_zero K (t.1 j)
        have hprod : ∏ l, tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t.1 l) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hj0
        rw [hprod, mul_zero]
      rw [hs, map_smul, map_smul, tupEval_tupD_single, Finset.sum_eq_zero fun j _ => hz j, smul_zero]

/-! ## 4. The cyclic operator, against a constant tuple -/

/-- **(E5) A constant tuple of single-degree cochains does not see `tupT` at odd arity.** -/
theorem tupEval_tupT_const (hr : Odd r) (φ : ∀ n : ℕ, singularCochainGroup K X n) (q : ℕ)
    (hq : ∀ n, n ≠ q → φ n = 0) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (fun _ => φ) (tupT K X r k x) = tupEval K X r k (fun _ => φ) x := by
  have hL : (tupEval K X r k (fun _ => φ)).comp (tupT K X r k) = tupEval K X r k (fun _ => φ) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupT_single, map_smul, tupEval_single, tupEval_single, smul_eq_mul, tupRotIdx_val]
    have hre : ∏ j, tagEvalG K φ (tupRot t.1 j) = ∏ j, tagEvalG K φ (t.1 j) :=
      Equiv.prod_comp (finRotate r) (fun j => tagEvalG K φ (t.1 j))
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
      have h0 : ∏ j, tagEvalG K φ (t.1 j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l) (tagEvalG_of_eq_zero K φ (t.1 l) (hq _ hl))
      rw [h0, mul_zero]
  exact LinearMap.congr_fun hL x

theorem tupEval_tupT_pow_const (hr : Odd r) (φ : ∀ n : ℕ, singularCochainGroup K X n) (q : ℕ)
    (hq : ∀ n, n ≠ q → φ n = 0) (k : ℕ) (i : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (fun _ => φ) ((tupT K X r k ^ i) x) = tupEval K X r k (fun _ => φ) x := by
  induction i generalizing x with
  | zero => rw [pow_zero, Module.End.one_apply]
  | succ i ih => rw [pow_succ', Module.End.mul_apply, tupEval_tupT_const K hr φ q hq, ih]

/-- **(E6) The norm, against a constant tuple of single-degree cochains at odd arity**, is
multiplication by `r`. -/
theorem tupEval_sum_tupT_pow (hr : Odd r) (φ : ∀ n : ℕ, singularCochainGroup K X n) (q : ℕ)
    (hq : ∀ n, n ≠ q → φ n = 0) (k : ℕ) (x : tupMod K X r k) :
    ∑ i ∈ Finset.range r, tupEval K X r k (fun _ => φ) ((tupT K X r k ^ i) x)
      = (r : K) * tupEval K X r k (fun _ => φ) x := by
  rw [Finset.sum_congr rfl fun i _ => tupEval_tupT_pow_const K hr φ q hq k i x, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-! ## 5. The axiom closure -/

#audit_axioms tupEval_tupD_single
#audit_axioms tupEval_tupD_eq_zero
#audit_axioms tupEval_tupT_const
#audit_axioms tupEval_sum_tupT_pow

end

end GroupApproximation.CharClass
