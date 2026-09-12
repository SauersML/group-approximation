import GroupApproximation.CharClass.OddPTopPowerAWChain
import GroupApproximation.CharClass.OddPEval

/-!
# The iterated Alexander–Whitney diagonal evaluates to the cup power

Against the constant tuple `u, …, u` of a single-degree cochain `u ∈ C^q(X; K)`, the left-nested
`r`-fold Alexander–Whitney diagonal of a `q r`-simplex evaluates to the left-nested cup power
`u^{⌣r}`, with no sign and no degree cast:

* `cupPowQ u r : C^{q r}(X; K)`, `u^{⌣0} = 1`, `u^{⌣(r+1)} = u^{⌣r} ⌣ u` (vendored `cochainCup`;
  `q * (r + 1)` is `q * r + q` by definition, so the degree needs no cast);
* `tupEvalAll_awAll_piSingle` — `⟨u^{⊗r}, AW^{(r)}(σ)⟩ = u^{⌣r}(σ)`.

The proof peels the last slot: only the cut at `i = q r` has a back face of degree `q`, so the
sum over cuts collapses to one term, which is the defining formula of `cochainCup`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace TopPow

section Eval

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The evaluation of `r` graded cochains on the full tuple model**: on a basis tuple, the product
of the slot evaluations, with no sign. -/
def tupEvalAll (r : ℕ) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) :
    tupAllMod K X r →ₗ[K] K :=
  Finsupp.linearCombination K (fun t : TupAll X r => ∏ j, tagEvalG K (φ j) (t j))

theorem tupEvalAll_single {r : ℕ} (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (t : TupAll X r) :
    tupEvalAll K X r φ (Finsupp.single t 1) = ∏ j, tagEvalG K (φ j) (t j) := by
  unfold tupEvalAll
  rw [Finsupp.linearCombination_single, one_smul]

/-- The graded evaluation factors through the inclusion into the full model. -/
theorem tupEval_eq_tupEvalAll {r k : ℕ} (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (x : tupMod K X r k) : tupEval K X r k φ x = tupEvalAll K X r φ (tupIncl K X r k x) := by
  unfold tupEval tupEvalAll tupIncl
  rw [Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

/-- **Evaluating a concatenation**: the product of the evaluation of the first `r` slots and of the
last slot. -/
theorem tupEvalAll_catLin_single {r : ℕ} (φ : Fin (r + 1) → ∀ n : ℕ, singularCochainGroup K X n)
    (x : tupAllMod K X r) (τ : TagSimp X) :
    tupEvalAll K X (r + 1) φ (catLin K X r x (Finsupp.single τ 1))
      = tupEvalAll K X r (fun j => φ j.castSucc) x * tagEvalG K (φ (Fin.last r)) τ := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply, map_zero, map_zero, zero_mul]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, add_mul]
  | single t c =>
    rw [show Finsupp.single t c = c • Finsupp.single t (1 : K) by rw [Finsupp.smul_single_one],
      map_smul, LinearMap.smul_apply, map_smul, map_smul, catLin_single, tupEvalAll_single,
      tupEvalAll_single, Fin.prod_univ_castSucc, smul_eq_mul, smul_eq_mul, mul_assoc]
    unfold snocT
    rw [Fin.snoc_last]
    simp only [Fin.snoc_castSucc]

/-- **The cup power** `u^{⌣r} ∈ C^{q r}(X; K)`, left-nested: `u^{⌣0} = 1`, `u^{⌣(r+1)} = u^{⌣r} ⌣ u`. -/
def cupPowQ {q : ℕ} (u : singularCochainGroup K X q) : (r : ℕ) → singularCochainGroup K X (q * r)
  | 0 => cochainOne
  | r + 1 => cochainCup (q * r) q (cupPowQ u r) u

theorem cupPowQ_zero {q : ℕ} (u : singularCochainGroup K X q) :
    cupPowQ K X u 0 = cochainOne :=
  rfl

theorem cupPowQ_succ {q : ℕ} (u : singularCochainGroup K X q) (r : ℕ) :
    cupPowQ K X u (r + 1) = cochainCup (q * r) q (cupPowQ K X u r) u :=
  rfl

/-- A single-degree cochain evaluates to `0` off its degree. -/
theorem tagEvalG_piSingle_of_ne {q : ℕ} (u : singularCochainGroup K X q) (τ : TagSimp X)
    (h : τ.1 ≠ q) : tagEvalG K (Pi.single q u) τ = 0 :=
  tagEvalG_of_eq_zero K _ τ (Pi.single_eq_of_ne h u)

/-- A single-degree cochain on a sub-simplex of its degree. -/
theorem tagEvalG_piSingle_vtx {q k a : ℕ} (u : singularCochainGroup K X q)
    (σ : singularSimplices X k) (v : ℕ → ℕ) (hv : Monotone v) (h : a = q) :
    tagEvalG K (Pi.single q u) (vtx σ a v hv)
      = cochainEval q u ((TopCat.toSSet.obj X).map (clampHom q k v hv).op σ) := by
  subst h
  show cochainEval a (Pi.single a u a) ((TopCat.toSSet.obj X).map (clampHom a k v hv).op σ) = _
  rw [Pi.single_eq_same]

theorem front_vtx_eq_frontSimplex {m q : ℕ} (σ : singularSimplices X (m + q)) :
    (vtx σ m id monotone_id).2 = frontSimplex X m q σ := by
  have hf : clampHom m (m + q) id monotone_id = frontFace m q := by
    ext j : 3
    apply Fin.ext
    rw [clampHom_apply, frontFace_apply]
    show min j.val (m + q) = j.val
    have := j.isLt
    omega
  show (TopCat.toSSet.obj X).map (clampHom m (m + q) id monotone_id).op σ = frontSimplex X m q σ
  rw [hf]
  rfl

theorem back_map_eq_backSimplex {m q : ℕ} (σ : singularSimplices X (m + q)) :
    (TopCat.toSSet.obj X).map (clampHom q (m + q) (fun j => j + m) (addRight_mono m)).op σ
      = backSimplex X m q σ := by
  have hf : clampHom q (m + q) (fun j => j + m) (addRight_mono m) = backFace m q := by
    ext j : 3
    apply Fin.ext
    rw [clampHom_apply, backFace_apply]
    show min (j.val + m) (m + q) = j.val + m
    have := j.isLt
    omega
  rw [hf]
  rfl

/-- **The iterated Alexander–Whitney diagonal evaluates to the cup power.** -/
theorem tupEvalAll_awAll_piSingle {q : ℕ} (u : singularCochainGroup K X q) (r : ℕ)
    (σ : singularSimplices X (q * r)) :
    tupEvalAll K X r (fun _ => Pi.single q u) (awAll K X r ⟨q * r, σ⟩)
      = cochainEval (q * r) (cupPowQ K X u r) σ := by
  induction r with
  | zero =>
    rw [awAll_zero, if_pos rfl, tupEvalAll_single, Fin.prod_univ_zero, cupPowQ_zero,
      cochainOne_eval]
  | succ r ih =>
    rw [awAll_succ, map_sum, cupPowQ_succ]
    have hqr : q * (r + 1) = q * r + q := Nat.mul_succ q r
    rw [Finset.sum_eq_single (q * r)]
    · rw [tupEvalAll_catLin_single]
      have hfront : awFront (⟨q * (r + 1), σ⟩ : TagSimp X) (q * r)
          = ⟨q * r, (vtx σ (q * r) id monotone_id).2⟩ := rfl
      rw [hfront, ih, awBack, tagEvalG_piSingle_vtx K X u σ _ _ (by show q * (r + 1) - q * r = q; omega)]
      show cochainEval (q * r) (cupPowQ K X u r) (vtx σ (q * r) id monotone_id).2
          * cochainEval q u ((TopCat.toSSet.obj X).map
              (clampHom q (q * r + q) (fun j => j + q * r) (addRight_mono (q * r))).op σ)
        = cochainEval (q * r + q) (cochainCup (q * r) q (cupPowQ K X u r) u) σ
      rw [cochainCup_eval, front_vtx_eq_frontSimplex, back_map_eq_backSimplex]
    · intro i hi hne
      rw [tupEvalAll_catLin_single, awBack, tagEvalG_piSingle_of_ne K X u _
        (by show q * (r + 1) - i ≠ q; have := Finset.mem_range.mp hi; omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

#audit_axioms tupEvalAll_awAll_piSingle

end Eval

end TopPow

end

end GroupApproximation.CharClass
