import GroupApproximation.CharClass.CartanFreeCxTensorAug
import GroupApproximation.CharClass.CartanTargetEquivariance

/-!
# The factor swap on a tensor square, in general

The Cartan comparison uses the swap twice: on `S(X) ⊗ S(X)`, where it is
`cc-steenrod`'s `swapEnd`, and on `S(X)^{⊗4}`, where it is the **block** swap
exchanging the first two factors with the last two.  Both are the same
construction applied to a tensor square, once with the singular complex as the
factor and once with the pair complex as the factor, so this file does it once.

That the fourfold swap is `(13)(24)` and not `(12)(34)` is forced twice over in
the comparison, and it comes out automatically here: the block swap of
`A ⊗ A` with `A` itself a tensor square exchanges blocks, which on the four
underlying factors is exactly `(13)(24)`.

## Main results

* `tenSwapIdx`, `tenSwap` — the swap on the index and on chains.
* `tenSwap_tenElt` — the swap on a decomposable element.
* `tensorD_tenSwap` — **the differential commutes with the swap**, so the swap
  makes the tensor square a complex of modules over the group ring.
* `tensorD_smul_tenSwap` — that linearity, stated for an arbitrary scalar.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A : FreeCx)

/-! ## 1. The swap -/

/-- Exchange the two tensor factors, degrees and all. -/
def tenSwapIdx {k : ℕ} (q : TensorIdx A A k) : TensorIdx A A k :=
  ⟨pairDegSwap q.1, (q.2.2, q.2.1)⟩

theorem tenSwapIdx_involutive {k : ℕ} (q : TensorIdx A A k) :
    tenSwapIdx A (tenSwapIdx A q) = q := rfl

/-- The swap, as an involution of the free `F₂`-module on the tensor index. -/
def tenSwap (k : ℕ) : Module.End (ZMod 2) (TensorIdx A A k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (tenSwapIdx A)

@[simp] theorem tenSwap_single (k : ℕ) (q : TensorIdx A A k) (c : ZMod 2) :
    tenSwap A k (Finsupp.single q c) = Finsupp.single (tenSwapIdx A q) c := by
  unfold tenSwap
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tenSwap_mul_self (k : ℕ) : tenSwap A k * tenSwap A k = 1 := by
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  show tenSwap A k (tenSwap A k (Finsupp.single q (1 : ZMod 2))) = Finsupp.single q 1
  rw [tenSwap_single, tenSwap_single, tenSwapIdx_involutive]

/-! ## 2. The swap on a decomposable element -/

theorem tenSwap_tenElt (k a b : ℕ) (h : a + b = k) (h' : b + a = k)
    (u : A.ι a →₀ ZMod 2) (v : A.ι b →₀ ZMod 2) :
    tenSwap A k (tenElt A A (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v)
      = tenElt A A (⟨(b, a), h'⟩ : Steenrod.PairDeg k) v u := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, tenElt_zero_right]
  | add f g hf hg => rw [tenElt_add_left, map_add, hf, hg, tenElt_add_right]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, tenElt_zero_left]
      | add f g hf hg => rw [tenElt_add_right, map_add, hf, hg, tenElt_add_left]
      | single y e =>
          have hc : (Finsupp.single x c : A.ι a →₀ ZMod 2)
              = c • Finsupp.single x (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          have he : (Finsupp.single y e : A.ι b →₀ ZMod 2)
              = e • Finsupp.single y (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hc, he, tenElt_smul_left, tenElt_smul_right, tenElt_single_single,
            map_smul, map_smul, tenSwap_single, tenElt_smul_left, tenElt_smul_right,
            tenElt_single_single]
          exact smul_comm _ _ _

/-! ## 3. The differential commutes with the swap -/

theorem tdL_tenSwap (k a b : ℕ) (h : b + a = k + 1) (h' : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : A.ι b →₀ ZMod 2) :
    tdL A A k b a h v u = tenSwap A k (tdR A A k a b h' u v) := by
  cases b with
  | zero => rw [tdL_zero, tdR_zero, map_zero]
  | succ b' =>
      rw [tdL_succ, tdR_succ]
      exact (tenSwap_tenElt A k a b' (by omega) (by omega) u (A.d b' v)).symm

theorem tdR_tenSwap (k a b : ℕ) (h : b + a = k + 1) (h' : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : A.ι b →₀ ZMod 2) :
    tdR A A k b a h v u = tenSwap A k (tdL A A k a b h' u v) := by
  cases a with
  | zero => rw [tdR_zero, tdL_zero, map_zero]
  | succ a' =>
      rw [tdR_succ, tdL_succ]
      exact (tenSwap_tenElt A k a' b (by omega) (by omega) (A.d a' u) v).symm

theorem tensorDGen_tenSwapIdx (k : ℕ) (q : TensorIdx A A (k + 1)) :
    tensorDGen A A k (tenSwapIdx A q) = tenSwap A k (tensorDGen A A k q) := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
  have key : tdL A A k b a (by omega) (Finsupp.single y 1) (Finsupp.single x 1)
        + tdR A A k b a (by omega) (Finsupp.single y 1) (Finsupp.single x 1)
      = tenSwap A k (tdL A A k a b hab (Finsupp.single x 1) (Finsupp.single y 1)
          + tdR A A k a b hab (Finsupp.single x 1) (Finsupp.single y 1)) := by
    rw [tdL_tenSwap A k a b (by omega) hab, tdR_tenSwap A k a b (by omega) hab, map_add]
    exact add_comm _ _
  exact key

/-- **The differential commutes with the swap.** -/
theorem tensorD_tenSwap (k : ℕ) (y : TensorIdx A A (k + 1) →₀ ZMod 2) :
    tensorD A A k (tenSwap A (k + 1) y) = tenSwap A k (tensorD A A k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]
  | single q c =>
      rw [tenSwap_single, tensorD_single, tensorD_single, map_smul,
        tensorDGen_tenSwapIdx]

/-! ## 4. The group ring acts -/

/-- **The tensor square is a module over the group ring**, with the generator
acting by the factor swap. -/
noncomputable abbrev tenModule (k : ℕ) :
    Module GroupRingZ2 (TensorIdx A A k →₀ ZMod 2) :=
  moduleOfInvolution (tenSwap A k) (tenSwap_mul_self A k)

/-- **The differential is linear over the group ring** for the swap action. -/
theorem tensorD_smul_tenSwap (k : ℕ) (c : GroupRingZ2)
    (y : TensorIdx A A (k + 1) →₀ ZMod 2) :
    letI := tenModule A (k + 1)
    letI := tenModule A k
    tensorD A A k (c • y) = c • tensorD A A k y := by
  letI := tenModule A (k + 1)
  letI := tenModule A k
  exact galAlgHom_comm (tenSwap A (k + 1)) (tenSwap_mul_self A (k + 1))
    (tenSwap A k) (tenSwap_mul_self A k) (tensorD A A k) (tensorD_tenSwap A k) c y

end

end GroupApproximation.CharClass
