import GroupApproximation.CharClass.SteenrodFourfoldA
import GroupApproximation.CharClass.CartanMidFour

/-!
# The second composite, `B`

The second map of the Cartan comparison is nominally
`τ₂₃ ∘ (Φ ⊗ Φ) ∘ (Δ_W ⊗ Φ₀)`, but **neither `W ⊗ W` nor the middle
transposition ever has to be built**.  The source `W ⊗ S(X)` is free over `Λ`, so
`B` is defined by its values on that basis; and on a basis element the two of
them together collapse to a power of the generator acting on the second factor,
pulled out by the `Λ`-linearity of `Φ`:

```text
B(e_i ⊗ σ) = ∑_{p+q=i} ∑_{σ' ⊗ σ'' ∈ Φ₀(σ)}  Φ(e_p ⊗ σ') ⊗ (t^p · Φ(e_q ⊗ σ'')).
```

That observation is `cc-cartan`'s.  It removes an object, a transposition, and
the three lemmas each would have needed.

## Degrees are free parameters

`Φ(e_p ⊗ σ')` for `σ'` of degree `c` lives in total degree `c + p`, and `0 + N`
does not reduce to `N`, so writing the degrees as derived quantities would put a
transport in every term.  Instead `phiAtDeg` takes the total degree as a free
parameter and `padFour` is zero unless the two halves sum to the total — the same
totalising that made the chain-map condition tractable.

## `Λ`-linearity is free

`compB` is the `Λ`-linear extension from the basis of a *free* `Λ`-module into
the fourfold, so linearity for the block-swap action is by construction, exactly
as it was for `Φ` itself.  Nothing has to be proved.

## Main results

* `phiAtDeg`, `padFour`, `compBGen` — `Φ` at an explicit index, the totalised
  decomposable, and `B` on a basis element.
* `compB` — **the second composite**, `Λ`-linear.
* `compB_zero` — it sends `e₀ ⊗ x` to `x ⊗ x ⊗ x ⊗ x`, the same element
  `compA_zero` produces.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. `Φ` at an explicit index and total degree -/

/-- `Φ(e_i ⊗ σ)` read in total degree `m`, with `m` a free parameter.  The cut
combinatorics make it zero unless `m` is the degree it ought to be, so no
side-condition is carried. -/
def phiAtDeg (X : TopCat.{0}) (m i : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    PairIdx X m →₀ ZMod 2 :=
  ∑ a ∈ Finset.range (m + 1), phiCell X m i a (m - a) σ

theorem phiAtDeg_eq_phiPair (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 1))
    (σ : singularSimplices X n.val) :
    phiAtDeg X k (k - n.val) σ = phiPair X k ⟨n, σ⟩ :=
  (phiPair_eq X k n σ).symm

theorem phiZero_eq_phiAtDeg (X : TopCat.{0}) (N : ℕ) (σ : singularSimplices X N) :
    phiZero X N σ = phiAtDeg X N 0 σ := rfl

/-! ## 2. The totalised decomposable of the fourfold -/

/-- `u ⊗ v` in the fourfold, and `0` unless the two degrees sum to the total
one. -/
def padFour (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  if h : a + b = k then
    tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) u v
  else 0

theorem padFour_of_eq {X : TopCat.{0}} {k a b : ℕ} (h : a + b = k)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b u v
      = tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) u v :=
  dif_pos h

theorem padFour_of_ne {X : TopCat.{0}} {k a b : ℕ} (h : ¬ a + b = k)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b u v = 0 :=
  dif_neg h

theorem padFour_zero_left {X : TopCat.{0}} (k a b : ℕ) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b 0 v = 0 := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h]
    exact tenElt_zero_left (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) v
  · exact padFour_of_ne h 0 v

theorem padFour_add_left {X : TopCat.{0}} (k a b : ℕ)
    (u u' : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b (u + u') v = padFour X k a b u v + padFour X k a b u' v := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h, padFour_of_eq h, padFour_of_eq h]
    exact tenElt_add_left (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) u u' v
  · rw [padFour_of_ne h, padFour_of_ne h, padFour_of_ne h, add_zero]

theorem padFour_zero_right {X : TopCat.{0}} (k a b : ℕ) (u : PairIdx X a →₀ ZMod 2) :
    padFour X k a b u 0 = 0 := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h]
    exact tenElt_zero_right (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) u
  · exact padFour_of_ne h u 0

theorem padFour_add_right {X : TopCat.{0}} (k a b : ℕ) (u : PairIdx X a →₀ ZMod 2)
    (v v' : PairIdx X b →₀ ZMod 2) :
    padFour X k a b u (v + v') = padFour X k a b u v + padFour X k a b u v' := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h, padFour_of_eq h, padFour_of_eq h]
    exact tenElt_add_right (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : PairDeg k) u v v'
  · rw [padFour_of_ne h, padFour_of_ne h, padFour_of_ne h, add_zero]

/-! ## 3. The second composite -/

/-- One term of `B` **before the middle interchange**: the `p`-th summand, on one
basis element `σ' ⊗ σ''` of `Φ₀(σ)`.  The power of the generator on the second
factor is what the resolution's diagonal collapses to. -/
def compBPre (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
    (phiAtDeg X (r.1.val.1 + p) p r.2.1)
    ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2)

/-- One term of `B`.

**The middle interchange is not optional.**  Without it the four slots are
grouped as the two factors of `Φ(e_p ⊗ σ')` against the two of
`t^p Φ(e_q ⊗ σ'')`, and the resulting map intertwines the generator with the
permutation that swaps *inside* each block rather than with the block swap the
fourfold carries.  The two are told apart by the chain-map property and by
nothing weaker, which is why an earlier version of this definition survived four
green probes.  `cc-cartan`'s `midSwap` supplies the conjugation. -/
def compBTerm (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k
    (compBPre X k i p N r)

/-- **`B` on a basis element** `e_i ⊗ σ`, read in total degree `k`. -/
noncomputable def compBGen (X : TopCat.{0}) (k i : ℕ) {N : ℕ}
    (σ : singularSimplices X N) : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  ∑ p ∈ Finset.range (i + 1),
    Finsupp.linearCombination (ZMod 2) (compBTerm X k i p N) (phiZero X N σ)

/-- **The second composite of the Cartan comparison.**  `Λ`-linearity is by
construction: the source is free over `Λ`, so the extension from its basis is the
whole of linearity, and the block-swap action needs no separate argument. -/
noncomputable def compB (X : TopCat.{0}) (k : ℕ) :
    WTensorSMod X k →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  Finsupp.linearCombination GroupRingZ2
    (fun b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X =>
      compBGen X k (k - b.1.val) ((simplexEquiv X b.1.val).symm b.2))

theorem compB_single (X : TopCat.{0}) (k : ℕ)
    (b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X) (c : GroupRingZ2) :
    compB X k (Finsupp.single b c)
      = c • compBGen X k (k - b.1.val) ((simplexEquiv X b.1.val).symm b.2) := by
  unfold compB
  simp

/-! ## 4. The degree-zero value -/

/-- `Φ₀` on a `0`-simplex, written as a decomposable of the pair complex. -/
theorem phiZero_degree_zero_tenElt (X : TopCat.{0}) (σ : singularSimplices X 0) :
    phiZero X 0 σ
      = tenElt (singFreeCx X) (singFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
          (Finsupp.single σ 1) (Finsupp.single σ 1) := by
  rw [phiZero_degree_zero]
  exact (tenElt_single_single (singFreeCx X) (singFreeCx X)
    (⟨(0, 0), rfl⟩ : PairDeg 0) σ σ).symm

theorem compBGen_degree_zero (X : TopCat.{0}) (σ : singularSimplices X 0) :
    compBGen X 0 0 σ = fourDiagZero X σ := by
  unfold compBGen
  rw [Finset.sum_range_one, phiZero_degree_zero]
  have hlc : Finsupp.linearCombination (ZMod 2) (compBTerm X 0 0 0 0)
      (Finsupp.single (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) 1)
      = compBTerm X 0 0 0 0 (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) := by
    simp
  have hpre : compBPre X 0 0 0 0 (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0)
      = tenElt (pairFreeCx X) (pairFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
            (Finsupp.single σ 1) (Finsupp.single σ 1))
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
            (Finsupp.single σ 1) (Finsupp.single σ 1)) := by
    show padFour X 0 (0 + 0) (0 + (0 - 0)) (phiAtDeg X (0 + 0) 0 σ)
        ((groupRingGen ^ 0) • phiAtDeg X (0 + (0 - 0)) (0 - 0) σ) = _
    rw [pow_zero, one_smul, padFour_of_eq (show 0 + 0 = 0 from rfl)]
    show tenElt (pairFreeCx X) (pairFreeCx X) (⟨(0, 0), show 0 + 0 = 0 from rfl⟩ : PairDeg 0)
        (phiZero X 0 σ) (phiZero X 0 σ) = _
    rw [phiZero_degree_zero_tenElt]
  rw [hlc]
  show midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) 0
      (compBPre X 0 0 0 0 (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0)) = _
  rw [hpre, midSwap_tenElt4_single (singFreeCx X) (singFreeCx X) (singFreeCx X)
      (singFreeCx X) 0 0 0 0 0 0 0 rfl rfl rfl rfl σ σ σ σ]
  show tenElt (pairFreeCx X) (pairFreeCx X) (⟨(0, 0), show 0 + 0 = 0 from rfl⟩ : PairDeg 0)
      (tenElt (singFreeCx X) (singFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
        (Finsupp.single σ 1) (Finsupp.single σ 1))
      (tenElt (singFreeCx X) (singFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
        (Finsupp.single σ 1) (Finsupp.single σ 1)) = _
  rw [← phiZero_degree_zero_tenElt]
  rfl

/-- **The degree-zero normalisation.**  `B(e₀ ⊗ x) = x ⊗ x ⊗ x ⊗ x`, the same
element `compA_zero` produces. -/
theorem compB_zero (X : TopCat.{0})
    (φ : stdSimplexTop (0 : Fin (0 + 1)).val ⟶ X) :
    compB X 0 (Finsupp.single (⟨0, φ⟩ : Σ n : Fin (0 + 1), stdSimplexTop n.val ⟶ X) 1)
      = fourDiagZero X ((simplexEquiv X 0).symm φ) := by
  rw [compB_single, one_smul]
  exact compBGen_degree_zero X _

end

end Steenrod
end CharClass
end GroupApproximation
