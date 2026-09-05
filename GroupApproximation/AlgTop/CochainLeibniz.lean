import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# The signed Alexander–Whitney Leibniz identity

This file proves, for an arbitrary commutative coefficient ring `R`, the
Alexander–Whitney chain-map / Leibniz identity for the cochain-level singular cup
product:

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ.
```

This is the one genuinely missing step between the vendored HamSandwich
development and an *integral* singular cohomology ring. That development already
supplies, generic in `R`, the singular cochain complex, the Alexander–Whitney
front/back faces, the cochain cup product `cochainCup`, the coboundary
`cochainCoboundary` with its alternating-face evaluation formula, and the four
face-composition identities. What it proves is the `ZMod 2` specialization
`aw_cochain_leibniz_zmod2`, whose only characteristic-two input is the abstract
splitting lemma `sum_split_char2`: there the two endpoint terms are *equal* and
cancel because `2 = 0`.

Over a general ring the same two endpoint terms are *negatives* of each other,
because the front endpoint carries the sign `(-1)^{p+1}` and the back endpoint
the sign `(-1)^p`. So the entire vendored telescoping argument goes through once
`sum_split_char2` is replaced by `sum_split_signed` below, whose endpoint
hypothesis is `A (Fin.last (p+1)) = - B 0` and which needs no torsion assumption
at all.

## Main results

* `sum_split_signed` — the sign-aware front/back splitting of a sum over
  `Fin (p+q+2)`, with cancelling endpoints.
* `aw_cochain_leibniz` — the Leibniz identity over any `CommRing R`.
* `cochainCup_cocycle` — the cup product of two cocycles is a cocycle.

## Degree bookkeeping

The three terms naturally live in degrees `(p+q)+1`, `(p+1)+q` and `p+(q+1)`.
`p+(q+1)` is **definitionally** `(p+q)+1`, but `(p+1)+q` is only propositionally
equal to it, so the `δφ ⌣ ψ` term is transported by the vendored degree cast
`cochainCast`. Downstream code must route every such mismatch through
`cochainCast`, never through rewriting a `ℕ` inside the dependent type.
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.AlgTop

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Elementary facts about the vendored degree cast -/

/-- The degree cast of the zero cochain is zero. -/
@[simp]
theorem cochainCast_zero {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    cochainCast (R := R) (Z := Z) h 0 = 0 := by
  unfold cochainCast
  simp

/-- The degree cast is additive. -/
theorem cochainCast_add {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ ψ : singularCochainGroup R Z m) :
    cochainCast h (φ + ψ) = cochainCast h φ + cochainCast h ψ := by
  unfold cochainCast
  simp

/-- The degree cast is `R`-linear. -/
theorem cochainCast_smul {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (s : R) (φ : singularCochainGroup R Z m) :
    cochainCast h (s • φ) = s • cochainCast h φ := by
  unfold cochainCast
  simp

/-! ## 2. The signed splitting lemma

This is `sum_split_char2` of the vendored `AlexanderWhitneyChainMap` with its
characteristic-two hypothesis removed: instead of asking that the two endpoint
terms be equal (so that `x + x = 0` kills them), we ask that they be negatives of
each other, which is what the Koszul signs actually deliver. -/

/-- **Signed front/back sum split.** Let `L` be a function on `Fin (p+q+2)` that
matches `A : Fin (p+2) → M` on the front block `k ≤ p` and matches
`B : Fin (q+2) → M` (reindexed by `k - p`) on the back block `k > p`. If the two
endpoint values `A (Fin.last (p+1))` and `B 0` are negatives of each other, then

```text
∑ k, L k = (∑ i, A i) + ∑ j, B j.
```

The front block of `L` accounts for the first `p+1` terms of `∑ A` and the back
block for the last `q+1` terms of `∑ B`; the two leftover endpoint terms cancel. -/
theorem sum_split_signed {M : Type} [AddCommGroup M]
    (p q : ℕ) (L : Fin (p + q + 2) → M) (A : Fin (p + 2) → M) (B : Fin (q + 2) → M)
    (hle : ∀ k : Fin (p + q + 2), (hk : k.val ≤ p) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (p + q + 2), (hk : p < k.val) → L k = B ⟨k.val - p, by
      have := k.isLt; omega⟩)
    (hend : A (Fin.last (p + 1)) = - B 0) :
    ∑ k, L k = (∑ i, A i) + ∑ j, B j := by
  rw [Fin.sum_univ_castSucc (n := p + 1) A, Fin.sum_univ_succ (n := q + 1) B]
  set e : Fin (p + 1) ⊕ Fin (q + 1) ≃ Fin (p + q + 2) :=
    finSumFinEquiv.trans (finCongr (by omega)) with he
  have hsum : ∑ k, L k = ∑ s, L (e s) := (Equiv.sum_comp e L).symm
  rw [hsum, Fintype.sum_sum_type]
  have hL : ∑ a₁ : Fin (p + 1), L (e (Sum.inl a₁)) = ∑ i : Fin (p + 1), A i.castSucc := by
    apply Finset.sum_congr rfl; intro i _
    have hval : (e (Sum.inl i)).val = i.val := by
      simp [he, finSumFinEquiv_apply_left, Fin.castAdd, Fin.castLE]
    rw [hle (e (Sum.inl i)) (by rw [hval]; omega)]
    apply congrArg A; apply Fin.ext; simp [hval, Fin.castSucc, Fin.castAdd, Fin.castLE]
  have hR : ∑ a₂ : Fin (q + 1), L (e (Sum.inr a₂)) = ∑ j : Fin (q + 1), B j.succ := by
    apply Finset.sum_congr rfl; intro j _
    have hval : (e (Sum.inr j)).val = p + 1 + j.val := by
      simp [he, finSumFinEquiv_apply_right, Fin.natAdd]
    rw [hgt (e (Sum.inr j)) (by rw [hval]; omega)]
    apply congrArg B; apply Fin.ext; simp only [hval, Fin.val_succ]; omega
  rw [hL, hR, hend]
  abel

/-! ## 3. The Leibniz identity over an arbitrary coefficient ring -/

/-- **Alexander–Whitney cochain Leibniz identity, arbitrary coefficients.**

The cochain coboundary is a graded derivation for the cup product:

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ.
```

This is the chain-map identity that lets the cup product descend to cohomology.
The `δφ ⌣ ψ` term, naturally of degree `(p+1)+q`, and the `φ ⌣ δψ` term, of
degree `p+(q+1)`, are transported to degree `(p+q)+1` via `cochainCast`.

The proof is the classical telescoping argument. Writing the coboundary as the
alternating sum over boundary faces and splitting the index by its position
relative to the cup split point `p`:

* for `k ≤ p` the `k`-th face acts on the front simplex only, matching the
  `k`-th term of `δφ ⌣ ψ`;
* for `k > p` it acts on the back simplex only, matching the `(k-p)`-th term of
  `φ ⌣ δψ` after the global sign `(-1)^p`;
* the two leftover endpoint terms — the top face of the front block and the
  bottom face of the back block — restrict to the *same* pair of simplices and
  carry the opposite signs `(-1)^{p+1}` and `(-1)^p`, so they cancel. -/
theorem aw_cochain_leibniz (R : Type) [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q) :
    cochainCoboundary R X (p + q) (cochainCup p q φ ψ)
      = cochainCast (aw_degree_left_succ p q)
            (cochainCup (p + 1) q (cochainCoboundary R X p φ) ψ)
        + ((-1 : R) ^ p) • cochainCast (aw_degree_right_succ p q)
            (cochainCup p (q + 1) φ (cochainCoboundary R X q ψ)) := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, cochainEval_smul]
  rw [show cochainEval (p + q + 1)
        (cochainCoboundary R X (p + q) (cochainCup p q φ ψ)) σ
      = ∑ k : Fin (p + q + 2), (-1 : R) ^ (k : ℕ) *
          (cochainEval p φ (frontSimplex X p q (faceSimplex X (p + q) k σ))
            * cochainEval q ψ (backSimplex X p q (faceSimplex X (p + q) k σ))) from ?_]
  · rw [show cochainEval (p + q + 1) (cochainCast (aw_degree_left_succ p q)
            (cochainCup (p + 1) q (cochainCoboundary R X p φ) ψ)) σ
        = ∑ i : Fin (p + 2), (-1 : R) ^ (i : ℕ) *
            (cochainEval p φ
                (faceSimplex X p i (frontSimplex X (p + 1) q (awCastSimplex X p q σ)))
              * cochainEval q ψ (backSimplex X (p + 1) q (awCastSimplex X p q σ))) from ?_]
    · rw [show (-1 : R) ^ p * cochainEval (p + q + 1) (cochainCast (aw_degree_right_succ p q)
              (cochainCup p (q + 1) φ (cochainCoboundary R X q ψ))) σ
          = ∑ j : Fin (q + 2), (-1 : R) ^ (p + (j : ℕ)) *
              (cochainEval p φ (frontSimplex X p (q + 1) σ)
                * cochainEval q ψ (faceSimplex X q j (backSimplex X p (q + 1) σ))) from ?_]
      · apply sum_split_signed
        · intro k hk
          rw [frontSimplex_faceSimplex_of_le X p q k hk, backSimplex_faceSimplex_of_le X p q k hk]
        · intro k hk
          rw [frontSimplex_faceSimplex_of_gt X p q k hk, backSimplex_faceSimplex_of_gt X p q k hk]
          have hidx : p + ((⟨(k : ℕ) - p, by have := k.isLt; omega⟩ : Fin (q + 2)) : ℕ)
              = (k : ℕ) := by
            show p + ((k : ℕ) - p) = (k : ℕ)
            omega
          rw [hidx]
        · rw [frontSimplex_faceSimplex_endpoint X p q, backSimplex_faceSimplex_endpoint X p q]
          have hlast : ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) = p + 1 := rfl
          have hzero : ((0 : Fin (q + 2)) : ℕ) = 0 := rfl
          rw [hlast, hzero, add_zero, pow_succ]
          ring
      · rw [cochainCast_eval_right, cochainCup_eval, cochainCoboundary_eval, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_add]
        ring
    · rw [cochainCast_eval_awCastSimplex, cochainCup_eval, cochainCoboundary_eval,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  · rw [cochainCoboundary_eval]
    apply Finset.sum_congr rfl
    intro k _
    rw [cochainCup_eval]

/-! ## 4. Consequences used by the cohomology descent -/

/-- **The cup product of two cocycles is a cocycle.** -/
theorem cochainCup_cocycle {R : Type} [CommRing R] {X : TopCat.{0}} {p q : ℕ}
    {φ : singularCochainGroup R X p} {ψ : singularCochainGroup R X q}
    (hφ : cochainCoboundary R X p φ = 0) (hψ : cochainCoboundary R X q ψ = 0) :
    cochainCoboundary R X (p + q) (cochainCup p q φ ψ) = 0 := by
  rw [aw_cochain_leibniz R p q φ ψ, hφ, hψ, cochainCup_zero_left, cochainCup_zero_right,
    cochainCast_zero, cochainCast_zero, smul_zero, add_zero]

/-- **A coboundary cupped with a cocycle is a coboundary.** Concretely, if `ψ` is
a cocycle then `δα ⌣ ψ` is, up to the degree cast, `δ(α ⌣ ψ)`. -/
theorem cochainCup_coboundary_left {R : Type} [CommRing R] {X : TopCat.{0}} {m q : ℕ}
    (α : singularCochainGroup R X m) {ψ : singularCochainGroup R X q}
    (hψ : cochainCoboundary R X q ψ = 0) :
    cochainCast (aw_degree_left_succ m q)
        (cochainCup (m + 1) q (cochainCoboundary R X m α) ψ)
      = cochainCoboundary R X (m + q) (cochainCup m q α ψ) := by
  rw [aw_cochain_leibniz R m q α ψ, hψ, cochainCup_zero_right, cochainCast_zero, smul_zero,
    add_zero]

/-- **A cocycle cupped with a coboundary is a coboundary.** If `φ` is a cocycle
then `(-1)^p φ ⌣ δβ` is, up to the degree cast, `δ(φ ⌣ β)`. -/
theorem cochainCup_coboundary_right {R : Type} [CommRing R] {X : TopCat.{0}} {p m : ℕ}
    {φ : singularCochainGroup R X p} (β : singularCochainGroup R X m)
    (hφ : cochainCoboundary R X p φ = 0) :
    ((-1 : R) ^ p) • cochainCast (aw_degree_right_succ p m)
        (cochainCup p (m + 1) φ (cochainCoboundary R X m β))
      = cochainCoboundary R X (p + m) (cochainCup p m φ β) := by
  rw [aw_cochain_leibniz R p m φ β, hφ, cochainCup_zero_left, cochainCast_zero, zero_add]

end GroupApproximation.AlgTop
