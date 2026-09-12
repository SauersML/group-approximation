import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CochainCupLeibniz

/-!
# The Alexander–Whitney Leibniz identity over an arbitrary coefficient ring

The vendored cochain layer
(`ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`) is generic in the
coefficient ring `R` everywhere except in one theorem: the Leibniz identity
`aw_cochain_leibniz_zmod2` is proved only at `ZMod 2`, and its proof genuinely
uses `(-1 : ZMod 2) ^ k = 1` (through `neg_one_pow_zmod2` and through
`sum_split_char2`, whose cancellation hypothesis is `∀ x, x + x = 0`).

This file removes that restriction.  It proves, over any `[CommRing R]`, the
**signed** Leibniz identity

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p · (φ ⌣ δψ)        (φ of degree p)
```

and the descent consequences that the cohomology-level cup product needs.  The
sign never escapes this file: each consequence below is stated *without* a sign,
because in the right-hand variable the factor `(-1)^p` is absorbed into the
cochain being differentiated (`(-1)^p · (-1)^p = 1`).

Nothing in the vendored tree is edited; the `ZMod 2` declarations there are
untouched and remain the ones the `F₂` instance uses.

## Main declarations

* `sum_split_cancel` — the sign-tracked replacement for the vendored
  `sum_split_char2`: the hypothesis `A (last) = B 0` together with `x + x = 0`
  is replaced by the single hypothesis `A (last) + B 0 = 0`.
* `aw_cochain_leibniz` — the signed Leibniz identity over `[CommRing R]`.
* `cochainCup_respects_cocycles` — the cup of two cocycles is a cocycle.
* `cochainCup_coboundary_left'`, `cochainCup_coboundary_right'` — the cup of a
  coboundary with a cocycle is, up to the degree cast, the coboundary of an
  explicit cochain (sign-free: the right-hand version differentiates
  `(-1)^p • (φ ⌣ η)`).
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The sum-splitting lemma with cancelling endpoints -/

/-- **Sum split with cancelling endpoints.**  If a function `L` on `Fin (p+q+2)`
matches `A` on the front block `k ≤ p`, matches `B` on the back block `k > p`,
and the two endpoint terms `A (last)` and `B 0` cancel, then
`∑ L = ∑ A + ∑ B`.

This is the vendored `sum_split_char2` with its characteristic-two hypothesis
`∀ x, x + x = 0` and its endpoint hypothesis `A (last) = B 0` merged into the
single hypothesis `A (last) + B 0 = 0`, which is what the *signed* Leibniz
identity supplies (`(-1)^{p+1} + (-1)^p = 0`). -/
theorem sum_split_cancel {M : Type} [AddCommGroup M]
    (p q : ℕ) (L : Fin (p + q + 2) → M) (A : Fin (p + 2) → M) (B : Fin (q + 2) → M)
    (hle : ∀ k : Fin (p + q + 2), (hk : k.val ≤ p) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (p + q + 2), (hk : p < k.val) → L k = B ⟨k.val - p, by have := k.isLt; omega⟩)
    (hend : A (Fin.last (p + 1)) + B 0 = 0) :
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
  rw [hL, hR]
  have hrw : (∑ i : Fin (p + 1), A i.castSucc + A (Fin.last (p + 1)))
        + (B 0 + ∑ j : Fin (q + 1), B j.succ)
      = (∑ i : Fin (p + 1), A i.castSucc + ∑ j : Fin (q + 1), B j.succ)
        + (A (Fin.last (p + 1)) + B 0) := by abel
  rw [hrw, hend, add_zero]

/-! ## 2. The signed Leibniz identity -/

/-- **Alexander–Whitney cochain Leibniz identity over any commutative ring.**

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p · (φ ⌣ δψ)
```

for `φ` of degree `p`.  The `δφ ⌣ ψ` term, naturally of degree `(p+1)+q`, and
the `φ ⌣ δψ` term, of degree `p+(q+1)`, are transported to degree `(p+q)+1` via
the cochain degree cast.

At `R = ZMod 2` this specialises to the vendored `aw_cochain_leibniz_zmod2`
(where `(-1)^p = 1`); the vendored theorem is not used here and is not
disturbed. -/
theorem aw_cochain_leibniz {R : Type} [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q) :
    cochainCoboundary R X (p + q) (cochainCup p q φ ψ)
      = cochainCast (aw_degree_left_succ p q)
          (cochainCup (p + 1) q (cochainCoboundary R X p φ) ψ)
        + (-1 : R) ^ p • cochainCast (aw_degree_right_succ p q)
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
        = ∑ i : Fin (p + 2),
            ((-1 : R) ^ (i : ℕ) * cochainEval p φ
                (faceSimplex X p i (frontSimplex X (p + 1) q (awCastSimplex X p q σ))))
              * cochainEval q ψ (backSimplex X (p + 1) q (awCastSimplex X p q σ)) from ?_]
    · rw [show cochainEval (p + q + 1) (cochainCast (aw_degree_right_succ p q)
              (cochainCup p (q + 1) φ (cochainCoboundary R X q ψ))) σ
          = ∑ j : Fin (q + 2),
              cochainEval p φ (frontSimplex X p (q + 1) σ)
                * ((-1 : R) ^ (j : ℕ) *
                    cochainEval q ψ (faceSimplex X q j (backSimplex X p (q + 1) σ))) from ?_]
      · rw [Finset.mul_sum]
        refine sum_split_cancel p q _ _ _ ?_ ?_ ?_
        · intro k hk
          rw [frontSimplex_faceSimplex_of_le X p q k hk, backSimplex_faceSimplex_of_le X p q k hk]
          exact (mul_assoc _ _ _).symm
        · intro k hk
          rw [frontSimplex_faceSimplex_of_gt X p q k hk, backSimplex_faceSimplex_of_gt X p q k hk]
          have hs : (-1 : R) ^ (k : ℕ) = (-1 : R) ^ p * (-1 : R) ^ ((k : ℕ) - p) := by
            rw [← pow_add, Nat.add_sub_cancel' hk.le]
          rw [hs]; ring
        · rw [frontSimplex_faceSimplex_endpoint X p q, backSimplex_faceSimplex_endpoint X p q]
          simp only [Fin.val_last, Fin.val_zero, pow_zero, pow_succ, one_mul]
          ring
      · rw [cochainCast_eval_right, cochainCup_eval, cochainCoboundary_eval, Finset.mul_sum]
    · rw [cochainCast_eval_awCastSimplex, cochainCup_eval, cochainCoboundary_eval, Finset.sum_mul]
  · rw [cochainCoboundary_eval]
    apply Finset.sum_congr rfl; intro k _; rw [cochainCup_eval]

/-! ## 3. Descent consequences, sign-free

Each statement below is the exact analogue of the corresponding `ZMod 2`
statement in the vendored `CochainCupLeibniz.lean`; the Leibniz sign is absorbed
before it reaches the conclusion. -/

/-- **The cup of two cocycles is a cocycle.** -/
theorem cochainCup_respects_cocycles {R : Type} [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q)
    (hφ : cochainCoboundary R X p φ = 0) (hψ : cochainCoboundary R X q ψ = 0) :
    cochainCoboundary R X (p + q) (cochainCup p q φ ψ) = 0 := by
  rw [aw_cochain_leibniz, hφ, hψ, cochainCup_zero_left, cochainCup_zero_right,
    cochainCast_zero, cochainCast_zero, smul_zero, add_zero]

/-- **A coboundary cupped with a cocycle is a coboundary.**  If `δψ = 0` then
`δη ⌣ ψ` is, up to the degree cast, the coboundary of `η ⌣ ψ`.  No sign appears:
the `(-1)^p` term of the Leibniz identity is the one killed by `δψ = 0`. -/
theorem cochainCup_coboundary_left' {R : Type} [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (η : singularCochainGroup R X p) (ψ : singularCochainGroup R X q)
    (hψ : cochainCoboundary R X q ψ = 0) :
    cochainCup (p + 1) q (cochainCoboundary R X p η) ψ
      = cochainCast (aw_degree_left_succ p q).symm
          (cochainCoboundary R X (p + q) (cochainCup p q η ψ)) := by
  rw [aw_cochain_leibniz, hψ, cochainCup_zero_right, cochainCast_zero, smul_zero, add_zero,
    cochainCast_cast]

/-- **A cocycle cupped with a coboundary is a coboundary.**  If `δφ = 0` then
`φ ⌣ δη` is, up to the degree cast, the coboundary of `(-1)^p • (φ ⌣ η)`.  The
Leibniz sign is absorbed into the differentiated cochain, using `(-1)^{2p} = 1`,
so the statement itself carries no sign. -/
theorem cochainCup_coboundary_right' {R : Type} [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (η : singularCochainGroup R X q)
    (hφ : cochainCoboundary R X p φ = 0) :
    cochainCup p (q + 1) φ (cochainCoboundary R X q η)
      = cochainCast (aw_degree_right_succ p q).symm
          (cochainCoboundary R X (p + q) ((-1 : R) ^ p • cochainCup p q φ η)) := by
  have hsmul : cochainCoboundary R X (p + q) ((-1 : R) ^ p • cochainCup p q φ η)
      = (-1 : R) ^ p • cochainCoboundary R X (p + q) (cochainCup p q φ η) := by
    unfold cochainCoboundary
    exact map_smul _ _ _
  rw [hsmul, aw_cochain_leibniz, hφ, cochainCup_zero_left, cochainCast_zero, zero_add,
    smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, cochainCast_cast]

end

end GroupApproximation.CharClass
