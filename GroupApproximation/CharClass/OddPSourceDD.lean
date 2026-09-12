import GroupApproximation.CharClass.OddPSourceComplex

/-!
# `d ∘ d = 0` for the odd-primary source, assembled

`OddPSourceComplex.lean` proves the three cancellations; this file is the case
split that puts them together, in the same shape as
`CartanSourceComplex.wDiff_wDiff`.

Three branches, and only the third does any work:

* `n = 0` — the simplex has no boundary, so only resolution-then-resolution
  survives;
* `n = Fin.succ (Fin.last _)` — the `W`-index is already `0`, so only
  simplex-then-simplex survives;
* `n = Fin.succ (Fin.castSucc i)` — the interior case, where all four terms are
  present, two die on their own and the two mixed ones cancel against each other.

## The one place truncated subtraction has to be crossed

`(k + 1) - (Fin.succ i).val` and `k - i.val` are the same number, and the second
spelling is the one `oddDiffS` writes into its sign.  `Nat.sub` recurses on its
second argument, so `(k+1) - (i+1)` reduces to `Nat.pred ((k+1) - i)` and is
**not** syntactically `k - i`; `Nat.succ_sub_succ` is a theorem, not `rfl`.  It
is crossed once, in `oddScalar_junction`, and never inside a rewrite that also
has to match a module element.
-/

open CategoryTheory Simplicial

namespace GroupApproximation.CharClass

section

variable (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0})

/-- The two mixed scalars, added.  This is the whole odd-primary content of
`d ∘ d = 0`: the resolution scalar factors out and the two signs are consecutive
powers of `-1`. -/
theorem oddScalar_junction (k : ℕ) (i : Fin (k + 1)) :
    altCoeff (grS p) (grNorm p) ((k + 1) - (Fin.succ i).val)
        * ((-1 : GroupRingZMod p) ^ (k - i.val))
      + ((-1 : GroupRingZMod p) ^ ((k - i.val) + 1))
        * altCoeff (grS p) (grNorm p) (k - i.val) = 0 := by
  have hv : (Fin.succ i).val = i.val + 1 := Fin.val_succ i
  have hnum : (k + 1) - (Fin.succ i).val = k - i.val := by
    rw [hv]; omega
  rw [hnum]
  have := neg_one_pow_add_succ (R := GroupRingZMod p) (k - i.val)
  calc altCoeff (grS p) (grNorm p) (k - i.val) * ((-1 : GroupRingZMod p) ^ (k - i.val))
        + ((-1 : GroupRingZMod p) ^ ((k - i.val) + 1))
          * altCoeff (grS p) (grNorm p) (k - i.val)
      = altCoeff (grS p) (grNorm p) (k - i.val)
        * (((-1 : GroupRingZMod p) ^ (k - i.val))
            + ((-1 : GroupRingZMod p) ^ ((k - i.val) + 1))) := by ring
    _ = altCoeff (grS p) (grNorm p) (k - i.val) * 0 := by rw [this]
    _ = 0 := by ring

/-- **The chain-complex condition for `W ⊗ C(X)` at odd `p`.** -/
theorem oddDiff_oddDiff (k : ℕ) (q : WSIndex (k + 2) X) :
    oddDiff p data X k
        (oddDiff p data X (k + 1) (Finsupp.single q (1 : GroupRingZMod p))) = 0 := by
  obtain ⟨n, σ⟩ := q
  rw [oddDiff_single]
  show oddDiff p data X k (oddDiffGen p data X (k + 1) n σ) = 0
  rw [oddDiffGen, map_add]
  revert σ
  induction n using Fin.cases with
  | zero =>
      intro σ
      have hcs : oddDiffW p X (k + 1) (0 : Fin (k + 3)) σ
          = altCoeff (grS p) (grNorm p) ((k + 1) - (0 : Fin (k + 2)).val) •
              Finsupp.single (⟨0, σ⟩ : WSIndex (k + 1) X) 1 :=
        oddDiffW_castSucc p X (k + 1) 0 σ
      have h1 : oddDiff p data X k
            (Finsupp.single (⟨0, σ⟩ : WSIndex (k + 1) X) (1 : GroupRingZMod p))
          = oddDiffGen p data X k 0 σ := oddDiff_single p data X k ⟨0, σ⟩
      rw [hcs, oddDiffS_zero, map_zero, add_zero, map_smul, h1, oddDiffGen, smul_add,
        altCoeff_smul_oddDiffW, oddDiffS_zero, smul_zero, add_zero]
  | succ m =>
      induction m using Fin.lastCases with
      | last =>
          intro σ
          have hW : oddDiffW p X (k + 1) (Fin.succ (Fin.last (k + 1))) σ = 0 :=
            oddDiffW_last p X (k + 1) σ
          have hz : (fun τ : stdSimplexTop (Fin.last (k + 1)).val ⟶ X =>
              oddDiffW p X k (Fin.last (k + 1)) τ) = fun _ => (0 : OddWTensor p k X) :=
            funext (oddDiffW_last p X k)
          rw [hW, map_zero, zero_add, oddDiffS_succ, map_smul, oddDiff_lmapDomain,
            linearCombination_oddDiffS_bd, add_zero, hz, linearCombinationR_zero_fun,
            smul_zero]
      | cast i =>
          intro σ
          have hcs : oddDiffW p X (k + 1) (Fin.succ (Fin.castSucc i)) σ
              = altCoeff (grS p) (grNorm p) ((k + 1) - (Fin.succ i).val) •
                  Finsupp.single (⟨Fin.succ i, σ⟩ : WSIndex (k + 1) X) 1 :=
            oddDiffW_castSucc p X (k + 1) (Fin.succ i) σ
          have h1 : oddDiff p data X k
                (Finsupp.single (⟨Fin.succ i, σ⟩ : WSIndex (k + 1) X)
                  (1 : GroupRingZMod p))
              = oddDiffGen p data X k (Fin.succ i) σ :=
            oddDiff_single p data X k ⟨Fin.succ i, σ⟩
          have hS : oddDiff p data X k
                (oddDiffS p data X (k + 1) (Fin.succ (Fin.castSucc i)) σ)
              = ((-1 : GroupRingZMod p) ^ ((k - i.val) + 1)) •
                  (altCoeff (grS p) (grNorm p) (k - i.val) •
                    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
                      (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
                      (data.bd X i.val (Finsupp.single σ (1 : GroupRingZMod p)))) := by
            -- `oddDiffS_succ` leaves the simplex degree spelled
            -- `(Fin.castSucc i).val`, while `oddMixed_terms_eq` states it as
            -- `i.val`.  The number is inside the type of a `Finsupp`, so `rw`
            -- cannot cross it; the `have` states the LHS in the goal's spelling
            -- and the RHS in the one the next step wants, and defeq does the
            -- rest.
            have hmix : Finsupp.linearCombination (GroupRingZMod p)
                  (fun τ => oddDiffW p X k (Fin.castSucc i) τ)
                  (data.bd X (Fin.castSucc i).val
                    (Finsupp.single σ (1 : GroupRingZMod p)))
                = altCoeff (grS p) (grNorm p) (k - i.val) •
                    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
                      (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
                      (data.bd X i.val (Finsupp.single σ (1 : GroupRingZMod p))) :=
              oddMixed_terms_eq p data X k i σ
            rw [oddDiffS_succ, map_smul, oddDiff_lmapDomain,
              linearCombination_oddDiffS_bd, add_zero, hmix,
              altCoeff_succ_junction]
          rw [hcs, map_smul, h1, oddDiffGen, smul_add, altCoeff_smul_oddDiffW,
            zero_add, hS, oddDiffS_succ, smul_smul, smul_smul, ← add_smul,
            oddScalar_junction, zero_smul]

end

end GroupApproximation.CharClass
