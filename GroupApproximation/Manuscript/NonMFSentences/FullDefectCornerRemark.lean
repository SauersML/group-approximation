import GroupApproximation.Algebra.CornerRing
import GroupApproximation.Leavitt.AryLeavitt
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingFullIdeal
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The remark after `thm:full-defect-ring`: the non-MF conclusion passes up from corners

`non_mf_groups_exist.tex`, tex lines 1008-1014 at origin/main `73c867c5b`:

> The non-MF conclusion passes up from corners: if a nonzero idempotent `p ∈ R`
> is such that the ring `pRp`, with unit `p`, satisfies the hypothesis, then
> `A ↦ A + (1-p)I_n` embeds `EL_n(pRp)` in `EL_n(R)`, and restricting models
> shows that MF passes to subgroups, so `EL_n(R)` is not MF for every `n ≥ 2`.
> The full-defect hypothesis itself need not pass to `R`, nor need every
> homomorphism from `EL_n(R)` to an MF group be trivial.

The census had graded both sentences `formalized` by citing the `Prop`
definitions `PrintedSimpleInfiniteRingRankTwo` and
`PrintedFullComplementaryIdempotentsRankTwo`, neither of which mentions a corner.
This module carries them:

* `cornerMatrixHom` is the printed map `A ↦ A + (1-p)I_n` on `M_n(pRp)`, a monoid
  homomorphism into `M_n(R)` because the entries of `A` are killed by `1-p` on both
  sides; `cornerElementaryHom` is its restriction `EL_n(pRp) → EL_n(R)`, and it is
  injective (`cornerElementaryHom_injective`);
* `isOperatorMF_of_injective'` is "restricting models shows that MF passes to
  subgroups";
* `manuscriptSentence_cornerPassesUp` is the first sentence at every `n ≥ 2`;
* `manuscriptSentence_hypothesisNeedNotPass` is the second sentence, witnessed by
  `R = L_{𝔽₂}(1,2) × 𝔽₂` and `p = (1,0)`: the corner is `L_{𝔽₂}(1,2)`, which
  satisfies the hypothesis; `R` does not, since `ts = 1` forces `st = 1` in the
  commutative factor; and `EL_n(R) → EL_n(𝔽₂)` is a nontrivial homomorphism to a
  finite, hence MF, group.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace FullDefectCornerRemark

open GroupApproximation.MFQuotientUnits

/-- The printed hypothesis of `thm:full-defect-ring` on the pair: `ts = 1` and
`1 = ∑ⱼ aⱼ(1-st)bⱼ` for finitely many `aⱼ, bⱼ` (countability is carried
separately, as an instance). -/
def FullDefectPair (A : Type*) [Ring A] : Prop :=
  ∃ s t : A, t * s = 1 ∧ ∃ (m : ℕ) (a b : Fin m → A), ∑ k, a k * (1 - s * t) * b k = 1

section CornerMatrix

variable {R : Type*} [Ring R] (p : R) (hp : IsIdempotentElem p)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem corner_mul_one_sub (x : Corner R p hp) : (x : R) * (1 - p) = 0 := by
  rw [mul_sub, mul_one, x.2.2, sub_self]

theorem one_sub_mul_corner (x : Corner R p hp) : (1 - p) * (x : R) = 0 := by
  rw [sub_mul, one_mul, x.2.1, sub_self]

/-- **The printed map `A ↦ A + (1-p)I_n`**, from `M_n(pRp)` to `M_n(R)`. -/
def cornerMatrixMap (A : Matrix ι ι (Corner R p hp)) : Matrix ι ι R :=
  A.map (fun x : Corner R p hp ↦ (x : R)) + Matrix.diagonal (fun _ ↦ 1 - p)

omit [DecidableEq ι] in
theorem map_coe_mul (A B : Matrix ι ι (Corner R p hp)) :
    (A * B).map (fun x : Corner R p hp ↦ (x : R))
      = A.map (fun x : Corner R p hp ↦ (x : R)) * B.map (fun x : Corner R p hp ↦ (x : R)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  exact map_sum (cornerInclusion p hp) (fun k ↦ A i k * B k j) Finset.univ

theorem map_coe_mul_diagonal (A : Matrix ι ι (Corner R p hp)) :
    A.map (fun x : Corner R p hp ↦ (x : R)) * Matrix.diagonal (fun _ ↦ 1 - p) = 0 := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.zero_apply]
  exact corner_mul_one_sub p hp (A i j)

theorem diagonal_mul_map_coe (A : Matrix ι ι (Corner R p hp)) :
    Matrix.diagonal (fun _ ↦ 1 - p) * A.map (fun x : Corner R p hp ↦ (x : R)) = 0 := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.map_apply, Matrix.zero_apply]
  exact one_sub_mul_corner p hp (A i j)

omit [Fintype ι] in
theorem cornerMatrixMap_one : cornerMatrixMap p hp (1 : Matrix ι ι (Corner R p hp)) = 1 := by
  ext i j
  simp only [cornerMatrixMap, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  split_ifs with h
  · rw [coe_cornerOne]
    abel
  · simp

theorem cornerMatrixMap_mul (A B : Matrix ι ι (Corner R p hp)) :
    cornerMatrixMap p hp (A * B) = cornerMatrixMap p hp A * cornerMatrixMap p hp B := by
  simp only [cornerMatrixMap]
  rw [map_coe_mul, add_mul, mul_add, mul_add, map_coe_mul_diagonal, diagonal_mul_map_coe,
    Matrix.diagonal_mul_diagonal, (IsIdempotentElem.one_sub hp).eq, add_zero, zero_add]

/-- The printed map as a monoid homomorphism `M_n(pRp) → M_n(R)`. -/
def cornerMatrixHom : Matrix ι ι (Corner R p hp) →* Matrix ι ι R where
  toFun := cornerMatrixMap p hp
  map_one' := cornerMatrixMap_one p hp
  map_mul' := cornerMatrixMap_mul p hp

omit [Fintype ι] in
theorem cornerMatrixMap_elementary (i j : ι) (hij : i ≠ j) (a : Corner R p hp) :
    cornerMatrixMap p hp (1 + Matrix.single i j a) = 1 + Matrix.single i j (a : R) := by
  ext k l
  simp only [cornerMatrixMap, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.diagonal_apply, coe_corner_add]
  split_ifs <;> simp_all

theorem cornerUnits_elementaryUnit (i j : ι) (hij : i ≠ j) (a : Corner R p hp) :
    Units.map (cornerMatrixHom p hp) (elementaryUnit i j hij a)
      = elementaryUnit i j hij (a : R) := by
  apply Units.ext
  exact cornerMatrixMap_elementary p hp i j hij a

theorem elementaryGroup_map_corner_le :
    (elementaryGroup ι (Corner R p hp)).map (Units.map (cornerMatrixHom p hp))
      ≤ elementaryGroup ι R := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change Units.map (cornerMatrixHom p hp) (elementaryUnit i j hij a) ∈ elementaryGroup ι R
  rw [cornerUnits_elementaryUnit]
  exact elementaryUnit_mem i j hij (a : R)

/-- **`EL_n(pRp) → EL_n(R)`, `A ↦ A + (1-p)I_n`.** -/
def cornerElementaryHom : elementaryGroup ι (Corner R p hp) →* elementaryGroup ι R :=
  ((Units.map (cornerMatrixHom p hp)).comp (elementaryGroup ι (Corner R p hp)).subtype).codRestrict
    (elementaryGroup ι R) fun g ↦
      elementaryGroup_map_corner_le p hp
        (Subgroup.apply_coe_mem_map (Units.map (cornerMatrixHom p hp))
          (elementaryGroup ι (Corner R p hp)) g)

theorem cornerElementaryHom_val (g : elementaryGroup ι (Corner R p hp)) :
    (((cornerElementaryHom p hp g : elementaryGroup ι R) : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((g : (Matrix ι ι (Corner R p hp))ˣ) : Matrix ι ι (Corner R p hp)).map
          (fun x : Corner R p hp ↦ (x : R)) + Matrix.diagonal (fun _ ↦ 1 - p) := rfl

/-- **The printed map embeds `EL_n(pRp)` in `EL_n(R)`.** -/
theorem cornerElementaryHom_injective :
    Function.Injective (cornerElementaryHom (ι := ι) p hp) := by
  intro g h hgh
  have hval := congrArg
    (fun z : elementaryGroup ι R ↦ ((z : (Matrix ι ι R)ˣ) : Matrix ι ι R)) hgh
  simp only [cornerElementaryHom_val, add_left_inj] at hval
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun hval i) j
  simp only [Matrix.map_apply] at hij
  exact hij

end CornerMatrix

/-- **"restricting models shows that MF passes to subgroups"**: an injective
homomorphism into an MF group pulls the models back. -/
theorem isOperatorMF_of_injective' {G M : Type} [Group G] [Group M]
    (φ : G →* M) (hφ : Function.Injective φ) (hM : IsOperatorMF M) :
    IsOperatorMF G := by
  obtain ⟨X, hX, rho, hrho⟩ := hM
  exact ⟨X, hX, rho.comp φ, hrho.comp hφ⟩

/-- **Printed (tex 1008-1012).**  "The non-MF conclusion passes up from corners: if
a nonzero idempotent `p ∈ R` is such that the ring `pRp`, with unit `p`, satisfies
the hypothesis, then `A ↦ A + (1-p)I_n` embeds `EL_n(pRp)` in `EL_n(R)`, and
restricting models shows that MF passes to subgroups, so `EL_n(R)` is not MF for
every `n ≥ 2`." -/
def PrintedCornerPassesUp : Prop :=
  ∀ (R : Type) [Ring R] (p : R) (hp : IsIdempotentElem p), p ≠ 0 →
    Countable (Corner R p hp) → FullDefectPair (Corner R p hp) →
      (∀ n : ℕ, Function.Injective (cornerElementaryHom (ι := Fin n) p hp)) ∧
      ∀ n : ℕ, 2 ≤ n → ¬ IsOperatorMF (elementaryGroup (Fin n) R)

theorem manuscriptSentence_cornerPassesUp : PrintedCornerPassesUp := by
  intro R _ p hp hp0 hcount hpair
  haveI := hcount
  refine ⟨fun _ ↦ cornerElementaryHom_injective p hp, fun n hn hMF ↦ ?_⟩
  obtain ⟨s, t, hts, hfull⟩ := hpair
  haveI : Nontrivial (Corner R p hp) := corner_nontrivial p hp hp0
  have hcornerMF : IsOperatorMF (elementaryGroup (Fin n) (Corner R p hp)) :=
    isOperatorMF_of_injective' (cornerElementaryHom p hp) (cornerElementaryHom_injective p hp) hMF
  have htriv :=
    GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
      (Corner R p hp) s t hts hfull n hn (elementaryGroup (Fin n) (Corner R p hp)) hcornerMF
      (MonoidHom.id _)
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hroot : elementaryRoot (R := Corner R p hp) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne 1
      ≠ 1 := by
    intro h
    have hval : elementaryUnit (R := Corner R p hp) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne 1
        = elementaryUnit (R := Corner R p hp) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (elementaryUnit_injective _ _ hne hval)
  exact hroot (htriv _)

/-- The corner element `(x, 0)` of `A × 𝔽₂` at `p = (1, 0)`. -/
def cornerElt {A : Type*} [Ring A] (hp : IsIdempotentElem ((1, 0) : A × ZMod 2)) (x : A) :
    Corner (A × ZMod 2) (1, 0) hp :=
  ⟨(x, 0), mem_cornerNonUnitalSubring_iff.mpr ⟨by simp, by simp⟩⟩

@[simp] theorem coe_cornerElt {A : Type*} [Ring A] (hp : IsIdempotentElem ((1, 0) : A × ZMod 2))
    (x : A) : ((cornerElt hp x : Corner (A × ZMod 2) (1, 0) hp) : A × ZMod 2) = (x, 0) := rfl

/-- **Printed (tex 1012-1014).**  "The full-defect hypothesis itself need not pass to
`R`, nor need every homomorphism from `EL_n(R)` to an MF group be trivial."

Witness: `R = L_{𝔽₂}(1,2) × 𝔽₂`, `p = (1,0)`. -/
theorem manuscriptSentence_hypothesisNeedNotPass :
    ∃ (hp : IsIdempotentElem ((1, 0) : AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2)),
      ((1, 0) : AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) ≠ 0 ∧
      Countable (Corner (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) (1, 0) hp) ∧
      FullDefectPair (Corner (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) (1, 0) hp) ∧
      ¬ FullDefectPair (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsOperatorMF (elementaryGroup (Fin n) (ZMod 2)) ∧
        ∃ f : elementaryGroup (Fin n) (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) →*
            elementaryGroup (Fin n) (ZMod 2), f ≠ 1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hp : IsIdempotentElem ((1, 0) : AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) := by
    simp [IsIdempotentElem]
  refine ⟨hp, ?_, inferInstance, ?_, ?_, fun n hn ↦ ?_⟩
  · intro h
    exact one_ne_zero (congrArg Prod.fst h)
  · -- the corner is `L_{𝔽₂}(1,2)`, with its printed pair `s = s₁`, `t = t₁`
    obtain ⟨hts, m, a, b, hab⟩ :=
      GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing.completeMatrixFamily_full
        (AryLeavitt.family (ZMod 2) 2) h01
    refine ⟨cornerElt hp ((AryLeavitt.family (ZMod 2) 2).left 0),
      cornerElt hp ((AryLeavitt.family (ZMod 2) 2).right 0), ?_,
      m, fun k ↦ cornerElt hp (a k), fun k ↦ cornerElt hp (b k), ?_⟩
    · apply Subtype.ext
      simp [hts]
    · apply Subtype.ext
      have hcoe : ∀ k, ((cornerElt hp (a k) *
            (1 - cornerElt hp ((AryLeavitt.family (ZMod 2) 2).left 0) *
              cornerElt hp ((AryLeavitt.family (ZMod 2) 2).right 0)) *
            cornerElt hp (b k) : Corner _ (1, 0) hp) :
              AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2)
          = (a k * (1 - (AryLeavitt.family (ZMod 2) 2).left 0 *
              (AryLeavitt.family (ZMod 2) 2).right 0) * b k, 0) := by
        intro k
        simp
      have hsum := map_sum (cornerInclusion _ hp)
        (fun k ↦ cornerElt hp (a k) *
            (1 - cornerElt hp ((AryLeavitt.family (ZMod 2) 2).left 0) *
              cornerElt hp ((AryLeavitt.family (ZMod 2) 2).right 0)) *
            cornerElt hp (b k)) Finset.univ
      simp only [cornerInclusion_apply] at hsum
      rw [hsum, coe_cornerOne]
      simp only [hcoe]
      refine Prod.ext ?_ ?_
      · simpa [Prod.fst_sum] using hab
      · simp [Prod.snd_sum]
  · rintro ⟨s, t, hts, m, a, b, hab⟩
    have h2 : t.2 * s.2 = 1 := by simpa using congrArg Prod.snd hts
    have h2' : s.2 * t.2 = 1 := by rw [mul_comm]; exact h2
    have hsum := congrArg Prod.snd hab
    simp only [Prod.snd_sum, Prod.snd_mul, Prod.snd_sub, Prod.snd_one, h2', sub_self,
      mul_zero, zero_mul, Finset.sum_const_zero] at hsum
    exact absurd hsum (by decide)
  · refine ⟨isOperatorMF_of_locallyFinite (isLocallyFiniteGroup_of_finite _),
      elementaryGroupMap (RingHom.snd _ (ZMod 2)), ?_⟩
    intro h
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h'
      exact absurd (congrArg Fin.val h') (by norm_num)
    have h1 := congrArg
      (fun φ : elementaryGroup (Fin n) (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2 × ZMod 2) →*
          elementaryGroup (Fin n) (ZMod 2) ↦
        ((φ (elementaryRoot (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne 1) :
          elementaryGroup (Fin n) (ZMod 2)) : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ)) h
    simp only [MonoidHom.one_apply, elementaryGroupMap_apply, elementaryRoot_val,
      elementaryMatrixUnitMap_elementaryUnit, map_one, OneMemClass.coe_one] at h1
    rw [← elementaryUnit_zero (R := ZMod 2) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne] at h1
    exact absurd (elementaryUnit_injective _ _ hne h1) (by decide)

end FullDefectCornerRemark
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.FullDefectCornerRemark

#audit_axioms cornerElementaryHom_injective
#audit_axioms isOperatorMF_of_injective'
#audit_closed_axioms manuscriptSentence_cornerPassesUp
#audit_closed_axioms manuscriptSentence_hypothesisNeedNotPass
