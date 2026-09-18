import GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsionAllCharacteristics
import GroupApproximation.Dynamics.ClopenSwapInvolution
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Every example above has torsion (tex 292)

`non_mf_groups_exist.tex`, line 292:

> Every example above has torsion, and in the lamp construction the
> obstruction is itself a torsion element.

## Proof route

The closed statement
`NonMFSentences.IntroExamplesTorsion.PrintedIntroExamplesTorsionAllCharacteristics`
(`printedIntroExamplesTorsionAllCharacteristics`) covers the unit group of `L_{𝔽₂}(1,2)`,
`GL_n` over purely infinite simple rings, the unit groups of `L_k(1,d)`, `EL_n(R)` over every
nonzero ring (the Weyl element `e₁₂(1)e₂₁(-1)e₁₂(1)` has order dividing `4`), the witness `W`,
and the lamp obstruction: the central sign of every Clifford witness is a nontrivial involution
killed by every MF target.

The introduction also lists the crossed products `R_X = LC(X, 𝔽) ⋊_T ℤ` (tex 249–259): `GL_n(R_X)`,
`EL_n(R_X)` and, for aperiodic `T`, the unit group `R_X^×`.  This module adds the torsion element of
`R_X^×`: if `T x ≠ x`, a clopen `V ∋ x` with `T x ∉ V` gives the clopen `A = V ∩ T⁻¹(Vᶜ)` with
`A ∩ T(A) = ∅`, and `ClopenCrossedProduct.exists_swapUnit` yields a unit `w` with `w⁻¹ = w` and
`w 1_A w⁻¹ = 1_{T(A)}`.  Hence `w² = 1`, and `w ≠ 1` because `1_A ≠ 1_{T(A)}` (evaluate at `x`,
using `ClopenCrossedProduct.coeff_injective`).  The nontrivial unit also shows `R_X ≠ 0`, so the
elementary torsion applies to `EL_n(R_X) ≤ GL_n(R_X)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroAmenable

/-- A point moved by `T` gives a nontrivial involution in the unit group of `R_X`. -/
theorem exists_unit_sq_eq_one_of_apply_ne {X : Type} [TopologicalSpace X]
    [TotallySeparatedSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] [Nontrivial k] (x : X)
    (hx : T x ≠ x) :
    ∃ g : (GroupApproximation.ClopenCrossedProduct T k)ˣ, g ≠ 1 ∧ g ^ 2 = 1 := by
  obtain ⟨V, hV, hxV, hTxV⟩ := exists_isClopen_of_totally_separated hx.symm
  have hA : IsClopen (V ∩ ⇑T ⁻¹' Vᶜ) := hV.inter (hV.compl.preimage T.continuous)
  have hxA : x ∈ V ∩ ⇑T ⁻¹' Vᶜ := ⟨hxV, hTxV⟩
  have hdisj : Disjoint (V ∩ ⇑T ⁻¹' Vᶜ) (⇑(T ^ (1 : ℤ)) '' (V ∩ ⇑T ⁻¹' Vᶜ)) := by
    rw [Set.disjoint_left]
    rintro a haA ⟨b, hbA, rfl⟩
    rw [zpow_one] at haA
    exact absurd haA.1 hbA.2
  obtain ⟨w, hwinv, hconj, -⟩ := GroupApproximation.ClopenCrossedProduct.exists_swapUnit T k
    ({()} : Finset Unit) (fun _ => V ∩ ⇑T ⁻¹' Vᶜ) (fun _ => hA) (fun _ => (1 : ℤ))
    (fun i _ j _ hij => absurd (Subsingleton.elim i j) hij)
    (fun i _ j _ hij => absurd (Subsingleton.elim i j) hij)
    (fun _ _ _ _ => hdisj)
  have hinv : w⁻¹ = w := Units.ext hwinv
  refine ⟨w, ?_, ?_⟩
  · intro hw1
    have h1 := hconj () (Finset.mem_singleton_self ())
    rw [hw1, inv_one, Units.val_one, mul_one, one_mul] at h1
    have h2 := DFunLike.congr_fun (GroupApproximation.ClopenCrossedProduct.coeff_injective T k h1) x
    have hxB : x ∈ ⇑(T ^ (1 : ℤ)) '' (V ∩ ⇑T ⁻¹' Vᶜ) :=
      (LocallyConstant.charFn_eq_one k x
        (GroupApproximation.ClopenCrossedProduct.isClopen_image (T ^ (1 : ℤ)) hA)).mp
        (h2.symm.trans ((LocallyConstant.charFn_eq_one k x hA).mpr hxA))
    exact Set.disjoint_left.mp hdisj hxA hxB
  · calc w ^ 2 = w⁻¹ * w := by rw [pow_two, hinv]
      _ = 1 := inv_mul_cancel w

/-- **tex 292.**  Every example above has torsion, and in the lamp construction the obstruction is
itself a torsion element: the closed printed statement over all characteristics, together with the
crossed products `R_X` over a finite field for an aperiodic homeomorphism `T` of a compact
Hausdorff totally disconnected space: the unit group `R_X^×` and `EL_n(R_X) ≤ GL_n(R_X)`, `n ≥ 2`,
contain nontrivial elements of finite order. -/
theorem manuscriptSentence_everyExampleHasTorsion :
    GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.PrintedIntroExamplesTorsionAllCharacteristics ∧
      ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
        [Nonempty X] (T : X ≃ₜ X), (∀ (x : X) (j : ℕ), 0 < j → (⇑T)^[j] x ≠ x) →
        ∀ (k : Type) [Field k] [Finite k],
          (∃ g : (GroupApproximation.ClopenCrossedProduct T k)ˣ, g ≠ 1 ∧ IsOfFinOrder g) ∧
            ∀ n : ℕ, 2 ≤ n →
              ∃ g ∈ GroupApproximation.elementaryGroup (Fin n)
                (GroupApproximation.ClopenCrossedProduct T k), g ≠ 1 ∧ IsOfFinOrder g := by
  refine ⟨GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.printedIntroExamplesTorsionAllCharacteristics,
    ?_⟩
  intro X _ _ _ _ _ T hap k _ _
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : T x ≠ x := by
    have h := hap x 1 Nat.zero_lt_one
    rwa [Function.iterate_one] at h
  obtain ⟨w, hw1, hw2⟩ := exists_unit_sq_eq_one_of_apply_ne T k x hx
  haveI : Nontrivial (GroupApproximation.ClopenCrossedProduct T k) :=
    nontrivial_of_ne (w : GroupApproximation.ClopenCrossedProduct T k) 1
      (mt Units.val_eq_one.mp hw1)
  exact ⟨⟨w, hw1, isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, hw2⟩⟩, fun n hn =>
    GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.printedIntroExamplesTorsionAllCharacteristics.2
      (GroupApproximation.ClopenCrossedProduct T k) n hn⟩

end IntroAmenable
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.exists_unit_sq_eq_one_of_apply_ne
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_everyExampleHasTorsion
