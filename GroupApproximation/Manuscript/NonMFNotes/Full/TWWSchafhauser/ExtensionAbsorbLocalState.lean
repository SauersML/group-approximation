import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbLocalCone

/-!
# Excisable states and state-compressible lifts

Lane `TWWSch3c2C2`, work order `WO-TWWSch-3c2-C2`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), absorption step. Sources: C. A. Akemann,
J. Anderson and G. K. Pedersen, *Excising states of C*-algebras*, Canad. J. Math. 38 (1986),
Prop. 2.3 (pure states are excisable); G. A. Elliott and D. Kucerovsky, Pacific J. Math. 198
(2001), Lemma 7.

* `IsExcisableState ω`: for every finite `F ⊆ S` and `ε > 0` there is `c` of norm one with
  `‖c⋆ s c − ω(s) c⋆ c‖ ≤ ε` on `F`. Akemann--Anderson--Pedersen show that every pure state
  is excisable (with `c` positive). The property already forces `ω(1) = 1`
  (`IsExcisableState.map_one`).
* `stateMatrixMap ω y b : s ↦ ∑ᵢ ∑ⱼ ω(yᵢ⋆ s yⱼ) bᵢ⋆ bⱼ`, the building blocks of a completely
  positive map into the compacts (Elliott--Kucerovsky, proof of Lemma 7).
* `IsStateCompressible ℓ`: every such block with excisable `ω` and compact `bᵢ` is locally
  compressible into `ℓ`, in the sense of `ExtensionAbsorbLocalCone`.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

variable {S : Type} [CStarAlgebra S]

/-- An **excisable state**: for all finite `F` and `ε > 0` there is `c` with `‖c‖ = 1` and
`‖c⋆ s c − ω(s) c⋆ c‖ ≤ ε` for `s ∈ F` (Akemann--Anderson--Pedersen 1986, Prop. 2.3;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def IsExcisableState (ω : S →ₗ[ℂ] ℂ) : Prop :=
  ∀ (F : Finset S) (ε : ℝ), 0 < ε → ∃ c : S, ‖c‖ = 1 ∧
    ∀ s ∈ F, ‖star c * s * c - ω s • (star c * c)‖ ≤ ε

/-- An excisable functional is unital (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem IsExcisableState.map_one {ω : S →ₗ[ℂ] ℂ} (hω : IsExcisableState ω) : ω 1 = 1 := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨c, hc, h⟩ := hω {1} ε hε
  have h1 := h 1 (Finset.mem_singleton_self 1)
  have e : star c * 1 * c - ω 1 • (star c * c) = (1 - ω 1) • (star c * c) := by
    rw [mul_one, sub_smul, one_smul]
  rw [e, norm_smul, CStarRing.norm_star_mul_self, hc] at h1
  rw [dist_eq_norm, norm_sub_rev]
  linarith

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The block `s ↦ ∑ᵢ ∑ⱼ ω(yᵢ⋆ s yⱼ) bᵢ⋆ bⱼ` (Elliott--Kucerovsky 2001, proof of Lemma 7;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def stateMatrixMap {ι : Type} [Fintype ι] (ω : S →ₗ[ℂ] ℂ) (y : ι → S) (b : ι → StdBdd J) :
    S → StdBdd J :=
  fun s => ∑ i, ∑ j, ω (star (y i) * s * y j) • (star (b i) * b j)

/-- `ℓ` is **state-compressible**: every block `stateMatrixMap ω y b` with `ω` excisable and
all `bᵢ` compact is locally compressible into `ℓ` (Elliott--Kucerovsky 2001, Lemma 7;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def IsStateCompressible (ℓ : S → StdBdd J) : Prop :=
  ∀ ω : S →ₗ[ℂ] ℂ, IsExcisableState ω → ∀ {ι : Type} [Fintype ι] (y : ι → S)
    (b : ι → StdBdd J), (∀ i, IsStdCompact (b i)) → IsLocallyCompressible ℓ (stateMatrixMap ω y b)

/-- Finite sums of blocks are compressible into a state-compressible lift
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsStateCompressible.sum {ℓ : S → StdBdd J} (hℓ : IsStateCompressible ℓ)
    {κ : Type} (t : Finset κ) {ι : Type} [Fintype ι] (ω : κ → S →ₗ[ℂ] ℂ)
    (hω : ∀ m ∈ t, IsExcisableState (ω m)) (y : κ → ι → S) (b : κ → ι → StdBdd J)
    (hb : ∀ m ∈ t, ∀ i, IsStdCompact (b m i)) :
    IsLocallyCompressible ℓ (fun s => ∑ m ∈ t, stateMatrixMap (ω m) (y m) (b m) s) :=
  isLocallyCompressible_sum t fun m hm => hℓ (ω m) (hω m hm) (y m) (b m) (hb m hm)

end

end GroupApproximation.Full.TWWSchafhauser
