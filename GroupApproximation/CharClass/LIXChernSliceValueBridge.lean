import GroupApproximation.CharClass.ChernOfInvariance
import GroupApproximation.CharClass.LIXChernSlice
import GroupApproximation.CharClass.LIXSliceEquation
import GroupApproximation.CharClass.LIXVBundle

/-!
# The restricted mapping torus and `V`, at the level of Chern classes

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`cc-cohom-api`'s `hslice_of_props` asks for `ChernSliceValue` of the class `v` that
`chernSliceNatural_lixChern` pins, namely the Chern classes of the mapping torus
restricted to the slice.  `cc-steenrod` proves the split relation for `V` over the
projective base.  The two are not the same bundle: the restricted mapping torus is
indexed by `VIdx dd ⊕ VIdx dd` and `V` by `VIdx dd`.

They are related on the nose rather than up to a unitary field.  `cc-lix-odd`'s
`mappingTorus_lixSlice_baseY` says the restriction at the marked points *equals*
`fromBlocks 0 0 0 (VmatY y)`, the clutching field being annihilated at the pole, and
that matrix is `V` pushed along the second-summand inclusion.  So the bridge is
`chernOf_congr` followed by `chernOf_pushforward`, with no transport and no
isomorphism.

## Main declarations

* `pushforward_inr_eq_fromBlocks` — the second-summand pushforward is the block form.
* `chernOf_lixSlice_eq_vBundleY` — **the bridge**: the classes of the restricted
  mapping torus are the classes of `V`.

## Manuscript status

Machinery.  Turns `cc-steenrod`'s `ChernSliceValue` for `V` into the one for `v`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

/-! ## 1. Two facts about a pushforward -/

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- A pushforward has the rank it came from: it has the same trace. -/
theorem rank_pushforward (f : ι → κ) (hf : Function.Injective f) (p : Bundle X ι)
    (x : X) : (pushforward f hf p).rank x = p.rank x := by
  have h1 := Bundle.trace_eq_rank (pushforward f hf p) x
  rw [trace_pushforward f hf p x, Bundle.trace_eq_rank p x] at h1
  exact_mod_cast h1.symm

/-- **Pushing along the second-summand inclusion is the block form.**  Both sides are
computed entrywise from `cc-bundle`'s three `coordIncl` conjugation lemmas: on the
image, off the image in the row, and off the image in the column. -/
theorem pushforward_inr_eq_fromBlocks (M : Matrix ι ι ℂ) :
    coordIncl (Sum.inr : ι → ι ⊕ ι) * M * (coordIncl (Sum.inr : ι → ι ⊕ ι))ᴴ
      = Matrix.fromBlocks 0 0 0 M := by
  ext p q
  rcases p with a | a
  · rw [coordIncl_conj_apply_row (f := (Sum.inr : ι → ι ⊕ ι)) (fun _ => Sum.inl_ne_inr) M q]
    rcases q with b | b <;> rfl
  · rcases q with b | b
    · rw [coordIncl_conj_apply_col (f := (Sum.inr : ι → ι ⊕ ι))
        (fun _ => Sum.inl_ne_inr) M (Sum.inr a)]
      rfl
    · rw [coordIncl_conj_apply Sum.inr_injective M a b]
      rfl

/-! ## 2. The bridge -/

variable {ℓ : ℕ}

/-- The restricted mapping torus has the rank of `V`. -/
theorem rank_comap_lixSlice (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (y : baseY dd) :
    (comap (lixSliceMap dd southPole negEThree) (lixBundle G hGc hGu)).rank y
      = lixRank dd :=
  rank_lixBundle G hGc hGu _

/-- `V` over the projective base has that rank, in the `lixRank` spelling. -/
theorem rank_vBundleY_lixRank (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY dd).rank y = lixRank dd :=
  rank_vBundleY dd y

/-- And so does its pushforward into the doubled index. -/
theorem rank_pushforward_vBundleY (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (pushforward (Sum.inr : VIdx dd → VIdx dd ⊕ VIdx dd) Sum.inr_injective
      (vBundleY dd)).rank y = lixRank dd :=
  (rank_pushforward _ Sum.inr_injective (vBundleY dd) y).trans
    (rank_vBundleY_lixRank dd y)

/-- The rank is positive. -/
theorem one_le_lixRank (dd : Fin ℓ → ℕ) : 1 ≤ lixRank dd := by simp [lixRank]

/-- **The bridge.**  The degreewise mod-2 Chern classes of the mapping torus
restricted to the slice are those of `V` over the projective base.

Nothing is transported and nothing is only isomorphic: the restriction *equals*
`V` in a block, so this is `chernOf_congr` for the equality and
`chernOf_pushforward` for the block, and the two index types of different sizes are
handled by the invariance lemma rather than by a reindexing here. -/
theorem chernOf_lixSlice_eq_vBundleY (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (k : ℕ) :
    chernOf (comap (lixSliceMap dd southPole negEThree) (lixBundle G hGc hGu))
        (lixRank dd) (rank_comap_lixSlice dd G hGc hGu) (one_le_lixRank dd) k
      = chernOf (vBundleY dd) (lixRank dd) (rank_vBundleY_lixRank dd)
        (one_le_lixRank dd) k := by
  have hpt : ∀ y : baseY dd,
      (comap (lixSliceMap dd southPole negEThree) (lixBundle G hGc hGu)) y
        = (pushforward (Sum.inr : VIdx dd → VIdx dd ⊕ VIdx dd) Sum.inr_injective
            (vBundleY dd)) y := fun y =>
    (mappingTorus_lixSlice_baseY G y).trans
      (pushforward_inr_eq_fromBlocks (VmatY y)).symm
  exact (chernOf_congr hpt (lixRank dd) (rank_comap_lixSlice dd G hGc hGu)
    (rank_pushforward_vBundleY dd) (one_le_lixRank dd) k).trans
    (chernOf_pushforward (Sum.inr : VIdx dd → VIdx dd ⊕ VIdx dd) Sum.inr_injective
      (vBundleY dd) (lixRank dd) (rank_vBundleY_lixRank dd)
      (rank_pushforward_vBundleY dd) (one_le_lixRank dd) k)

end

end LH
end CharClass
end GroupApproximation
