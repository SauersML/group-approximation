import GroupApproximation.Leavitt.RankTwelveCompressor
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# The rank-twelve Kazhdan corner is a faithful copy of `EL₃`

`non_mf_groups_exist.tex`, Section `The binary Leavitt self-compression`,
writes "let `L = EL₃(R) ≤ H` be the upper-left corner".  The word *is* carries
content: the printed argument uses `L` as a copy of `EL₃(R)`, not merely as a
quotient of it.

`Manuscript.OneSidedMFRadical.RankTwelveConfiguration` supplies the embedding
`cornerEmbedding : EL₃(R) →* H`, its range (`cornerEmbedding_range`), and
surjectivity onto `corner`.  What was missing is **injectivity**.  This module
supplies it, and hence the isomorphism `EL₃(R) ≃* corner`.

## The retraction

Injectivity is a retraction statement: the `12 × 12` corner matrix determines
its upper-left `3 × 3` block.  Two observations make it cheap.

* The flattening `flat12 : RankTwelve.Full R ≃+* M₁₂(R)` is a ring
  **equivalence**, so it is injective for free; no entry-level analysis of
  `flat12` is needed.
* At the nested level the retraction is literally an entry lookup:
  `fullCorner M = diag(diag(M, I₃), I₆)`, so `(fullCorner M) 0 0 0 0 = M`.
  That is `RankTwelve.cornerRetract`, and it is the nested analogue of the
  `Matrix.submatrix cornerIndex cornerIndex` retraction; it needs no
  multiplicativity of `submatrix`, because it is used only on values, and
  multiplicativity of the embedding is already carried by
  `RankTwelve.fullCorner_mul`.

`flatCornerRetract` records the composite retraction on the flat side.

## Property `(T)` for the corner

`RankTwelveConfiguration.corner_hasKazhdanPropertyT` already proves
`HasKazhdanPropertyT corner`, by transporting `(T)` along the **surjection**
`cornerEmbeddingToCorner`.  Injectivity is not needed for that, so no `(T)`
statement is duplicated here.  What the isomorphism adds is the reverse
direction: every property of `corner` now transfers back to `EL₃(R)`, and the
corner is a faithful copy rather than a possibly proper quotient.
-/

namespace GroupApproximation
namespace RankTwelve

variable {A : Type*} [Ring A]

/-! ## The nested corner retraction -/

theorem halfCorner_apply_zero (M : Cell A) : halfCorner M 0 0 = M := by
  simp [halfCorner]

theorem fullCorner_apply_zero (M : Cell A) : fullCorner M 0 0 = halfCorner M := by
  simp [fullCorner]

/-- The retraction of `diag(M, I₉)` back onto its upper-left `3 × 3` block:
read off the `(0,0)` entry twice. -/
def cornerRetract (X : Full A) : Cell A := (X 0 0 : Half A) 0 0

@[simp] theorem cornerRetract_fullCorner (M : Cell A) :
    cornerRetract (fullCorner M) = M := by
  show (fullCorner M 0 0 : Half A) 0 0 = M
  rw [fullCorner_apply_zero, halfCorner_apply_zero]

theorem halfCorner_injective : Function.Injective (halfCorner (A := A)) := by
  intro M N h
  have h' : halfCorner M 0 0 = halfCorner N 0 0 := by rw [h]
  rwa [halfCorner_apply_zero, halfCorner_apply_zero] at h'

/-- **The corner embedding of matrices is injective**, because
`cornerRetract` retracts it. -/
theorem fullCorner_injective : Function.Injective (fullCorner (A := A)) := by
  intro M N h
  have h' : cornerRetract (fullCorner M) = cornerRetract (fullCorner N) := by
    rw [h]
  rwa [cornerRetract_fullCorner, cornerRetract_fullCorner] at h'

end RankTwelve

namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-! ## The flat retraction -/

/-- The retraction on the literal `12 × 12` side: undo the flattening, then
read off the nested corner.  `flat12` is a ring equivalence, so this is a
genuine left inverse of `M ↦ flat12 (fullCorner M)`. -/
noncomputable def flatCornerRetract (X : Matrix (Fin 12) (Fin 12) R) :
    RankTwelve.Cell R :=
  RankTwelve.cornerRetract (flat12.symm X)

@[simp] theorem flatCornerRetract_flat12_fullCorner (M : RankTwelve.Cell R) :
    flatCornerRetract (flat12 (RankTwelve.fullCorner M)) = M := by
  show RankTwelve.cornerRetract (flat12.symm (flat12 (RankTwelve.fullCorner M)))
    = M
  rw [RingEquiv.symm_apply_apply, RankTwelve.cornerRetract_fullCorner]

/-! ## Injectivity of the printed corner embedding -/

theorem fullCornerUnits_injective : Function.Injective fullCornerUnits := by
  intro u v h
  have h' : RankTwelve.fullCorner (u : RankTwelve.Cell R) =
      RankTwelve.fullCorner (v : RankTwelve.Cell R) := congrArg Units.val h
  exact Units.ext (RankTwelve.fullCorner_injective h')

theorem flatCornerUnits_injective : Function.Injective flatCornerUnits := by
  intro u v h
  have h' : flat12Units (fullCornerUnits u) = flat12Units (fullCornerUnits v) := h
  exact fullCornerUnits_injective (flat12Units.injective h')

/-- **The manuscript's `EL₃(R) ≤ H` really is an inclusion.** -/
theorem cornerEmbedding_injective : Function.Injective cornerEmbedding := by
  intro x y h
  have h' : flatCornerUnits (x : (RankTwelve.Cell R)ˣ) =
      flatCornerUnits (y : (RankTwelve.Cell R)ˣ) := congrArg Subtype.val h
  exact Subtype.ext (flatCornerUnits_injective h')

theorem cornerEmbedding_ker : cornerEmbedding.ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff cornerEmbedding).mpr cornerEmbedding_injective

theorem cornerEmbeddingToCorner_injective :
    Function.Injective cornerEmbeddingToCorner := by
  intro x y h
  have h' : cornerEmbedding x = cornerEmbedding y := congrArg Subtype.val h
  exact cornerEmbedding_injective h'

theorem cornerEmbeddingToCorner_bijective :
    Function.Bijective cornerEmbeddingToCorner :=
  ⟨cornerEmbeddingToCorner_injective, cornerEmbeddingToCorner_surjective⟩

/-- **The upper-left corner of `H` is a copy of `EL₃(R)`**, not merely a
quotient of it: the manuscript's `L = EL₃(R)` reading is exact. -/
noncomputable def cornerEquiv :
    BinaryLeavittSteinberg.ElementaryBase 3 ≃* corner :=
  MulEquiv.ofBijective cornerEmbeddingToCorner cornerEmbeddingToCorner_bijective

@[simp] theorem cornerEquiv_apply (g : BinaryLeavittSteinberg.ElementaryBase 3) :
    (cornerEquiv g : H) = cornerEmbedding g := rfl

/-- Consequently the corner is nontrivial: it contains the printed
`ell = e₁₂(1)`, and it is a faithful copy of `EL₃(R)`. -/
theorem cornerEquiv_symm_apply_cornerEmbedding
    (g : BinaryLeavittSteinberg.ElementaryBase 3) :
    cornerEquiv.symm (cornerEmbeddingToCorner g) = g :=
  cornerEquiv.symm_apply_apply g

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
