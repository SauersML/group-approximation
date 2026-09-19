import GroupApproximation.Analysis.ShulmanFillNormingBlockHom
import GroupApproximation.Analysis.VoiculescuFrameFromEntries

/-!
# (V3) The amplification `Mₙ(A) ⊆ B(Hⁿ)`, and its compact intersection

Voiculescu's one-step approximation runs Glimm's lemma not on `A ⊆ B(H)` but on
the amplification `Mₙ(A) ⊆ B(Hⁿ)`, because the off-diagonal entries
`⟪ξ_i, a ξ_j⟫` of the tuple it needs are not visible to any state of `A` itself.
This module builds that amplification and checks the one hypothesis Glimm's lemma
cares about: that it meets the compacts only in `0`.

## The definition, and why it is by entries

`Mₙ(A)` could be defined as the image of the matrices over `A` under the block
homomorphism of `Analysis/ShulmanFillNormingBlockHom`, but then closedness would
be a theorem about images of `*`-homomorphisms rather than an observation.
Defined by its entries — `S` belongs when every `π_i S ι_j` lies in `A` — the
subalgebra is closed because each entry map is a bounded linear map and `A` is
closed, and it is a subalgebra because the inclusions and projections are matrix
units: `blockEntry_mul` is the resolution of the identity `Σ_r ι_r π_r = 1`
inserted between the factors, and `blockEntry_star` is the fact that `ι_i` and
`π_i` are adjoint to each other.  Everything below is one of those two facts.

The block space, its projections and inclusions, and the matrix-unit relations
are already in the tree: `Analysis/ShulmanFillNormingBlockHilbert` built them for
the `M₂` amplification of Shulman's `𝒟` over an arbitrary coefficient Hilbert
space, and nothing there is special to `n = 2`.

## The compact intersection

An entry of a compact operator is compact — the compacts are an ideal, and the
entry is a compact operator composed with bounded ones on both sides — so every
entry of a compact `S ∈ Mₙ(A)` lies in `A ∩ K(H) = 0`.  And an operator on the
block space with vanishing entries vanishes, because the identity resolves into
the block projections.  That is `eq_zero_of_blockEntry_eq_zero`.

So the hypothesis Glimm's lemma runs on transfers from `A` to `Mₙ(A)` with no
condition on `n`, which is what lets the amplification be taken at the dimension
of the representation being approximated.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {n : ℕ}

/-! ## The entries of a block operator -/

/-- The `(i,j)` entry of an operator on the block space: compress by the
inclusion on the right and the projection on the left. -/
def blockEntry (S : BlockSpace H n →L[ℂ] BlockSpace H n) (i j : Fin n) :
    H →L[ℂ] H :=
  (hBlockProj H n i) ∘L S ∘L (hBlockIncl H n j)

@[simp] theorem blockEntry_apply (S : BlockSpace H n →L[ℂ] BlockSpace H n)
    (i j : Fin n) (x : H) :
    blockEntry S i j x = hBlockProj H n i (S (hBlockIncl H n j x)) := rfl

/-- Every vector of the block space is the sum of its coordinates. -/
theorem sum_hBlockIncl_coord (w : BlockSpace H n) :
    ∑ r : Fin n, hBlockIncl H n r (hBlockProj H n r w) = w := by
  have h := congrArg
    (fun U : BlockSpace H n →L[ℂ] BlockSpace H n ↦ U w)
    (sum_hBlockIncl_comp_hBlockProj (E := H) (n := n))
  simpa using h

theorem blockEntry_zero (i j : Fin n) :
    blockEntry (0 : BlockSpace H n →L[ℂ] BlockSpace H n) i j = 0 := by
  ext x
  simp

theorem blockEntry_add (S T : BlockSpace H n →L[ℂ] BlockSpace H n) (i j : Fin n) :
    blockEntry (S + T) i j = blockEntry S i j + blockEntry T i j := by
  ext x
  simp

theorem blockEntry_smul (z : ℂ) (S : BlockSpace H n →L[ℂ] BlockSpace H n)
    (i j : Fin n) : blockEntry (z • S) i j = z • blockEntry S i j := by
  ext x
  simp

theorem blockEntry_one (i j : Fin n) :
    blockEntry (1 : BlockSpace H n →L[ℂ] BlockSpace H n) i j
      = if i = j then 1 else 0 := by
  ext x
  have hx : (1 : BlockSpace H n →L[ℂ] BlockSpace H n) (hBlockIncl H n j x)
      = hBlockIncl H n j x := rfl
  have hcoord : blockEntry (1 : BlockSpace H n →L[ℂ] BlockSpace H n) i j x
      = hBlockIncl H n j x i := by rw [blockEntry_apply, hx]; rfl
  by_cases h : i = j
  · subst h
    rw [hcoord, hBlockIncl_coord_same]
    simp
  · rw [hcoord, hBlockIncl_coord_ne h]
    simp [if_neg h]

/-- **The entries multiply as matrices.**  The resolution of the identity
inserted between the two factors. -/
theorem blockEntry_mul (S T : BlockSpace H n →L[ℂ] BlockSpace H n) (i j : Fin n) :
    blockEntry (S * T) i j = ∑ r : Fin n, blockEntry S i r * blockEntry T r j := by
  ext x
  have hw : T (hBlockIncl H n j x)
      = ∑ r : Fin n,
        hBlockIncl H n r (hBlockProj H n r (T (hBlockIncl H n j x))) :=
    (sum_hBlockIncl_coord _).symm
  calc blockEntry (S * T) i j x
      = hBlockProj H n i (S (T (hBlockIncl H n j x))) := rfl
    _ = hBlockProj H n i (S (∑ r : Fin n,
          hBlockIncl H n r (hBlockProj H n r (T (hBlockIncl H n j x))))) := by
        rw [← hw]
    _ = ∑ r : Fin n, hBlockProj H n i (S (hBlockIncl H n r
          (hBlockProj H n r (T (hBlockIncl H n j x))))) := by
        rw [map_sum, map_sum]
    _ = (∑ r : Fin n, blockEntry S i r * blockEntry T r j) x := by
        rw [sum_apply]
        exact Finset.sum_congr rfl fun r _ ↦ rfl

/-- **The entries transpose under the star.**  The inclusions and projections
are adjoint to each other. -/
theorem blockEntry_star (S : BlockSpace H n →L[ℂ] BlockSpace H n) (i j : Fin n) :
    blockEntry (star S) i j = star (blockEntry S j i) := by
  refine ContinuousLinearMap.ext fun x ↦ ext_inner_left ℂ fun y ↦ ?_
  have hleft : ⟪y, blockEntry (star S) i j x⟫_ℂ
      = ⟪S (hBlockIncl H n i y), hBlockIncl H n j x⟫_ℂ := by
    have e1 : ⟪y, blockEntry (star S) i j x⟫_ℂ
        = ⟪hBlockIncl H n i y, (star S) (hBlockIncl H n j x)⟫_ℂ :=
      (inner_hBlockIncl_left i y ((star S) (hBlockIncl H n j x))).symm
    rw [e1, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hright : ⟪y, star (blockEntry S j i) x⟫_ℂ
      = ⟪S (hBlockIncl H n i y), hBlockIncl H n j x⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    exact (inner_hBlockIncl_right j (S (hBlockIncl H n i y)) x).symm
  rw [hleft, hright]

/-- An operator on the block space with vanishing entries vanishes. -/
theorem eq_zero_of_blockEntry_eq_zero {S : BlockSpace H n →L[ℂ] BlockSpace H n}
    (h : ∀ i j, blockEntry S i j = 0) : S = 0 := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hw : S w = ∑ j : Fin n, S (hBlockIncl H n j (hBlockProj H n j w)) := by
    conv_lhs => rw [← sum_hBlockIncl_coord w]
    rw [map_sum]
  have hterm : ∀ j : Fin n, S (hBlockIncl H n j (hBlockProj H n j w)) = 0 := by
    intro j
    have hres : S (hBlockIncl H n j (hBlockProj H n j w))
        = ∑ i : Fin n, hBlockIncl H n i
            (blockEntry S i j (hBlockProj H n j w)) :=
      (sum_hBlockIncl_coord (S (hBlockIncl H n j (hBlockProj H n j w)))).symm
    rw [hres]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [h i j]
    simp
  rw [hw, Finset.sum_congr rfl fun j _ ↦ hterm j]
  simp

/-! ## The entry map is bounded -/

/-- The entry map, as a bounded linear map.  Its continuity is what makes the
amplification of a closed subalgebra closed. -/
def blockEntryL (i j : Fin n) :
    (BlockSpace H n →L[ℂ] BlockSpace H n) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun S ↦ blockEntry S i j
      map_add' := fun S T ↦ blockEntry_add S T i j
      map_smul' := fun z S ↦ blockEntry_smul z S i j }
    (‖hBlockProj H n i‖ * ‖hBlockIncl H n j‖)
    (by
      intro S
      show ‖blockEntry S i j‖
        ≤ ‖hBlockProj H n i‖ * ‖hBlockIncl H n j‖ * ‖S‖
      calc ‖blockEntry S i j‖
          ≤ ‖hBlockProj H n i‖ * ‖S ∘L hBlockIncl H n j‖ :=
            (hBlockProj H n i).opNorm_comp_le (S ∘L hBlockIncl H n j)
        _ ≤ ‖hBlockProj H n i‖ * (‖S‖ * ‖hBlockIncl H n j‖) :=
            mul_le_mul_of_nonneg_left (S.opNorm_comp_le (hBlockIncl H n j))
              (norm_nonneg (hBlockProj H n i))
        _ = ‖hBlockProj H n i‖ * ‖hBlockIncl H n j‖ * ‖S‖ := by ring)

@[simp] theorem blockEntryL_apply (i j : Fin n)
    (S : BlockSpace H n →L[ℂ] BlockSpace H n) :
    blockEntryL i j S = blockEntry S i j := rfl

/-! ## The amplified subalgebra -/

/-- **`Mₙ(A)` inside `B(Hⁿ)`**, defined by its entries. -/
def ampSubalgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) :
    StarSubalgebra ℂ (BlockSpace H n →L[ℂ] BlockSpace H n) where
  carrier := {S | ∀ i j, blockEntry S i j ∈ A}
  zero_mem' := by
    intro i j
    rw [blockEntry_zero]
    exact zero_mem A
  one_mem' := by
    intro i j
    rw [blockEntry_one]
    split
    · exact one_mem A
    · exact zero_mem A
  add_mem' := by
    intro S T hS hT i j
    rw [blockEntry_add]
    exact add_mem (hS i j) (hT i j)
  mul_mem' := by
    intro S T hS hT i j
    rw [blockEntry_mul]
    exact sum_mem fun r _ ↦ mul_mem (hS i r) (hT r j)
  algebraMap_mem' := by
    intro z i j
    have h : (algebraMap ℂ (BlockSpace H n →L[ℂ] BlockSpace H n)) z = z • 1 :=
      Algebra.algebraMap_eq_smul_one z
    rw [h, blockEntry_smul, blockEntry_one]
    split
    · rw [← Algebra.algebraMap_eq_smul_one]
      exact A.algebraMap_mem z
    · rw [smul_zero]
      exact zero_mem A
  star_mem' := by
    intro S hS i j
    rw [blockEntry_star]
    exact star_mem (hS j i)

theorem mem_ampSubalgebra_iff {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {S : BlockSpace H n →L[ℂ] BlockSpace H n} :
    S ∈ ampSubalgebra A n ↔ ∀ i j, blockEntry S i j ∈ A := Iff.rfl

/-- The amplification of a closed subalgebra is closed. -/
theorem isClosed_ampSubalgebra (A : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ)
    (hA : IsClosed (A : Set (H →L[ℂ] H))) :
    IsClosed ((ampSubalgebra A n :
      Set (BlockSpace H n →L[ℂ] BlockSpace H n))) := by
  have h : (ampSubalgebra A n : Set (BlockSpace H n →L[ℂ] BlockSpace H n))
      = ⋂ (i : Fin n) (j : Fin n),
          (fun S : BlockSpace H n →L[ℂ] BlockSpace H n ↦ blockEntry S i j) ⁻¹'
            (A : Set (H →L[ℂ] H)) := by
    ext S
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_
  exact IsClosed.preimage (blockEntryL (H := H) (n := n) i j).continuous hA

/-! ## The compact intersection -/

/-- **The hypothesis Glimm's lemma runs on transfers to the amplification.**  An
entry of a compact operator is compact, so it dies in `A`; and an operator with
vanishing entries vanishes. -/
theorem ampSubalgebra_compactMem_eq_zero (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (n : ℕ) (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) :
    ∀ S ∈ ampSubalgebra A n, IsCompactOperator S → S = 0 := by
  intro S hS hcpt
  refine eq_zero_of_blockEntry_eq_zero fun i j ↦ ?_
  refine hAK _ (hS i j) ?_
  have h1 : IsCompactOperator (⇑(S ∘L hBlockIncl H n j)) := by
    have h := hcpt.comp_clm (hBlockIncl H n j)
    rwa [← ContinuousLinearMap.coe_comp] at h
  have h2 := h1.clm_comp (hBlockProj H n i)
  rwa [← ContinuousLinearMap.coe_comp] at h2

end

end ShulmanFill
end GroupApproximation
