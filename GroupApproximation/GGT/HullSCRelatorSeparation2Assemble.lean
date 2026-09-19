import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorClose

/-!
# The two joints of the assembly

Everything the corrected separation needs is now proved except two joints, and
this module is both.  They are small on purpose: the mathematics is in the four
closers, and what is left is to see that the four cases are exhaustive and that
the polygon's first gap says what the join wants to hear.

`listVal_conj_of_sym_cases` is the dispatch.  `RelWord.Sym.exists_rotate` splits
the symmetrized closure into rotations of the relator and rotations of its
formal inverse, so a match between two members falls into four cases, and each
is discharged by its own closer:
`HullSC.listVal_conj_of_alignedMatch` for two rotations of the relator,
`HullSC.listVal_conj_of_mirroredAlignedMatch` for two of the formal inverse, and
`HullSC.not_mixedMatch` for the two mixed cases, which return `False`.  The
dispatch takes those four as obligations against the rotation indices the
splitting produces, so a consumer supplies each by applying the closer to the
quadrilateral's data for that case.

`vertex_eq_of_gap_one` is the other joint.  `GGT.OsinComponents.exists_block_span_conj`
does not merely bound its first gap, it names it:
`x = (vertex 1 s j)⁻¹ * (listVal p * vertex 1 q i)`.  Once the diagonal clause of
the design has forced `x = 1`, that definition rearranges to
`listVal p * vertex 1 q i = vertex 1 s j`, which is exactly the vertex relation
`GGT/HullSCRelatorSeparation2Join.lean` consumes -- with `y = listVal p`, the
four-gon's own first side, which is what made the aligned case close without a
centralizer claim.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Joints

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The polygon's first gap, once trivial, is the join's vertex relation.** -/
theorem vertex_eq_of_gap_one {q s : List (GGT.RelLetter G Λ)} {i j : ℕ}
    {x y : G}
    (hx : x = (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
      (y * GGT.OsinComponents.vertex (1 : G) q i))
    (hx1 : x = 1) :
    y * GGT.OsinComponents.vertex (1 : G) q i
      = GGT.OsinComponents.vertex (1 : G) s j := by
  rw [hx1] at hx
  have h := congrArg
    (fun g : G => GGT.OsinComponents.vertex (1 : G) s j * g) hx
  simpa [mul_assoc] using h.symm

/-- **The four cases are exhaustive.**

The dispatch of the corrected separation: two members of the symmetrized
closure are rotations of the relator or of its formal inverse, and each of the
four combinations has its closer. -/
theorem listVal_conj_of_sym_cases {v w w' : List (GGT.RelLetter G Λ)} {y : G}
    (hw : RelWord.Sym v w) (hw' : RelWord.Sym v w')
    (hrr : ∀ c c' : ℕ, w = v.rotate c → w' = v.rotate c' →
      GGT.RelLetter.listVal w' = y * GGT.RelLetter.listVal w * y⁻¹)
    (hii : ∀ c c' : ℕ, w = (RelWord.revInv v).rotate c →
      w' = (RelWord.revInv v).rotate c' →
        GGT.RelLetter.listVal w' = y * GGT.RelLetter.listVal w * y⁻¹)
    (hri : ∀ c c' : ℕ, w = v.rotate c →
      w' = (RelWord.revInv v).rotate c' → False)
    (hir : ∀ c c' : ℕ, w = (RelWord.revInv v).rotate c →
      w' = v.rotate c' → False) :
    GGT.RelLetter.listVal w' = y * GGT.RelLetter.listVal w * y⁻¹ := by
  rcases hw.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    rcases hw'.exists_rotate with ⟨c', hc'⟩ | ⟨c', hc'⟩
  · exact hrr c c' hc hc'
  · exact (hri c c' hc hc').elim
  · exact (hir c c' hc hc').elim
  · exact hii c c' hc hc'

end Joints

end HullSC
end GroupApproximation
