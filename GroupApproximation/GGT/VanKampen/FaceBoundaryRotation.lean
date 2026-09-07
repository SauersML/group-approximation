import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation

/-! # Changing the initial dart of an actual face traversal -/

namespace GroupApproximation.GGT.VanKampen.FaceBoundary

universe v
variable {M : CombMap.{v}} {f : M.Face}

def rotate (B : FaceBoundary M f) (n : ℕ) : FaceBoundary M f where
  darts := B.darts.rotate n
  nonempty := fun h => B.nonempty (List.rotate_eq_nil_iff.mp h)
  nodup := List.nodup_rotate.mpr B.nodup
  mem_iff d := List.mem_rotate.trans (B.mem_iff d)
  chain := Embedded.isChain_rotate_of_isChain_closes B.nonempty B.chain B.closes n
  closes := Embedded.isChain_rotate_closing B.nonempty B.chain B.closes n _
  length_eq_degree := (List.length_rotate _ _).trans B.length_eq_degree

theorem rotate_head (B : FaceBoundary M f) (n : Fin B.darts.length) :
    ((B.rotate n.val).darts).head (B.rotate n.val).nonempty = B.darts.get n := by
  simp only [rotate, List.head_eq_getElem, List.get_eq_getElem, List.getElem_rotate,
    Nat.zero_add, Nat.mod_eq_of_lt n.isLt]

end GroupApproximation.GGT.VanKampen.FaceBoundary

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotate
#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotate_head
