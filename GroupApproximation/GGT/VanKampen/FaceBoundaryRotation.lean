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

/-- Forward cyclic distance between two original corners, including zero
when they agree. -/
def forwardOffset (B : FaceBoundary M f) (start finish : Fin B.darts.length) : ℕ :=
  if start.val ≤ finish.val then finish.val - start.val
  else B.darts.length + finish.val - start.val

theorem forwardOffset_lt (B : FaceBoundary M f) (start finish : Fin B.darts.length) :
    B.forwardOffset start finish < B.darts.length := by
  have hs := start.isLt
  have hf := finish.isLt
  unfold forwardOffset
  split <;> omega

theorem forwardOffset_add_mod (B : FaceBoundary M f) (start finish : Fin B.darts.length) :
    (B.forwardOffset start finish + start.val) % B.darts.length = finish.val := by
  have hs := start.isLt
  have hf := finish.isLt
  unfold forwardOffset
  split
  · rw [show finish.val - start.val + start.val = finish.val by omega,
      Nat.mod_eq_of_lt hf]
  · rw [show B.darts.length + finish.val - start.val + start.val =
      B.darts.length + finish.val by omega, Nat.add_mod, Nat.mod_self,
      Nat.zero_add, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hf]

def rotatedIndex (B : FaceBoundary M f) (start finish : Fin B.darts.length) :
    Fin (B.rotate start.val).darts.length :=
  ⟨B.forwardOffset start finish, by
    simpa only [rotate, List.length_rotate] using B.forwardOffset_lt start finish⟩

theorem rotatedIndex_get (B : FaceBoundary M f) (start finish : Fin B.darts.length) :
    (B.rotate start.val).darts.get (B.rotatedIndex start finish) = B.darts.get finish := by
  simp only [rotatedIndex, rotate, List.get_eq_getElem, List.getElem_rotate,
    forwardOffset_add_mod]

end GroupApproximation.GGT.VanKampen.FaceBoundary

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotate
#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotate_head
#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotatedIndex_get
