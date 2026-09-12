import GroupApproximation.GGT.VanKampen.CactusBigBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner boundary of a polygon with no relator cells

A zero-cell cactus is a single polygon. Its complementary face is the
backwards outer polygon, including the monogon case. This explicit boundary
allows an arbitrary nonempty null relative word to be filled by one G-cell
without changing its literal relative letters.
-/

namespace GroupApproximation.GGT.VanKampen.CactusShape

open GroupApproximation.HullSC.Lemma44OrientedRelatorDiagram

/-- The backward traversal of the outer polygon, starting at its last edge. -/
def outerBackwardDarts (S : CactusShape) : List (CactusDart S) :=
  List.ofFn fun j : Fin S.boundaryLength => CactusDart.outerBackward j.rev

theorem outerBackwardDarts_nonempty (S : CactusShape) : S.outerBackwardDarts ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp only [outerBackwardDarts, List.length_ofFn, List.length_nil] at hlen
  exact (Nat.ne_of_gt S.boundary_pos) hlen

theorem outerBackwardDarts_nodup (S : CactusShape) : S.outerBackwardDarts.Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  exact Fin.rev_injective (CactusDart.outerBackward.inj hij)

theorem outerBackwardDarts_mem_iff (S : CactusShape) (hzero : S.cellCount = 0)
    (d : CactusDart S) : d ∈ S.outerBackwardDarts ↔ S.toCombMap.faceOf d = S.bigFace := by
  rw [outerBackwardDarts, List.mem_ofFn, faceOf_eq_bigFace_iff]
  cases d with
  | outerForward j => simp [faceClass]
  | outerBackward j =>
      exact ⟨fun _ => rfl, fun _ => ⟨j.rev, by rw [Fin.rev_rev]⟩⟩
  | relatorForward i j => have := i.isLt; omega
  | relatorBackward i j => have := i.isLt; omega
  | stemOut i => have := i.isLt; omega
  | stemIn i => have := i.isLt; omega

theorem outerBackwardDarts_chain (S : CactusShape) :
    S.outerBackwardDarts.IsChain (fun d e : CactusDart S => S.toCombMap.facePerm d = e) := by
  rw [outerBackwardDarts, List.isChain_ofFn]
  intro k hk
  have hne : Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin S.boundaryLength) ≠
      S.boundaryZero := rev_mk_ne_zero hk
  rw [S.facePerm_outerBackward_of_ne _ hne]
  exact congrArg (fun j => CactusDart.outerBackward (S := S) j) (prevFin_rev_succ hk)

theorem facePerm_outerBackward_of_zero (S : CactusShape) (hzero : S.cellCount = 0)
    (j : Fin S.boundaryLength) :
    S.toCombMap.facePerm (.outerBackward j) = .outerBackward (prevFin S.boundaryLength j) := by
  change S.sigmaFun (.outerForward j) = _
  simp only [sigmaFun, hzero, Nat.lt_irrefl, dite_false]
  split_ifs <;> rfl

theorem outerBackwardDarts_closes (S : CactusShape) (hzero : S.cellCount = 0) :
    S.toCombMap.facePerm (S.outerBackwardDarts.getLast S.outerBackwardDarts_nonempty) =
      S.outerBackwardDarts.head S.outerBackwardDarts_nonempty := by
  change S.toCombMap.facePerm
      ((List.ofFn (fun j : Fin S.boundaryLength => CactusDart.outerBackward (S := S) j.rev)).getLast _) =
    (List.ofFn (fun j : Fin S.boundaryLength => CactusDart.outerBackward (S := S) j.rev)).head _
  rw [List.getLast_ofFn, List.head_ofFn, S.facePerm_outerBackward_of_zero hzero]
  have hlast : Fin.rev (⟨S.boundaryLength - 1,
      Nat.sub_one_lt (Nat.ne_of_gt S.boundary_pos)⟩ : Fin S.boundaryLength) =
      S.boundaryZero := by
    apply Fin.ext
    simp only [Fin.val_rev, boundaryZero, Fin.val_mk]
    omega
  rw [hlast]
  exact congrArg (fun j => CactusDart.outerBackward (S := S) j)
    (prevFin_zero_eq_rev_zero S.boundary_pos)

/-- The genuine complementary face boundary of a zero-cell cactus. -/
noncomputable def zeroBigFaceBoundary (S : CactusShape) (hzero : S.cellCount = 0) :
    FaceBoundary S.toCombMap S.bigFace := by
  classical
  let l := S.outerBackwardDarts
  have hn : l.Nodup := S.outerBackwardDarts_nodup
  let e₁ : Fin l.length ≃ {x : CactusDart S // x ∈ l} := hn.getEquiv l
  have hpred : (fun x : CactusDart S => x ∈ l) =
      (fun x : CactusDart S => S.toCombMap.faceOf x = S.bigFace) := by
    funext x
    exact propext (S.outerBackwardDarts_mem_iff hzero x)
  let e₂ : {x : CactusDart S // x ∈ l} ≃
      {x : CactusDart S // S.toCombMap.faceOf x = S.bigFace} := Equiv.subtypeEquivProp hpred
  exact {
    darts := l
    nonempty := S.outerBackwardDarts_nonempty
    nodup := hn
    mem_iff := S.outerBackwardDarts_mem_iff hzero
    chain := S.outerBackwardDarts_chain
    closes := S.outerBackwardDarts_closes hzero
    length_eq_degree := by
      change l.length = Nat.card {x : CactusDart S // S.toCombMap.faceOf x = S.bigFace}
      rw [← Nat.card_fin l.length]
      exact Nat.card_congr (e₁.trans e₂) }

/-- The only nonouter face is the complementary face. -/
theorem face_eq_big_of_ne_outer (S : CactusShape) (hzero : S.cellCount = 0)
    (f : S.toCombMap.Face) (hf : f ≠ S.outerFace) : f = S.bigFace := by
  rw [← S.indexedFace_faceEquiv f]
  cases hi : S.faceEquiv f with
  | outer =>
      apply False.elim
      apply hf
      change f = S.indexedFace .outer
      simpa only [hi] using (S.indexedFace_faceEquiv f).symm
  | relator i => have := i.isLt; omega
  | big => rfl

end GroupApproximation.GGT.VanKampen.CactusShape

#audit_axioms GroupApproximation.GGT.VanKampen.CactusShape.outerBackwardDarts_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CactusShape.outerBackwardDarts_chain
#audit_axioms GroupApproximation.GGT.VanKampen.CactusShape.outerBackwardDarts_closes
#audit_axioms GroupApproximation.GGT.VanKampen.CactusShape.zeroBigFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.CactusShape.face_eq_big_of_ne_outer
