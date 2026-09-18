import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Map
import GroupApproximation.Meta.AxiomGuard

/-!
# Planarity and face boundaries of the 24-dart counterexample map

Lane gl-p10-51.

Proof route: connectivity by an explicit spanning tree of rotation and edge steps from the dart
`0`; the Euler characteristic `7 - 12 + 7 = 2` from the orbit classifiers.  The face boundaries
are the listed face orbits, checked by `decide`.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

theorem roseJunctionRefute_planar : roseJunctionRefute_M.IsPlanar := by
  constructor
  · have s {a b : roseJunctionRefute_M.Dart} (h : roseJunctionRefute_M.sigma a = b) :
        Relation.EqvGen roseJunctionRefute_M.Adjacent a b :=
      .rel _ _ (Or.inr h)
    have t {a b : roseJunctionRefute_M.Dart} (h : roseJunctionRefute_M.alpha a = b) :
        Relation.EqvGen roseJunctionRefute_M.Adjacent a b :=
      .rel _ _ (Or.inl h)
    have tr {a b c : roseJunctionRefute_M.Dart}
        (h1 : Relation.EqvGen roseJunctionRefute_M.Adjacent a b)
        (h2 : Relation.EqvGen roseJunctionRefute_M.Adjacent b c) :
        Relation.EqvGen roseJunctionRefute_M.Adjacent a c :=
      .trans _ _ _ h1 h2
    have h19 : Relation.EqvGen roseJunctionRefute_M.Adjacent 0 19 := s rfl
    have h1 : Relation.EqvGen roseJunctionRefute_M.Adjacent 0 1 := t rfl
    have h2 := tr h19 (s (b := 2) rfl)
    have h18 := tr h19 (t (b := 18) rfl)
    have h14 := tr h2 (s (b := 14) rfl)
    have h3 := tr h2 (t (b := 3) rfl)
    have h7 := tr h18 (s (b := 7) rfl)
    have h23 := tr h14 (s (b := 23) rfl)
    have h15 := tr h14 (t (b := 15) rfl)
    have h16 := tr h3 (s (b := 16) rfl)
    have h6 := tr h7 (t (b := 6) rfl)
    have h8 := tr h23 (s (b := 8) rfl)
    have h22 := tr h23 (t (b := 22) rfl)
    have h17 := tr h16 (t (b := 17) rfl)
    have h5 := tr h6 (s (b := 5) rfl)
    have h9 := tr h8 (t (b := 9) rfl)
    have h13 := tr h22 (s (b := 13) rfl)
    have h4 := tr h5 (s (b := 4) rfl)
    have h20 := tr h9 (s (b := 20) rfl)
    have h12 := tr h13 (t (b := 12) rfl)
    have h21 := tr h20 (t (b := 21) rfl)
    have h11 := tr h12 (s (b := 11) rfl)
    have h10 := tr h11 (s (b := 10) rfl)
    have hstep : ∀ d : Fin 24, Relation.EqvGen roseJunctionRefute_M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · exact h9
      · exact h10
      · exact h11
      · exact h12
      · exact h13
      · exact h14
      · exact h15
      · exact h16
      · exact h17
      · exact h18
      · exact h19
      · exact h20
      · exact h21
      · exact h22
      · exact h23
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : roseJunctionRefute_M.vertexCount = 7 :=
      (Nat.card_congr roseJunctionRefute_vertexEquiv).trans (by simp)
    have hf : roseJunctionRefute_M.faceCount = 7 :=
      (Nat.card_congr roseJunctionRefute_faceEquiv).trans (by simp)
    have hd : roseJunctionRefute_M.dartCount = 24 := by
      simp [CombMap.dartCount, roseJunctionRefute_M]
    have he := roseJunctionRefute_M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : roseJunctionRefute_M.edgeCount = 12 := by omega
    rw [heq]
    norm_num

def roseJunctionRefute_faceDarts : Fin 7 → List (Fin 24) :=
  ![[0], [19, 7, 5, 17, 3, 14, 1], [2, 16, 6, 18], [4], [8, 20, 12, 22],
    [15, 23, 13, 11, 21, 9], [10]]

noncomputable def roseJunctionRefute_idxBd (i : Fin 7) :
    FaceBoundary roseJunctionRefute_M (roseJunctionRefute_face i) where
  darts := roseJunctionRefute_faceDarts i
  nonempty := by
    change roseJunctionRefute_faceDarts i ≠ ([] : List (Fin 24))
    fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [roseJunctionRefute_faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree roseJunctionRefute_M.facePerm
      (roseJunctionRefute_faceRep i)
    have hd : closedOrbitList roseJunctionRefute_M.facePerm (roseJunctionRefute_faceRep i) =
        roseJunctionRefute_faceDarts i := by
      fin_cases i <;> decide +kernel
    rw [hd] at h
    exact h

noncomputable def roseJunctionRefute_boundary (f : roseJunctionRefute_M.Face) :
    FaceBoundary roseJunctionRefute_M f :=
  (roseJunctionRefute_faceEquiv.left_inv f) ▸
    roseJunctionRefute_idxBd (roseJunctionRefute_faceEquiv f)

@[simp] theorem roseJunctionRefute_bd_face (i : Fin 7) :
    (roseJunctionRefute_boundary (roseJunctionRefute_face i)).darts =
      roseJunctionRefute_faceDarts i := by
  have htransport {f g : roseJunctionRefute_M.Face} (h : f = g)
      (B : FaceBoundary roseJunctionRefute_M f) : (h ▸ B).darts = B.darts := by
    cases h
    rfl
  unfold roseJunctionRefute_boundary
  rw [htransport]
  exact congrArg roseJunctionRefute_faceDarts (roseJunctionRefute_faceEquiv_face i)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_planar
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_idxBd
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_bd_face
