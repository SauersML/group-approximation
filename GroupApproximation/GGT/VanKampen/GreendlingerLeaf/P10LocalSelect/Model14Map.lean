import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWholeSectionWrapModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The 14-dart shared-rose model: the map

A planar map with 14 darts, for the truth check of the kept sub-walk core
(`Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement`) in its last open configuration: a
three-passage rose vertex visited by both stretches of a first-turn contact vertex.

The edges are `{2i, 2i+1}`:

* `0 = a_S : v → w`, `2 = a_E : w → v`, `4 = b_E : v → w`, `6 = b_S : w → v`;
* the loops `8 = ℓ`, `10 = m`, `12 = n` at `w`.

The rotation has the cycles `(3 0 7 4)` at `v` and `(1 2 12 13 5 8 9 6 10 11)` at `w`.  The
faces are `K = [0,2]`, `P_B = [4,8,6]`, the lake `[9]`, `S = [1,7,10]`, `[11]`,
`E = [3,12,5]` and `[13]`.  So `V - E + F = 2 - 7 + 7 = 2`.

Proof route: every fact is a kernel `decide` over `Fin 14`, or an orbit classifier
(`OrbitClassifier.orbitEquiv`).  Same pattern as `P10RoseJunctionRefute/Map` and
`P10RoseJunctionRefute/Boundary`.

Manuscript status: infrastructure (a truth witness) for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

open Equiv

def m14_pAlpha : Perm (Fin 14) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  left_inv := by decide
  right_inv := by decide

def m14_pSigma : Perm (Fin 14) where
  toFun := ![7, 2, 12, 0, 3, 8, 10, 4, 9, 6, 11, 1, 13, 5]
  invFun := ![3, 11, 1, 4, 7, 13, 9, 0, 5, 8, 6, 10, 2, 12]
  left_inv := by decide
  right_inv := by decide

/-- The map with 14 darts, two vertices and seven faces. -/
def m14_M : CombMap where
  Dart := Fin 14
  dartFintype := inferInstance
  alpha := m14_pAlpha
  sigma := m14_pSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance m14_instDecEqM : DecidableEq m14_M.Dart := inferInstanceAs (DecidableEq (Fin 14))
instance m14_instOfNatM (n : ℕ) : OfNat m14_M.Dart n := inferInstanceAs (OfNat (Fin 14) n)

def m14_faceClass : Fin 14 → Fin 7 := ![0, 3, 0, 5, 1, 5, 1, 3, 1, 2, 3, 4, 5, 6]
def m14_faceRep : Fin 7 → Fin 14 := ![0, 4, 9, 1, 11, 3, 13]

noncomputable def m14_faceEquiv : m14_M.Face ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv m14_M.facePerm m14_faceClass m14_faceRep (by decide +kernel)
    (by decide) (by decide +kernel)

def m14_face (i : Fin 7) : m14_M.Face := m14_M.faceOf (m14_faceRep i)

@[simp] theorem m14_faceEquiv_face (i : Fin 7) : m14_faceEquiv (m14_face i) = i := by
  change m14_faceClass (m14_faceRep i) = i
  fin_cases i <;> rfl

theorem m14_faceOf_eq_face (d : Fin 14) (i : Fin 7) :
    m14_M.faceOf d = m14_face i ↔ m14_faceClass d = i := by
  rw [← m14_faceEquiv.injective.eq_iff, m14_faceEquiv_face]
  rfl

theorem m14_face_eq_iff (i j : Fin 7) : m14_face i = m14_face j ↔ i = j := by
  rw [← m14_faceEquiv.injective.eq_iff, m14_faceEquiv_face, m14_faceEquiv_face]

theorem m14_faceOf_eq_face' (x : Fin 14) : m14_M.faceOf x = m14_face (m14_faceClass x) :=
  (m14_faceOf_eq_face x _).mpr rfl

def m14_vClass : Fin 14 → Fin 2 := ![0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1]
def m14_vRep : Fin 2 → Fin 14 := ![0, 1]

noncomputable def m14_vertexEquiv : m14_M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv m14_M.sigma m14_vClass m14_vRep (by decide +kernel) (by decide)
    (by decide +kernel)

theorem m14_vClass_iff (d e : Fin 14) :
    m14_M.vertexOf d = m14_M.vertexOf e ↔ m14_vClass d = m14_vClass e := by
  rw [← m14_vertexEquiv.injective.eq_iff]
  rfl

theorem m14_planar : m14_M.IsPlanar := by
  constructor
  · have s {a b : m14_M.Dart} (h : m14_M.sigma a = b) : Relation.EqvGen m14_M.Adjacent a b :=
      .rel _ _ (Or.inr h)
    have t {a b : m14_M.Dart} (h : m14_M.alpha a = b) : Relation.EqvGen m14_M.Adjacent a b :=
      .rel _ _ (Or.inl h)
    have tr {a b c : m14_M.Dart} (h1 : Relation.EqvGen m14_M.Adjacent a b)
        (h2 : Relation.EqvGen m14_M.Adjacent b c) : Relation.EqvGen m14_M.Adjacent a c :=
      .trans _ _ _ h1 h2
    have h1 : Relation.EqvGen m14_M.Adjacent 0 1 := t rfl
    have h7 : Relation.EqvGen m14_M.Adjacent 0 7 := s rfl
    have h4 := tr h7 (s (b := 4) rfl)
    have h3 := tr h4 (s (b := 3) rfl)
    have h2 := tr h1 (s (b := 2) rfl)
    have h12 := tr h2 (s (b := 12) rfl)
    have h13 := tr h12 (s (b := 13) rfl)
    have h5 := tr h13 (s (b := 5) rfl)
    have h8 := tr h5 (s (b := 8) rfl)
    have h9 := tr h8 (s (b := 9) rfl)
    have h6 := tr h9 (s (b := 6) rfl)
    have h10 := tr h6 (s (b := 10) rfl)
    have h11 := tr h10 (s (b := 11) rfl)
    have hstep : ∀ d : Fin 14, Relation.EqvGen m14_M.Adjacent 0 d := by
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
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : m14_M.vertexCount = 2 := (Nat.card_congr m14_vertexEquiv).trans (by simp)
    have hf : m14_M.faceCount = 7 := (Nat.card_congr m14_faceEquiv).trans (by simp)
    have hd : m14_M.dartCount = 14 := by simp [CombMap.dartCount, m14_M]
    have he := m14_M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : m14_M.edgeCount = 7 := by omega
    rw [heq]
    norm_num

def m14_faceDarts : Fin 7 → List (Fin 14) :=
  ![[0, 2], [4, 8, 6], [9], [1, 7, 10], [11], [3, 12, 5], [13]]

noncomputable def m14_idxBd (i : Fin 7) : FaceBoundary m14_M (m14_face i) where
  darts := m14_faceDarts i
  nonempty := by
    change m14_faceDarts i ≠ ([] : List (Fin 14))
    fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [m14_faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree m14_M.facePerm (m14_faceRep i)
    have hd : closedOrbitList m14_M.facePerm (m14_faceRep i) = m14_faceDarts i := by
      fin_cases i <;> decide +kernel
    rw [hd] at h
    exact h

noncomputable def m14_boundary (f : m14_M.Face) : FaceBoundary m14_M f :=
  (m14_faceEquiv.left_inv f) ▸ m14_idxBd (m14_faceEquiv f)

@[simp] theorem m14_bd_face (i : Fin 7) :
    (m14_boundary (m14_face i)).darts = m14_faceDarts i := by
  have htransport {f g : m14_M.Face} (h : f = g) (B : FaceBoundary m14_M f) :
      (h ▸ B).darts = B.darts := by
    cases h
    rfl
  unfold m14_boundary
  rw [htransport]
  exact congrArg m14_faceDarts (m14_faceEquiv_face i)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_M
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_vClass_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_planar
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_bd_face
