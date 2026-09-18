import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The map of the enclosed-pocket counterexample

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Model test for the infrastructure of
`thm:hull` (non_mf_groups_exist.tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)).

A planar map with 26 darts, 13 edges, 8 vertices and 7 faces.  There are two main vertices `v` and
`w`, joined by four parallel edges.  The triangles `Π_i` and `C` hang at `v`, and the triangle `Π_j`
hangs at `w`.  The faces are the classes
* `0`: `Π_i = [0,1,2]`,
* `1`: `Π_j = [3,4,5]`,
* `2`: `C = [6,7,8]`,
* `3`: the big face `H = [9,…,19]`, which surrounds all three triangles,
* `4`: the digon `b = [20,21]`,
* `5`: the digon `a = [22,23]`,
* `6`: the exterior digon `[24,25]`.

Every dart of a triangle has its reverse on `H` (`alpha_faceClass_of_le_two`).

## Manuscript status

Model test for infrastructure of `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL03BPinchModel

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen Equiv

/-- The edge involution. -/
def mAlpha : Perm (Fin 26) where
  toFun := ![11, 10, 9, 18, 17, 16, 14, 13, 12, 2, 1, 0, 8, 7, 6, 23, 5, 4, 3, 20, 19, 24, 25, 15,
    21, 22]
  invFun := ![11, 10, 9, 18, 17, 16, 14, 13, 12, 2, 1, 0, 8, 7, 6, 23, 5, 4, 3, 20, 19, 24, 25, 15,
    21, 22]
  left_inv := by decide
  right_inv := by decide

/-- The vertex rotation. -/
def mSigma : Perm (Fin 26) where
  toFun := ![12, 11, 10, 19, 18, 17, 15, 14, 13, 0, 2, 1, 6, 8, 7, 22, 3, 5, 4, 21, 9, 25, 24, 16,
    20, 23]
  invFun := ![9, 11, 10, 16, 18, 17, 12, 14, 13, 20, 2, 1, 0, 8, 7, 6, 23, 5, 4, 3, 24, 19, 15, 25,
    22, 21]
  left_inv := by decide
  right_inv := by decide

/-- The map. -/
def M : CombMap where
  Dart := Fin 26
  dartFintype := inferInstance
  alpha := mAlpha
  sigma := mSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 26))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 26) n)

/-- The face classes `Π_i, Π_j, C, H, b, a` and the exterior are `0, …, 6`. -/
def faceClass : Fin 26 → Fin 7 :=
  ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6]
def faceRep : Fin 7 → Fin 26 := ![0, 3, 6, 9, 20, 22, 24]

theorem faceClass_facePerm : ∀ d : M.Dart, faceClass (M.facePerm d) = faceClass d := by
  decide +kernel

theorem faceClass_faceRep : ∀ i : Fin 7, faceClass (faceRep i) = i := by decide

theorem faceRep_sameCycle :
    ∀ d : M.Dart, M.facePerm.SameCycle (faceRep (faceClass d)) d := by
  decide +kernel

noncomputable def faceEquiv : M.Face ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep faceClass_facePerm faceClass_faceRep
    faceRep_sameCycle

def face (i : Fin 7) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 7) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  exact faceClass_faceRep i

theorem faceOf_eq_face (d : Fin 26) (i : Fin 7) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 7) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

/-- The vertex classes. -/
def vertexClass : Fin 26 → Fin 8 :=
  ![6, 3, 2, 7, 4, 5, 6, 1, 0, 6, 2, 3, 6, 0, 1, 6, 7, 5, 4, 7, 6, 7, 6, 7, 6, 7]
def vertexRep : Fin 8 → Fin 26 := ![8, 7, 2, 1, 4, 5, 0, 3]

theorem vertexClass_sigma : ∀ d : M.Dart, vertexClass (M.sigma d) = vertexClass d := by
  decide +kernel

theorem vertexClass_vertexRep : ∀ i : Fin 8, vertexClass (vertexRep i) = i := by decide

theorem vertexRep_sameCycle :
    ∀ d : M.Dart, M.sigma.SameCycle (vertexRep (vertexClass d)) d := by
  decide +kernel

noncomputable def vertexEquiv : M.Vertex ≃ Fin 8 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep vertexClass_sigma
    vertexClass_vertexRep vertexRep_sameCycle

theorem vertexOf_eq_of_class {d e : Fin 26} (h : vertexClass d = vertexClass e) :
    M.vertexOf d = M.vertexOf e := by
  apply vertexEquiv.injective
  exact h

theorem connected : M.IsConnected := by
  have trans {d e f : M.Dart} (hde : Relation.EqvGen M.Adjacent d e)
      (hef : Relation.EqvGen M.Adjacent e f) : Relation.EqvGen M.Adjacent d f :=
    .trans _ _ _ hde hef
  have h11 : Relation.EqvGen M.Adjacent 0 11 := .rel _ _ (Or.inl rfl)
  have h12 : Relation.EqvGen M.Adjacent 0 12 := .rel _ _ (Or.inr rfl)
  have h1 : Relation.EqvGen M.Adjacent 0 1 := trans h11 (.rel _ _ (Or.inr rfl))
  have h8 : Relation.EqvGen M.Adjacent 0 8 := trans h12 (.rel _ _ (Or.inl rfl))
  have h6 : Relation.EqvGen M.Adjacent 0 6 := trans h12 (.rel _ _ (Or.inr rfl))
  have h10 : Relation.EqvGen M.Adjacent 0 10 := trans h1 (.rel _ _ (Or.inl rfl))
  have h13 : Relation.EqvGen M.Adjacent 0 13 := trans h8 (.rel _ _ (Or.inr rfl))
  have h14 : Relation.EqvGen M.Adjacent 0 14 := trans h6 (.rel _ _ (Or.inl rfl))
  have h15 : Relation.EqvGen M.Adjacent 0 15 := trans h6 (.rel _ _ (Or.inr rfl))
  have h2 : Relation.EqvGen M.Adjacent 0 2 := trans h10 (.rel _ _ (Or.inr rfl))
  have h7 : Relation.EqvGen M.Adjacent 0 7 := trans h13 (.rel _ _ (Or.inl rfl))
  have h23 : Relation.EqvGen M.Adjacent 0 23 := trans h15 (.rel _ _ (Or.inl rfl))
  have h22 : Relation.EqvGen M.Adjacent 0 22 := trans h15 (.rel _ _ (Or.inr rfl))
  have h9 : Relation.EqvGen M.Adjacent 0 9 := trans h2 (.rel _ _ (Or.inl rfl))
  have h16 : Relation.EqvGen M.Adjacent 0 16 := trans h23 (.rel _ _ (Or.inr rfl))
  have h25 : Relation.EqvGen M.Adjacent 0 25 := trans h22 (.rel _ _ (Or.inl rfl))
  have h24 : Relation.EqvGen M.Adjacent 0 24 := trans h22 (.rel _ _ (Or.inr rfl))
  have h5 : Relation.EqvGen M.Adjacent 0 5 := trans h16 (.rel _ _ (Or.inl rfl))
  have h3 : Relation.EqvGen M.Adjacent 0 3 := trans h16 (.rel _ _ (Or.inr rfl))
  have h21 : Relation.EqvGen M.Adjacent 0 21 := trans h24 (.rel _ _ (Or.inl rfl))
  have h20 : Relation.EqvGen M.Adjacent 0 20 := trans h24 (.rel _ _ (Or.inr rfl))
  have h17 : Relation.EqvGen M.Adjacent 0 17 := trans h5 (.rel _ _ (Or.inr rfl))
  have h18 : Relation.EqvGen M.Adjacent 0 18 := trans h3 (.rel _ _ (Or.inl rfl))
  have h19 : Relation.EqvGen M.Adjacent 0 19 := trans h3 (.rel _ _ (Or.inr rfl))
  have h4 : Relation.EqvGen M.Adjacent 0 4 := trans h17 (.rel _ _ (Or.inl rfl))
  have hstep : ∀ d : Fin 26, Relation.EqvGen M.Adjacent 0 d := by
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
    · exact h24
    · exact h25
  intro d e
  exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)

theorem planar : M.IsPlanar := by
  constructor
  · exact connected
  · have hv : M.vertexCount = 8 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 7 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 26 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 13 := by omega
    rw [heq]
    norm_num
