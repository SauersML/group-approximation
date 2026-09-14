import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import Mathlib.GroupTheory.Perm.Sign
import GroupApproximation.Meta.AxiomGuard

/-!
# Three loops out of rotation order: the membership turning condition is too weak

`EnclosedFaceSet` (`ClosedWalkEnclosedSubdiagram`) asks that rotating from the reverse of a walk
dart, the first dart met on an edge of the walk lies on the walk.  It does not ask for the next
dart of the walk.  This model, found by lane ms-inverses-1, refutes
`EnclosedLeastAreaFilterStatement` and shows that `EnclosedFaceSetSucc` excludes the walk.

The map has six darts at one vertex: three loops `0/1`, `2/3`, `4/5` bounding the relator faces
`Π₁ = [0]`, `Π₂ = [2]`, `Π₃ = [4]`, and the exterior `[1,3,5]`.  The walk `[1,5,3]` lists the
exterior darts out of rotation order.  Every dart lies on an edge of the walk, so the first dart
met is one rotation step away, and it lies on the walk; `EnclosedFaceSet` holds for `{Π₁, Π₂, Π₃}`.

The group is `S₃ × S₃`, with letters `a = (τ, ρ)`, `b = (ρ, τ')` and `c = b⁻¹ h a⁻¹` for
`h = (τ'', ρ⁻¹)`, a conjugate of `a` (`τ, τ', τ''` transpositions, `ρ` a 3-cycle).

* `leastArea`: the boundary reads `c b a`, whose second coordinate is `1`.  The character
  `sign × sign` is `-1` on every relator and on `c b a`, so a filling has odd length.  No relator or
  inverse has second coordinate `1`, so one relator does not fill it.  So every filling has at least
  three relators, the number of cells.
* `walkWord_relatorProduct`: the inverse walk `[2,4,0]` reads `b c a = h`, one relator.
* `not_enclosedLeastAreaFilterStatement`: the filter would give `3 ≤ 1`.
* `not_enclosedFaceSetSucc`: at the dart `1` the first dart met is `3`, not the next dart `5`.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, "Hull's small cancellation theorem", through
Osin's Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedOutOfOrderModel

open Equiv GroupApproximation.HullSC GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-! ## The map -/

def alpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 6) where
  toFun := ![0, 3, 2, 5, 4, 1]
  invFun := ![0, 5, 2, 1, 4, 3]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 4 := ![0, 3, 1, 3, 2, 3]
def faceRep : Fin 4 → Fin 6 := ![0, 2, 4, 1]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

def vertexClass : Fin 6 → Fin 1 := ![0, 0, 0, 0, 0, 0]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass (![0] : Fin 1 → Fin 6)
    (by decide) (by decide) (by decide)

theorem vertexOf_eq_iff (d e : Fin 6) :
    M.vertexOf d = M.vertexOf e ↔ vertexClass d = vertexClass e := by
  rw [← vertexEquiv.injective.eq_iff]
  rfl

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .rel _ _ (Or.inr rfl)
      have h32 : Relation.EqvGen M.Adjacent 3 2 := .rel _ _ (Or.inr rfl)
      have h25 : Relation.EqvGen M.Adjacent 2 5 := .rel _ _ (Or.inr rfl)
      have h54 : Relation.EqvGen M.Adjacent 5 4 := .rel _ _ (Or.inr rfl)
      have h41 : Relation.EqvGen M.Adjacent 4 1 := .rel _ _ (Or.inr rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact trans (trans (trans (trans h03 h32) h25) h54) h41
      · exact trans h03 h32
      · exact h03
      · exact trans (trans (trans h03 h32) h25) h54
      · exact trans (trans h03 h32) h25
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 4 → List (Fin 6) := ![[0], [2], [4], [1, 3, 5]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 6)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 4) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-! ## The group and the letters -/

abbrev S3 := Perm (Fin 3)
abbrev G := S3 × S3

def tau : S3 := swap 0 1
def rho : S3 := swap 0 1 * swap 1 2
def tau' : S3 := swap 0 2
def tau'' : S3 := swap 1 2

def ga : G := (tau, rho)
def gb : G := (rho, tau')
def gh : G := (tau'', rho⁻¹)
def gc : G := gb⁻¹ * gh * ga⁻¹

/-- `h` is the conjugate of `a` by `(swap 0 2, swap 0 1)`. -/
def conjugator : G := (swap 0 2, swap 0 1)

theorem gh_eq_conj : gh = conjugator * ga * conjugator⁻¹ := by decide

/-- The letters `a, a⁻¹, b, b⁻¹, c, c⁻¹` on the darts `0, …, 5`. -/
def label (d : Fin 6) : RelLetter G Empty :=
  .base ((![ga, ga⁻¹, gb, gb⁻¹, gc, gc⁻¹] : Fin 6 → G) d)

def W : Set (List (RelLetter G Empty)) := {[.base ga], [.base gb], [.base gc]}

def cellA : RelatorCell M (face 3) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := [.base ga]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellB : RelatorCell M (face 3) W where
  face := face 1
  face_ne_outer := (face_eq_iff 1 3).not.mpr (by decide)
  word := [.base gb]
  word_mem := Or.inr (Or.inl rfl)
  conjugator := 1
  reversed := false

def cellC : RelatorCell M (face 3) W where
  face := face 2
  face_ne_outer := (face_eq_iff 2 3).not.mpr (by decide)
  word := [.base gc]
  word_mem := Or.inr (Or.inr rfl)
  conjugator := 1
  reversed := false

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 3
  faceBoundary := boundary
  relatorCells := [cellC, cellB, cellA]
  relatorCell_faces_nodup := by
    change [face 2, face 1, face 0].Nodup
    simp [face_eq_iff]
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gc] = (boundary (face 2)).darts.map label
      rw [boundary_face_darts]
      rfl
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gb] = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    obtain rfl := List.mem_singleton.mp hC
    change [RelLetter.base ga] = (boundary (face 0)).darts.map label
    rw [boundary_face_darts]
    rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellA, by simp, rfl⟩
    · exact Or.inl ⟨cellB, by simp, rfl⟩
    · exact Or.inl ⟨cellC, by simp, rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

/-! ## Least area -/

/-- The character `sign × sign`. -/
noncomputable def psi : G →* ℤˣ :=
  (Perm.sign.comp (MonoidHom.fst S3 S3)) * (Perm.sign.comp (MonoidHom.snd S3 S3))

theorem psi_apply (x : G) : psi x = Perm.sign x.1 * Perm.sign x.2 := rfl

theorem psi_ga : psi ga = -1 := by
  simp [psi_apply, ga, tau, rho, Perm.sign_swap']

theorem psi_gb : psi gb = -1 := by
  simp [psi_apply, gb, rho, tau', Perm.sign_swap']

theorem psi_gh : psi gh = -1 := by
  simp [psi_apply, gh, tau'', rho, Perm.sign_swap']

theorem psi_gc : psi gc = -1 := by
  rw [gc, map_mul, map_mul, map_inv, map_inv, psi_ga, psi_gb, psi_gh]
  simp

theorem psi_boundary : psi (gc * gb * ga) = -1 := by
  rw [map_mul, map_mul, psi_ga, psi_gb, psi_gc]
  simp

theorem listVal_relator {r : G} (hr : r ∈ RelLetter.listVal '' W) : psi r = -1 ∧ r.2 ≠ 1 := by
  obtain ⟨word, hword, rfl⟩ := hr
  rcases hword with rfl | rfl | rfl
  · rw [show RelLetter.listVal [RelLetter.base ga] = ga by decide]
    exact ⟨psi_ga, by decide⟩
  · rw [show RelLetter.listVal [RelLetter.base gb] = gb by decide]
    exact ⟨psi_gb, by decide⟩
  · rw [show RelLetter.listVal [RelLetter.base gc] = gc by decide]
    exact ⟨psi_gc, by decide⟩

/-- A relator product of `m` factors has character `(-1)^m`. -/
theorem psi_of_isRelatorProduct {m : ℕ} {x : G}
    (h : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m x) :
    psi x = (-1) ^ m := by
  induction h with
  | one => simp
  | base hr => simpa using (listVal_relator hr).1
  | inv _ ih => rw [map_inv, ih, Int.units_inv_eq_self]
  | conj c _ ih =>
      rw [map_mul, map_mul, map_inv, ih, mul_comm (psi c), mul_assoc, mul_inv_cancel, mul_one]
  | mul _ _ iha ihb =>
      rw [map_mul, iha, ihb]
      exact (pow_add _ _ _).symm

/-- A relator product with one factor is a signed conjugate of a relator. -/
theorem exists_conj_of_index_one {R : Set G} {n : ℕ} {x : G}
    (h : RelatorDefectBudget.IsRelatorProduct R n x) :
    n = 1 → ∃ r ∈ R, ∃ g : G, x = g * r * g⁻¹ ∨ x = g * r⁻¹ * g⁻¹ := by
  induction h with
  | one => intro hn; exact absurd hn (by decide)
  | base hr => intro _; exact ⟨_, hr, 1, Or.inl (by group)⟩
  | inv _ ih =>
      intro hn
      obtain ⟨r, hr, g, hg | hg⟩ := ih hn
      · exact ⟨r, hr, g, Or.inr (by rw [hg]; group)⟩
      · exact ⟨r, hr, g, Or.inl (by rw [hg]; group)⟩
  | conj c _ ih =>
      intro hn
      obtain ⟨r, hr, g, hg | hg⟩ := ih hn
      · exact ⟨r, hr, c * g, Or.inl (by rw [hg]; group)⟩
      · exact ⟨r, hr, c * g, Or.inr (by rw [hg]; group)⟩
  | @mul m n a b ha hb iha ihb =>
      intro hn
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [ha.eq_one_of_index_zero, one_mul]
        exact ihb (by omega)
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [hb.eq_one_of_index_zero, mul_one]
        exact iha (by omega)

theorem boundaryValue_eq : diagram.boundaryValue = gc * gb * ga := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 3)).darts.map label)) = _
  rw [boundary_face_darts]
  decide

/-- The boundary value is no signed conjugate of a relator: its second coordinate is `1`. -/
theorem boundary_not_conj {r : G} (hr : r ∈ RelLetter.listVal '' W) (g : G) :
    gc * gb * ga ≠ g * r * g⁻¹ ∧ gc * gb * ga ≠ g * r⁻¹ * g⁻¹ := by
  have hsnd : (gc * gb * ga).2 = 1 := by decide
  have hr2 := (listVal_relator hr).2
  constructor
  · intro h
    have h2 := congrArg Prod.snd h
    rw [hsnd, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv] at h2
    apply hr2
    calc r.2 = g.2⁻¹ * (g.2 * r.2 * g.2⁻¹) * g.2 := by group
      _ = g.2⁻¹ * 1 * g.2 := by rw [← h2]
      _ = 1 := by group
  · intro h
    have h2 := congrArg Prod.snd h
    rw [hsnd, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, Prod.snd_inv] at h2
    apply hr2
    calc r.2 = (g.2⁻¹ * (g.2 * r.2⁻¹ * g.2⁻¹) * g.2)⁻¹ := by group
      _ = (g.2⁻¹ * 1 * g.2)⁻¹ := by rw [← h2]
      _ = 1 := by group

/-- **The diagram has least area.** -/
theorem leastArea : diagram.LeastArea := by
  intro m hm
  rw [boundaryValue_eq] at hm
  show 3 ≤ m
  by_contra hlt
  have hlt' : m < 3 := by omega
  have hpar := psi_of_isRelatorProduct hm
  rw [psi_boundary] at hpar
  interval_cases m
  · exact absurd hm.eq_one_of_index_zero (by decide)
  · obtain ⟨r, hr, g, hg | hg⟩ := exists_conj_of_index_one hm rfl
    · exact (boundary_not_conj hr g).1 hg
    · exact (boundary_not_conj hr g).2 hg
  · exact absurd hpar (by decide)

/-! ## The out-of-order walk -/

/-- The exterior darts, listed out of rotation order. -/
def outerWalk : List M.Dart := [1, 5, 3]

open scoped Classical in
/-- The three relator faces. -/
noncomputable def outFaces : Finset M.Face := Finset.univ.erase (face 3)

theorem mem_outFaces (d : Fin 6) : M.faceOf d ∈ outFaces ↔ faceClass d ≠ 3 := by
  classical
  simp only [outFaces, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, faceOf_eq_face]

theorem walkKeep_all (x : M.Dart) : walkKeep M outerWalk x := by
  unfold walkKeep
  fin_cases x <;> decide

theorem sigma_alpha_mem (d : M.Dart) : d ∈ outerWalk → M.sigma (M.alpha d) ∈ outerWalk := by
  fin_cases d <;> decide

/-- **`{Π₁, Π₂, Π₃}` is enclosed by the out-of-order walk.** -/
theorem enclosedFaceSet : EnclosedFaceSet diagram outFaces outerWalk where
  outerFace_not_mem := by
    change M.faceOf (1 : M.Dart) ∉ outFaces
    rw [mem_outFaces]
    decide
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := by
    change List.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) outerWalk
    simp only [vertexOf_eq_iff]
    decide
  closes := (vertexOf_eq_iff (M.alpha 3) 1).mpr (by decide)
  mem_iff := by
    intro d
    change d ∈ outerWalk ↔ M.faceOf d ∉ outFaces ∧
      (M.faceOf (M.alpha d) ∈ outFaces ∨ M.alpha d ∈ outerWalk)
    simp only [mem_outFaces]
    fin_cases d <;> decide
  turn_mem := by
    intro d hd m hm hkeep hmin
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · exact absurd (walkKeep_all _) (hmin 1 Nat.one_pos h1)
    · obtain rfl : m = 1 := by omega
      rw [pow_one]
      exact sigma_alpha_mem d hd

/-- **The inverse walk reads one relator.** -/
theorem walkWord_relatorProduct :
    RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 1
      (RelLetter.listVal (Embedded.dartWord diagram (Embedded.invDarts diagram outerWalk))) := by
  rw [show RelLetter.listVal (Embedded.dartWord diagram (Embedded.invDarts diagram outerWalk)) =
      conjugator * ga * conjugator⁻¹ by decide]
  exact RelatorDefectBudget.IsRelatorProduct.conj conjugator
    (RelatorDefectBudget.IsRelatorProduct.base ⟨[.base ga], Or.inl rfl, by decide⟩)

theorem cells_mem_outFaces : ∀ C ∈ diagram.relatorCells, C.face ∈ outFaces := by
  classical
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact Finset.mem_erase.mpr ⟨(face_eq_iff 2 3).not.mpr (by decide), Finset.mem_univ _⟩
  rcases List.mem_cons.mp hC with rfl | hC
  · exact Finset.mem_erase.mpr ⟨(face_eq_iff 1 3).not.mpr (by decide), Finset.mem_univ _⟩
  obtain rfl := List.mem_singleton.mp hC
  exact Finset.mem_erase.mpr ⟨(face_eq_iff 0 3).not.mpr (by decide), Finset.mem_univ _⟩

/-- A filter keeping every entry keeps the length, for any decision procedure. -/
theorem length_filter_of_all {α : Type*} (l : List α) (p : α → Bool) (hp : ∀ a ∈ l, p a = true) :
    (l.filter p).length = l.length := by
  rw [List.filter_eq_self.mpr hp]

/-- **The membership turning condition does not give the least-area filter.** -/
theorem not_enclosedLeastAreaFilterStatement : ¬ EnclosedLeastAreaFilterStatement.{0, 0, 0} := by
  intro h
  have hle := h diagram leastArea outFaces outerWalk enclosedFaceSet walkWord_relatorProduct
  refine absurd (le_trans (le_of_eq (length_filter_of_all diagram.relatorCells _ ?_).symm) hle)
    (by decide)
  intro C hC
  have h := cells_mem_outFaces C hC
  simp only [decide_eq_true_eq]
  exact h

/-- **The walk does not turn to its successor**: from the dart `1` the first dart met is `3`, while
the next dart of the walk is `5`. -/
theorem not_enclosedFaceSetSucc : ¬ EnclosedFaceSetSucc diagram outFaces outerWalk := by
  intro h
  have hnext := h.turn_next 0 (by decide) 1 Nat.one_pos (walkKeep_all _)
    (fun k hk hk1 => absurd hk1 (by omega))
  revert hnext
  decide

end GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedOutOfOrderModel

open GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedOutOfOrderModel

#audit_axioms planar
#audit_axioms diagram
#audit_axioms leastArea
#audit_axioms enclosedFaceSet
#audit_axioms walkWord_relatorProduct
#audit_axioms not_enclosedLeastAreaFilterStatement
#audit_axioms not_enclosedFaceSetSucc
