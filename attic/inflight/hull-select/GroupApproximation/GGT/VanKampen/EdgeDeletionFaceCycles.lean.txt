import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceRotation
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionConnected
import GroupApproximation.Meta.AxiomGuard

/-!
# Face cycles across the deletion of an edge between two faces

Let `a` be a dart whose two sides lie on distinct faces, enumerated from the edge
as the face cycles `a :: xs` and `alpha a :: ys` (`EdgeDeletion.MergeCycles`).
Deleting the edge of `a` merges the two faces into one face enumerated by
`xs ++ ys`, and every other face of the deleted map is a face of the original map
with the same darts.  This is the inductive step of the planar van Kampen lemma
(`PlanarVanKampen`).

* `EdgeDeletion.next`, `EdgeDeletion.isFaceCycle_iff`: face cycles of the deleted
  map, read through `EdgeDeletion.value`, are the cycles of `next`.
* `EdgeDeletion.isFaceCycle_map_value`: a face cycle of the deleted map that never
  steps onto the deleted edge is a face cycle of the original map.
* `EdgeDeletion.exists_map_value_eq`: lists avoiding the deleted edge lift.
* `EdgeDeletion.MergeCycles.isFaceCycle_lift`: the lift of `xs ++ ys` is a face
  cycle of the deleted map.
* `EdgeDeletion.MergeCycles.isFaceCycle_map_value_of_ne`, `.faceOf_value_eq`,
  `.faceOf_eq_of_faceOf_value_eq`, `.exists_value_eq_of_faceOf_ne`: the faces of
  the deleted map other than the merged face are the faces of the original map
  other than the two merged ones.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv

universe u

/-- The last entry of a nonempty list with a given head, read through `getLast?`. -/
theorem getLast_cons_eq_getD {α : Type u} (x : α) (l : List α) (h : x :: l ≠ []) :
    (x :: l).getLast h = l.getLast?.getD x :=
  Option.some.inj ((List.getLast?_eq_some_getLast h).symm.trans List.getLast?_cons)

namespace EdgeDeletion

section Lift

variable (M : CombMap.{u}) (a : M.Dart)

/-- **A list of darts avoiding the deleted edge lifts to the deleted map.** -/
theorem exists_map_value_eq (l : List M.Dart) (h : ∀ x ∈ l, x ≠ a ∧ x ≠ M.alpha a) :
    ∃ l' : List (Dart M a), l'.map (value M a) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
      obtain ⟨l', hl'⟩ := ih fun y hy => h y (List.mem_cons_of_mem x hy)
      have hx := h x List.mem_cons_self
      exact ⟨ofValue M a x hx.1 hx.2 :: l', congrArg (List.cons x) hl'⟩

end Lift

section Next

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- **The successor of a dart after deleting the edge of `a`**, read in the original
map (`EdgeDeletion.value_facePerm_general`). -/
def next (d : M.Dart) : M.Dart :=
  if M.facePerm d = a then
    (if M.facePerm (M.alpha a) = M.alpha a then M.facePerm a else M.facePerm (M.alpha a))
  else if M.facePerm d = M.alpha a then
    (if M.facePerm a = a then M.facePerm (M.alpha a) else M.facePerm a)
  else M.facePerm d

theorem value_facePerm_eq_next (x : Dart M a) :
    value M a ((toCombMap M a).facePerm x) = next M a (value M a x) :=
  value_facePerm_general M a x

theorem next_of_ne_of_ne {d : M.Dart} (h1 : M.facePerm d ≠ a)
    (h2 : M.facePerm d ≠ M.alpha a) : next M a d = M.facePerm d := by
  rw [next, if_neg h1, if_neg h2]

/-- The face rotation of the deleted map, read through `value`. -/
theorem facePerm_eq_iff (x y : Dart M a) :
    (toCombMap M a).facePerm x = y ↔ next M a (value M a x) = value M a y := by
  rw [← value_facePerm_eq_next]
  exact (value_injective M a).eq_iff.symm

/-- **Face cycles of the deleted map are the cycles of `next`**, read through
`value`. -/
theorem isFaceCycle_iff (l : List (Dart M a)) :
    (toCombMap M a).IsFaceCycle l ↔
      ∃ h : l ≠ [], (l.map (value M a)).Nodup ∧
        (l.map (value M a)).IsChain (fun d e => next M a d = e) ∧
        next M a (value M a (l.getLast h)) = value M a (l.head h) := by
  have hchain : (l.map (value M a)).IsChain (fun d e => next M a d = e) ↔
      l.IsChain (fun x y => (toCombMap M a).facePerm x = y) := by
    rw [List.isChain_map]
    exact List.IsChain.iff fun x y => (facePerm_eq_iff M a x y).symm
  constructor
  · intro hl
    exact ⟨hl.ne_nil, hl.nodup.map (value_injective M a), hchain.mpr hl.chain,
      (facePerm_eq_iff M a _ _).mp hl.closes⟩
  · rintro ⟨hne, hnd, hch, hcl⟩
    exact ⟨hne, hnd.of_map _, hchain.mp hch, (facePerm_eq_iff M a _ _).mpr hcl⟩

/-- **A cycle of `next` avoiding the deleted edge lifts to a face cycle.** -/
theorem isFaceCycle_of_map_value {l : List (Dart M a)} {L : List M.Dart}
    (hL : l.map (value M a) = L) (hne : L ≠ []) (hnd : L.Nodup)
    (hch : L.IsChain (fun d e => next M a d = e))
    (hcl : ∀ u ∈ L.getLast?, ∀ v ∈ L.head?, next M a u = v) :
    (toCombMap M a).IsFaceCycle l := by
  subst hL
  have hl : l ≠ [] := by simpa using hne
  refine (isFaceCycle_iff M a l).mpr ⟨hl, hnd, hch, ?_⟩
  refine hcl _ ?_ _ ?_
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast hl]
    exact rfl
  · rw [List.head?_map, List.head?_eq_some_head hl]
    exact rfl

/-- **A face cycle of the deleted map that never steps onto the deleted edge is a
face cycle of the original map.** -/
theorem isFaceCycle_map_value {l : List (Dart M a)} (hl : (toCombMap M a).IsFaceCycle l)
    (hgood : ∀ x ∈ l, M.facePerm (value M a x) ≠ a ∧
      M.facePerm (value M a x) ≠ M.alpha a) :
    M.IsFaceCycle (l.map (value M a)) := by
  obtain ⟨hne, hnd, hch, hcl⟩ := (isFaceCycle_iff M a l).mp hl
  have hnext : ∀ x ∈ l, next M a (value M a x) = M.facePerm (value M a x) :=
    fun x hx => next_of_ne_of_ne M a (hgood x hx).1 (hgood x hx).2
  refine ⟨by simpa using hne, hnd, ?_, ?_⟩
  · refine hch.imp_of_mem_imp fun d e hd _ h => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    exact (hnext x hx).symm.trans h
  · rw [List.getLast_map, List.head_map, ← hnext _ (List.getLast_mem _)]
    exact hcl

end Next

/-- **The two sides of an edge on distinct faces**, each enumerated as a face cycle
starting from that side. -/
structure MergeCycles (M : CombMap.{u}) (a : M.Dart) where
  /-- The face of `a`, after `a`. -/
  xs : List M.Dart
  /-- The face of `alpha a`, after `alpha a`. -/
  ys : List M.Dart
  /-- The face of `a`. -/
  cycO : M.IsFaceCycle (a :: xs)
  /-- The face of `alpha a`. -/
  cycG : M.IsFaceCycle (M.alpha a :: ys)
  /-- The two sides lie on distinct faces. -/
  face_ne : M.faceOf a ≠ M.faceOf (M.alpha a)

namespace MergeCycles

variable {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a)

theorem ne_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : d ≠ a := by
  rintro rfl
  exact (List.nodup_cons.mp C.cycO.nodup).1 hd

theorem faceOf_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : M.faceOf d = M.faceOf a :=
  (C.cycO.mem_iff d).mp (List.mem_cons_of_mem a hd)

theorem faceOf_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) :
    M.faceOf d = M.faceOf (M.alpha a) :=
  (C.cycG.mem_iff d).mp (List.mem_cons_of_mem (M.alpha a) hd)

theorem ne_alpha_of_mem_xs {d : M.Dart} (hd : d ∈ C.xs) : d ≠ M.alpha a := by
  rintro rfl
  exact C.face_ne (C.faceOf_of_mem_xs hd).symm

theorem ne_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) : d ≠ a := by
  rintro rfl
  exact C.face_ne (C.faceOf_of_mem_ys hd)

theorem ne_alpha_of_mem_ys {d : M.Dart} (hd : d ∈ C.ys) : d ≠ M.alpha a := by
  rintro rfl
  exact (List.nodup_cons.mp C.cycG.nodup).1 hd

theorem mem_xs_of_faceOf {d : M.Dart} (hd : M.faceOf d = M.faceOf a) (hne : d ≠ a) :
    d ∈ C.xs := by
  rcases List.mem_cons.mp ((C.cycO.mem_iff d).mpr hd) with h | h
  · exact absurd h hne
  · exact h

theorem mem_ys_of_faceOf {d : M.Dart} (hd : M.faceOf d = M.faceOf (M.alpha a))
    (hne : d ≠ M.alpha a) : d ∈ C.ys := by
  rcases List.mem_cons.mp ((C.cycG.mem_iff d).mpr hd) with h | h
  · exact absurd h hne
  · exact h

/-- The merged enumeration has no repeated dart. -/
theorem nodup_append : (C.xs ++ C.ys).Nodup :=
  List.nodup_append.mpr ⟨(List.nodup_cons.mp C.cycO.nodup).2,
    (List.nodup_cons.mp C.cycG.nodup).2, fun d hd e he hde => by
      subst hde
      exact C.face_ne ((C.faceOf_of_mem_xs hd).symm.trans (C.faceOf_of_mem_ys he))⟩

/-- The merged enumeration avoids the deleted edge. -/
theorem avoid {d : M.Dart} (hd : d ∈ C.xs ++ C.ys) : d ≠ a ∧ d ≠ M.alpha a := by
  rcases List.mem_append.mp hd with h | h
  · exact ⟨C.ne_of_mem_xs h, C.ne_alpha_of_mem_xs h⟩
  · exact ⟨C.ne_of_mem_ys h, C.ne_alpha_of_mem_ys h⟩

theorem faceOf_of_mem_append {d : M.Dart} (hd : d ∈ C.xs ++ C.ys) :
    M.faceOf d = M.faceOf a ∨ M.faceOf d = M.faceOf (M.alpha a) := by
  rcases List.mem_append.mp hd with h | h
  · exact Or.inl (C.faceOf_of_mem_xs h)
  · exact Or.inr (C.faceOf_of_mem_ys h)

theorem mem_append_of_faceOf {d : M.Dart}
    (hd : M.faceOf d = M.faceOf a ∨ M.faceOf d = M.faceOf (M.alpha a))
    (h1 : d ≠ a) (h2 : d ≠ M.alpha a) : d ∈ C.xs ++ C.ys := by
  rcases hd with hd | hd
  · exact List.mem_append.mpr (Or.inl (C.mem_xs_of_faceOf hd h1))
  · exact List.mem_append.mpr (Or.inr (C.mem_ys_of_faceOf hd h2))

/-- The last dart of the face of `a` returns to `a`. -/
theorem facePerm_getD_last_xs : M.facePerm (C.xs.getLast?.getD a) = a := by
  have h := C.cycO.closes
  rw [getLast_cons_eq_getD] at h
  exact h

/-- The last dart of the face of `alpha a` returns to `alpha a`. -/
theorem facePerm_getD_last_ys :
    M.facePerm (C.ys.getLast?.getD (M.alpha a)) = M.alpha a := by
  have h := C.cycG.closes
  rw [getLast_cons_eq_getD] at h
  exact h

/-- The successor of `a` heads the rest of its face. -/
theorem facePerm_eq_getD_head_xs : M.facePerm a = C.xs.head?.getD a := by
  have hlast := C.facePerm_getD_last_xs
  have hchain := (List.isChain_cons.mp C.cycO.chain).1
  revert hlast hchain
  cases C.xs with
  | nil => exact fun h _ => h
  | cons y t => exact fun _ h => h y rfl

/-- The successor of `alpha a` heads the rest of its face. -/
theorem facePerm_alpha_eq_getD_head_ys :
    M.facePerm (M.alpha a) = C.ys.head?.getD (M.alpha a) := by
  have hlast := C.facePerm_getD_last_ys
  have hchain := (List.isChain_cons.mp C.cycG.chain).1
  revert hlast hchain
  cases C.ys with
  | nil => exact fun h _ => h
  | cons y t => exact fun _ h => h y rfl

/-- A surviving dart whose value lies on either merged face lies on the lift of the
merged enumeration. -/
theorem mem_lift_of_faceOf {l : List (Dart M a)} (hl : l.map (value M a) = C.xs ++ C.ys)
    {x : Dart M a} (hx : M.faceOf (value M a x) = M.faceOf a ∨
      M.faceOf (value M a x) = M.faceOf (M.alpha a)) : x ∈ l := by
  have hmem : value M a x ∈ l.map (value M a) := by
    rw [hl]
    exact C.mem_append_of_faceOf hx (value_ne M a x) (value_ne_reverse M a x)
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hmem
  rwa [value_injective M a hxy] at hy

variable [DecidableEq M.Dart]

/-- The merged enumeration follows `next`. -/
theorem isChain_next_append :
    (C.xs ++ C.ys).IsChain (fun d e => next M a d = e) := by
  have hxs : C.xs.IsChain (fun d e => next M a d = e) :=
    (List.isChain_cons.mp C.cycO.chain).2.imp_of_mem_imp fun d e _ he h => by
      have h' : M.facePerm d = e := h
      have h1 : M.facePerm d ≠ a := by rw [h']; exact C.ne_of_mem_xs he
      have h2 : M.facePerm d ≠ M.alpha a := by rw [h']; exact C.ne_alpha_of_mem_xs he
      show next M a d = e
      rw [next_of_ne_of_ne M a h1 h2, h']
  have hys : C.ys.IsChain (fun d e => next M a d = e) :=
    (List.isChain_cons.mp C.cycG.chain).2.imp_of_mem_imp fun d e _ he h => by
      have h' : M.facePerm d = e := h
      have h1 : M.facePerm d ≠ a := by rw [h']; exact C.ne_of_mem_ys he
      have h2 : M.facePerm d ≠ M.alpha a := by rw [h']; exact C.ne_alpha_of_mem_ys he
      show next M a d = e
      rw [next_of_ne_of_ne M a h1 h2, h']
  refine hxs.append hys fun x hx y hy => ?_
  have hlast := C.facePerm_getD_last_xs
  have hhead := C.facePerm_alpha_eq_getD_head_ys
  have hx' : C.xs.getLast? = some x := hx
  have hy' : C.ys.head? = some y := hy
  rw [hx'] at hlast
  rw [hy'] at hhead
  have hlast' : M.facePerm x = a := hlast
  have hhead' : M.facePerm (M.alpha a) = y := hhead
  have hyα : M.facePerm (M.alpha a) ≠ M.alpha a := by
    rw [hhead']
    exact C.ne_alpha_of_mem_ys (List.mem_of_mem_head? hy)
  show next M a x = y
  rw [next, if_pos hlast', if_neg hyα, hhead']

/-- The merged enumeration closes up under `next`. -/
theorem next_last_eq_head :
    ∀ u ∈ (C.xs ++ C.ys).getLast?, ∀ v ∈ (C.xs ++ C.ys).head?, next M a u = v := by
  intro u hu v hv
  have hlastO := C.facePerm_getD_last_xs
  have hlastG := C.facePerm_getD_last_ys
  have hfa := C.facePerm_eq_getD_head_xs
  have hfαa := C.facePerm_alpha_eq_getD_head_ys
  have hxa : ∀ x ∈ C.xs.head?, x ≠ a := fun x hx =>
    C.ne_of_mem_xs (List.mem_of_mem_head? hx)
  have hu' : (C.xs ++ C.ys).getLast? = some u := hu
  have hv' : (C.xs ++ C.ys).head? = some v := hv
  clear hu hv
  have hαa : M.alpha a ≠ a := M.alpha_fixedPointFree a
  revert hlastO hlastG hfa hfαa hxa hu' hv'
  cases C.xs with
  | nil =>
    cases C.ys with
    | nil =>
      intro _ _ _ _ _ hu' _
      exact absurd hu' (by simp)
    | cons y t =>
      intro _ hlastG hfa hfαa _ hu' hv'
      have hU : (y :: t).getLast (List.cons_ne_nil y t) = u := Option.some.inj hu'
      have hlast : M.facePerm ((y :: t).getLast (List.cons_ne_nil y t)) = M.alpha a := hlastG
      rw [hU] at hlast
      have hvy : y = v := Option.some.inj hv'
      have hfa' : M.facePerm a = a := hfa
      have hfαa' : M.facePerm (M.alpha a) = y := hfαa
      have hne1 : M.facePerm u ≠ a := by
        rw [hlast]
        exact hαa
      rw [next, if_neg hne1, if_pos hlast, if_pos hfa', hfαa', hvy]
  | cons x s =>
    cases C.ys with
    | nil =>
      intro hlastO _ hfa hfαa _ hu' hv'
      rw [List.append_nil] at hu' hv'
      have hU : (x :: s).getLast (List.cons_ne_nil x s) = u := Option.some.inj hu'
      have hlast : M.facePerm ((x :: s).getLast (List.cons_ne_nil x s)) = a := hlastO
      rw [hU] at hlast
      have hvx : x = v := Option.some.inj hv'
      have hfa' : M.facePerm a = x := hfa
      have hfαa' : M.facePerm (M.alpha a) = M.alpha a := hfαa
      rw [next, if_pos hlast, if_pos hfαa', hfa', hvx]
    | cons y t =>
      intro _ hlastG hfa _ hxa hu' hv'
      rw [List.getLast?_append] at hu'
      have hU : (y :: t).getLast (List.cons_ne_nil y t) = u := Option.some.inj hu'
      have hlast : M.facePerm ((y :: t).getLast (List.cons_ne_nil y t)) = M.alpha a := hlastG
      rw [hU] at hlast
      have hvx : x = v := Option.some.inj hv'
      have hfa' : M.facePerm a = x := hfa
      have hxa' : x ≠ a := hxa x rfl
      have hne1 : M.facePerm u ≠ a := by
        rw [hlast]
        exact hαa
      have hne2 : M.facePerm a ≠ a := by
        rw [hfa']
        exact hxa'
      rw [next, if_neg hne1, if_pos hlast, if_neg hne2, hfa', hvx]

/-- **The merged face.**  The lift of `xs ++ ys` is a face cycle of the deleted
map. -/
theorem isFaceCycle_lift (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) : (toCombMap M a).IsFaceCycle l :=
  isFaceCycle_of_map_value M a hl hne C.nodup_append C.isChain_next_append
    C.next_last_eq_head

/-- A surviving dart off the merged face has its value off both merged faces. -/
theorem faceOf_value_ne (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {x : Dart M a} (hx : (toCombMap M a).faceOf x ≠ (toCombMap M a).faceOf x₀) :
    M.faceOf (value M a x) ≠ M.faceOf a ∧
      M.faceOf (value M a x) ≠ M.faceOf (M.alpha a) := by
  have hcyc := C.isFaceCycle_lift hne hl
  have hkey : ∀ y ∈ l, (toCombMap M a).faceOf y = (toCombMap M a).faceOf x₀ := fun y hy =>
    ((hcyc.mem_iff y).mp hy).trans ((hcyc.mem_iff x₀).mp hx₀).symm
  exact ⟨fun h => hx (hkey x (C.mem_lift_of_faceOf hl (Or.inl h))),
    fun h => hx (hkey x (C.mem_lift_of_faceOf hl (Or.inr h)))⟩

/-- A surviving dart off the merged face never steps onto the deleted edge. -/
theorem facePerm_value_ne (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {x : Dart M a} (hx : (toCombMap M a).faceOf x ≠ (toCombMap M a).faceOf x₀) :
    M.facePerm (value M a x) ≠ a ∧ M.facePerm (value M a x) ≠ M.alpha a := by
  obtain ⟨h1, h2⟩ := C.faceOf_value_ne hne hl hx₀ hx
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [← M.faceOf_facePerm (value M a x), h]
  · rw [← M.faceOf_facePerm (value M a x), h]

/-- **Every other face.**  A face cycle of the deleted map off the merged face is a
face cycle of the original map. -/
theorem isFaceCycle_map_value_of_ne (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {l' : List (Dart M a)} (hl' : (toCombMap M a).IsFaceCycle l')
    (hoff : (toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠ (toCombMap M a).faceOf x₀) :
    M.IsFaceCycle (l'.map (value M a)) :=
  isFaceCycle_map_value M a hl' fun x hx =>
    C.facePerm_value_ne hne hl hx₀ fun h => hoff (((hl'.mem_iff x).mp hx).symm.trans h)

/-- Two surviving darts on one face off the merged face have values on one face. -/
theorem faceOf_value_eq (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {x y : Dart M a} (hxy : (toCombMap M a).faceOf x = (toCombMap M a).faceOf y)
    (hx : (toCombMap M a).faceOf x ≠ (toCombMap M a).faceOf x₀) :
    M.faceOf (value M a x) = M.faceOf (value M a y) := by
  obtain ⟨l', hl', hhead⟩ := (toCombMap M a).exists_isFaceCycle_head x
  have hoff : (toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠ (toCombMap M a).faceOf x₀ := by
    rw [hhead]
    exact hx
  have hM := C.isFaceCycle_map_value_of_ne hne hl hx₀ hl' hoff
  have hy : y ∈ l' := (hl'.mem_iff y).mpr (by rw [hhead]; exact hxy.symm)
  have hmem := (hM.mem_iff (value M a y)).mp (List.mem_map.mpr ⟨y, hy, rfl⟩)
  have hx' : M.faceOf ((l'.map (value M a)).head hM.ne_nil) = M.faceOf (value M a x) :=
    congrArg M.faceOf ((List.head_map hM.ne_nil).trans (congrArg (value M a) hhead))
  exact (hmem.trans hx').symm

/-- Conversely, surviving darts off the merged face with values on one face lie on
one face. -/
theorem faceOf_eq_of_faceOf_value_eq (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {x y : Dart M a} (hx : (toCombMap M a).faceOf x ≠ (toCombMap M a).faceOf x₀)
    (hxy : M.faceOf (value M a x) = M.faceOf (value M a y)) :
    (toCombMap M a).faceOf x = (toCombMap M a).faceOf y := by
  obtain ⟨l', hl', hhead⟩ := (toCombMap M a).exists_isFaceCycle_head x
  have hoff : (toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠ (toCombMap M a).faceOf x₀ := by
    rw [hhead]
    exact hx
  have hM := C.isFaceCycle_map_value_of_ne hne hl hx₀ hl' hoff
  have hmem : value M a y ∈ l'.map (value M a) :=
    (hM.mem_iff _).mpr (hxy.symm.trans (congrArg M.faceOf
      ((congrArg (value M a) hhead).symm.trans (List.head_map hM.ne_nil).symm)))
  obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hmem
  rw [value_injective M a hzy] at hz
  have hface := (hl'.mem_iff y).mp hz
  rw [hhead] at hface
  exact hface.symm

/-- Every dart off both merged faces is the value of a surviving dart off the merged
face. -/
theorem exists_value_eq_of_faceOf_ne (hne : C.xs ++ C.ys ≠ []) {l : List (Dart M a)}
    (hl : l.map (value M a) = C.xs ++ C.ys) {x₀ : Dart M a} (hx₀ : x₀ ∈ l)
    {d : M.Dart} (h1 : M.faceOf d ≠ M.faceOf a) (h2 : M.faceOf d ≠ M.faceOf (M.alpha a)) :
    ∃ x : Dart M a, value M a x = d ∧
      (toCombMap M a).faceOf x ≠ (toCombMap M a).faceOf x₀ := by
  have hda : d ≠ a := fun h => h1 (by rw [h])
  have hdα : d ≠ M.alpha a := fun h => h2 (by rw [h])
  refine ⟨ofValue M a d hda hdα, rfl, fun h => ?_⟩
  have hcyc := C.isFaceCycle_lift hne hl
  have hmem : ofValue M a d hda hdα ∈ l :=
    (hcyc.mem_iff _).mpr (h.trans ((hcyc.mem_iff x₀).mp hx₀))
  have hv : d ∈ C.xs ++ C.ys := by
    rw [← hl]
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  rcases C.faceOf_of_mem_append hv with h' | h'
  · exact h1 h'
  · exact h2 h'

end MergeCycles

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.isFaceCycle_map_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.isFaceCycle_lift
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceOf_value_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceOf_eq_of_faceOf_value_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.exists_value_eq_of_faceOf_ne
