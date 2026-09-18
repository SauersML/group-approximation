import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Classes
import GroupApproximation.Meta.AxiomGuard

/-!
# The finite checks behind the refutation of `RoseExtremalJunctionStatement`

Lane gl-p10-51.

For the walk class `c = cid r`, the moved darts of the pocket walk are
`roseJunctionRefute_F c` (`roseJunctionRefute_filtC2`, …, `roseJunctionRefute_filtC5`).
* `c = 2`, `c = 4`: the dart `4`, resp. `10`, meets no other moved dart at a vertex
  (`roseJunctionRefute_isoC2`, `roseJunctionRefute_isoC4`), so a walk through all moved darts
  has at most one dart (`roseJunctionRefute_isolated`).
* `c = 3`, `c = 5`: a window of the cell `S` read backwards, resp. of the exterior boundary,
  inside the moved darts has at most `3`, `5`, resp. `6`, `2` darts, with the listed windows at
  the maximum (`roseJunctionRefute_w1c3`, …).  The one free dart between the two windows then
  meets neither junction (`roseJunctionRefute_endC3`, `roseJunctionRefute_endC5a`, `…_endC5b`).

Proof route: `decide` on the windows `(L.drop n ++ L.take n).take m` for all `n`, `m`.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

/-- **A walk through a dart meeting no other dart of the walk has at most one dart.** -/
theorem roseJunctionRefute_isolated {α : Type*} {R : α → α → Prop} (x : α) :
    ∀ l : List α, l.IsChain R → l.Nodup → x ∈ l → (∀ y ∈ l, y ≠ x → ¬R x y ∧ ¬R y x) →
      l.length ≤ 1
  | [], _, _, _, _ => Nat.zero_le _
  | [_], _, _, _, _ => Nat.le_refl 1
  | a :: b :: t, hc, hnd, hx, hiso => by
    obtain ⟨hab, hbt⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨ha, hbnd⟩ := List.nodup_cons.mp hnd
    have hba : b ≠ a := fun h => ha (by subst h; exact List.mem_cons_self)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact absurd hab (hiso b (List.mem_cons_of_mem _ List.mem_cons_self) hba).1
    · rcases List.mem_cons.mp hx with rfl | hxt
      · exact absurd hab (hiso a List.mem_cons_self hba.symm).2
      · have h := roseJunctionRefute_isolated x (b :: t) hbt hbnd hx
          fun y hy hne => hiso y (List.mem_cons_of_mem _ hy) hne
        have hpos := List.length_pos_of_mem hxt
        simp only [List.length_cons] at h
        omega

/-- The darts of an arc, through an equation for its cycle. -/
theorem roseJunctionRefute_arcDarts {α : Type*} {l L : List α} (h : l = L)
    (t : Embedded.CyclicArc l) :
    t.darts = (L.drop t.start.1 ++ L.take t.start.1).take t.length := by
  subst h
  rfl

/-- The window at `n` of length `m` of the cell `S`, read backwards. -/
def roseJunctionRefute_win1 (n m : ℕ) : List roseJunctionRefute_X.toCombMap.Dart :=
  Embedded.invDarts roseJunctionRefute_X
    ((([19, 7, 5, 17, 3, 14, 1] : List roseJunctionRefute_X.toCombMap.Dart).drop n ++
      ([19, 7, 5, 17, 3, 14, 1] : List roseJunctionRefute_X.toCombMap.Dart).take n).take m)

/-- The window at `p` of length `q` of the exterior boundary. -/
def roseJunctionRefute_win2 (p q : ℕ) : List roseJunctionRefute_X.toCombMap.Dart :=
  (([8, 20, 10, 12, 22, 14] : List roseJunctionRefute_X.toCombMap.Dart).drop p ++
    ([8, 20, 10, 12, 22, 14] : List roseJunctionRefute_X.toCombMap.Dart).take p).take q

/-- The moved darts of the class `2`. -/
def roseJunctionRefute_F2 : List roseJunctionRefute_X.toCombMap.Dart := [0, 4, 8, 20, 10, 12, 22]

/-- The moved darts of the class `3`. -/
def roseJunctionRefute_F3 : List roseJunctionRefute_X.toCombMap.Dart :=
  [0, 2, 16, 6, 18, 8, 20, 10, 12, 22]

/-- The moved darts of the class `4`. -/
def roseJunctionRefute_F4 : List roseJunctionRefute_X.toCombMap.Dart := [0, 2, 16, 4, 6, 18, 10]

/-- The moved darts of the class `5`. -/
def roseJunctionRefute_F5 : List roseJunctionRefute_X.toCombMap.Dart :=
  [0, 2, 16, 4, 6, 18, 8, 20, 12, 22]

theorem roseJunctionRefute_filtC2 : roseJunctionRefute_pK.boundary.cycle.filter
    (roseJunctionRefute_keptTab 2) = roseJunctionRefute_F2 := by
  decide

theorem roseJunctionRefute_filtC3 : roseJunctionRefute_pK.boundary.cycle.filter
    (roseJunctionRefute_keptTab 3) = roseJunctionRefute_F3 := by
  decide

theorem roseJunctionRefute_filtC4 : roseJunctionRefute_pK.boundary.cycle.filter
    (roseJunctionRefute_keptTab 4) = roseJunctionRefute_F4 := by
  decide

theorem roseJunctionRefute_filtC5 : roseJunctionRefute_pK.boundary.cycle.filter
    (roseJunctionRefute_keptTab 5) = roseJunctionRefute_F5 := by
  decide

/-- The dart `4` meets no other moved dart of the class `2`. -/
theorem roseJunctionRefute_isoC2 : ∀ y ∈ roseJunctionRefute_F2, y ≠ 4 →
    roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha 4) ≠
      roseJunctionRefute_vClass y ∧
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha y) ≠
        roseJunctionRefute_vClass 4 := by
  decide

/-- The dart `10` meets no other moved dart of the class `4`. -/
theorem roseJunctionRefute_isoC4 : ∀ y ∈ roseJunctionRefute_F4, y ≠ 10 →
    roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha 10) ≠
      roseJunctionRefute_vClass y ∧
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha y) ≠
        roseJunctionRefute_vClass 10 := by
  decide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
