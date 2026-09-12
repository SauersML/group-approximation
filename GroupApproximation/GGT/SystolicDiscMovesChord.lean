import GroupApproximation.GGT.SystolicDiscMovesAdapter
import GroupApproximation.GGT.VanKampen.EdgeInsertionFaceCycles
import GroupApproximation.GGT.VanKampen.CombMapEdgePlanarity
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Inserting a chord and attaching a triangle (HC3(a), HC3(b))

Let `du dv` be consecutive exterior darts of a cycle disc, reading `u v`, followed by a dart
at `w`, with `X.Tri u v w`.  Inserting an edge from the corner before `du` to the corner
before the dart at `w` (`EdgeInsertion`) cuts the triangle `u v w` off the exterior face:
the new face `[du, dv, new]` is a triangle of `X`, and the exterior walk reads `u w` where it
read `u v w` (`CycleDisc.insertChord`).  This proves `insertChordStatement`.

Attaching a triangle along a boundary edge `u w` is a pendant edge `u v` followed by the
chord across `v u w` (`attachTriangleStatement`).
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

namespace TriangleComplex

theorem tri_rotate {X : TriangleComplex V} {x y z : V} (h : X.Tri x y z) : X.Tri y z x :=
  X.tri_swap23 (X.tri_swap12 h)

end TriangleComplex

namespace CycleDisc

section Chord

variable (D : CycleDisc X) (a b : D.map.Dart)

/-- Labels after inserting an edge between the corners before `a` and before `b`. -/
def chordLab : EdgeInsertion.Dart D.map → V
  | none => D.lab b
  | some none => D.lab a
  | some (some d) => D.lab d

variable {D a b}

theorem chordLab_sigma (hab : a ≠ b) (x : EdgeInsertion.Dart D.map) :
    chordLab D a b ((EdgeInsertion.toCombMap D.map a b).sigma x) = chordLab D a b x := by
  classical
  have hsa : some a ≠ some b := fun h => hab (Option.some.inj h)
  rcases x with _ | (_ | d)
  · show chordLab D a b (PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore D.map.sigma a)
      (some b) none) = D.lab b
    rw [PermOrbitInsert.insertBefore_none]
    rfl
  · show chordLab D a b (PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore D.map.sigma a)
      (some b) (some none)) = D.lab a
    rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_none, if_neg hsa]
    rfl
  · show chordLab D a b (PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore D.map.sigma a)
      (some b) (some (some d))) = D.lab d
    rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_some]
    by_cases h1 : D.map.sigma d = a
    · rw [if_pos h1, if_neg (fun h : (none : Option D.map.Dart) = some b => by cases h)]
      show D.lab a = D.lab d
      rw [← h1, D.lab_sigma]
    · rw [if_neg h1]
      by_cases h2 : D.map.sigma d = b
      · rw [if_pos (congrArg some h2)]
        show D.lab b = D.lab d
        rw [← h2, D.lab_sigma]
      · rw [if_neg (fun h => h2 (Option.some.inj h))]
        exact D.lab_sigma d

theorem chordLab_adj (hadj : X.G.Adj (D.lab a) (D.lab b)) (x : EdgeInsertion.Dart D.map) :
    X.G.Adj (chordLab D a b x) (chordLab D a b ((EdgeInsertion.toCombMap D.map a b).alpha x)) := by
  rcases x with _ | (_ | d)
  · exact hadj.symm
  · exact hadj
  · exact D.adj d

/-- **Inserting a chord across two consecutive exterior darts.** -/
theorem insertChord {s t : List D.map.Dart} {du dv : D.map.Dart}
    (hcyc : D.cyc = s ++ du :: dv :: t)
    (htri : X.Tri (D.lab du) (D.lab dv) (D.lab (D.map.facePerm dv))) :
    ∃ D' : CycleDisc X,
      D'.boundary = s.map D.lab ++ D.lab du :: (t.map D.lab ++
        [D.lab (D.cyc.head D.isFaceCycle.ne_nil)]) := by
  classical
  have hR : D.map.IsFaceCycle (du :: dv :: (t ++ s)) := by
    have h := D.isFaceCycle.rotate s.length
    rw [hcyc, List.rotate_append_length_eq] at h
    exact h
  have hnextu : D.map.facePerm du = dv := (List.isChain_cons_cons.mp hR.chain).1
  have hne_uw : D.lab du ≠ D.lab (D.map.facePerm dv) := (X.tri_adj htri).2.2.ne
  have hts : t ++ s ≠ [] := by
    intro h
    rw [h] at hR
    have hc : D.map.facePerm dv = du := hR.closes
    exact hne_uw (by rw [hc])
  obtain ⟨b, ys, hbys⟩ := List.exists_cons_of_ne_nil hts
  rw [hbys] at hR
  have hnextv : D.map.facePerm dv = b :=
    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hR.chain).2).1
  have hab : du ≠ b := fun h => hne_uw (by rw [hnextv, h])
  have hsplit : EdgeInsertion.SplitCycle D.map du b [dv] ys :=
    ⟨hR.nodup, hR.chain, by
      have hc := hR.closes
      rwa [List.getLast_cons_cons, List.getLast_cons_cons] at hc⟩
  have hnd := hR.nodup
  have hdv_b : dv ≠ b := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (h ▸ List.mem_cons_self)
  have hdv_du : dv ≠ du := by
    intro h
    exact (List.nodup_cons.mp hnd).1 (h ▸ List.mem_cons_self)
  let N := EdgeInsertion.toCombMap D.map du b
  have hstep_u : N.facePerm (EdgeInsertion.embed D.map du) = EdgeInsertion.embed D.map dv := by
    rw [EdgeInsertion.facePerm_embed hab, hnextu, if_neg hdv_du, if_neg hdv_b]
  have hstep_v : N.facePerm (EdgeInsertion.embed D.map dv) = none := by
    rw [EdgeInsertion.facePerm_embed hab, hnextv, if_neg (Ne.symm hab), if_pos rfl]
  have hstep_n : N.facePerm none = EdgeInsertion.embed D.map du := EdgeInsertion.facePerm_none hab
  let P : List (EdgeInsertion.Dart D.map) := (b :: ys).map (EdgeInsertion.embed D.map) ++ [some none]
  have hP : N.IsFaceCycle P :=
    ⟨by simp [P], EdgeInsertion.nodup_right hsplit, EdgeInsertion.isChain_right hab hsplit,
      EdgeInsertion.closes_right hab⟩
  let L : List (EdgeInsertion.Dart D.map) := P.rotate t.length
  have hL : L = s.map (EdgeInsertion.embed D.map) ++ some none :: t.map (EdgeInsertion.embed D.map) := by
    show P.rotate t.length = _
    have hP' : P = t.map (EdgeInsertion.embed D.map) ++ (s.map (EdgeInsertion.embed D.map) ++ [some none]) := by
      show (b :: ys).map (EdgeInsertion.embed D.map) ++ [some none] = _
      rw [← hbys, List.map_append, List.append_assoc]
    have hlen : (t.map (EdgeInsertion.embed D.map)).length = t.length := List.length_map _
    rw [hP', ← hlen, List.rotate_append_length_eq, List.append_assoc]
    rfl
  have hLcyc : N.IsFaceCycle L := hP.rotate t.length
  have hdu : du ∈ D.cyc := by rw [hcyc]; simp
  have hbmem : b ∈ D.cyc := by
    have hbts : b ∈ t ++ s := by rw [hbys]; exact List.mem_cons_self
    rw [hcyc]
    rcases List.mem_append.mp hbts with h | h
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    · exact List.mem_append.mpr (Or.inl h)
  have hinner : ∀ y, y ∉ D.cyc → N.facePerm (EdgeInsertion.embed D.map y) =
      EdgeInsertion.embed D.map (D.map.facePerm y) := by
    intro y hy
    have hfy := D.facePerm_not_mem hy
    have h1 : D.map.facePerm y ≠ du := fun h => hfy (by rw [h]; exact hdu)
    have h2 : D.map.facePerm y ≠ b := fun h => hfy (by rw [h]; exact hbmem)
    rw [EdgeInsertion.facePerm_embed hab, if_neg h1, if_neg h2]
  have hinner_pow : ∀ y, y ∉ D.cyc → ∀ k : ℕ, (N.facePerm ^ k) (EdgeInsertion.embed D.map y) =
      EdgeInsertion.embed D.map ((D.map.facePerm ^ k) y) := by
    intro y hy k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hk : (D.map.facePerm ^ k) y ∉ D.cyc := by
          clear ih
          induction k with
          | zero => exact hy
          | succ k ihk =>
              rw [pow_succ', Equiv.Perm.mul_apply]
              exact D.facePerm_not_mem ihk
        rw [pow_succ', Equiv.Perm.mul_apply, ih, hinner _ hk, pow_succ', Equiv.Perm.mul_apply]
  refine ⟨{ map := N
            planar := EdgeInsertion.planar D.map du b D.planar
              (((D.isFaceCycle.mem_iff du).mp hdu).trans ((D.isFaceCycle.mem_iff b).mp hbmem).symm)
            lab := chordLab D du b
            lab_sigma := chordLab_sigma hab
            adj := chordLab_adj (by rw [← hnextv]; exact (X.tri_adj htri).2.2)
            cyc := L
            isFaceCycle := hLcyc
            tri := ?_ }, ?_⟩
  · intro x hx
    have htri_u : (N.facePerm ^ 3) (EdgeInsertion.embed D.map du) = EdgeInsertion.embed D.map du := by
      rw [perm_pow_three_apply, hstep_u, hstep_v, hstep_n]
    have hlab_u : chordLab D du b (EdgeInsertion.embed D.map du) = D.lab du := rfl
    have hlab_v : chordLab D du b (EdgeInsertion.embed D.map dv) = D.lab dv := rfl
    have hlab_n : chordLab D du b none = D.lab (D.map.facePerm dv) := by rw [hnextv]; rfl
    rcases x with _ | (_ | y)
    · refine ⟨by rw [perm_pow_three_apply, hstep_n, hstep_u, hstep_v], ?_⟩
      rw [perm_pow_two_apply, hstep_n, hstep_u, hlab_n, hlab_u, hlab_v]
      exact TriangleComplex.tri_rotate (TriangleComplex.tri_rotate htri)
    · have hmem : (some none : EdgeInsertion.Dart D.map) ∈ L := by
        rw [hL]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      exact absurd hmem hx
    · by_cases hyu : y = du
      · rw [hyu]
        show (N.facePerm ^ 3) (EdgeInsertion.embed D.map du) = EdgeInsertion.embed D.map du ∧
          X.Tri (chordLab D du b (EdgeInsertion.embed D.map du))
            (chordLab D du b (N.facePerm (EdgeInsertion.embed D.map du)))
            (chordLab D du b ((N.facePerm ^ 2) (EdgeInsertion.embed D.map du)))
        refine ⟨htri_u, ?_⟩
        rw [perm_pow_two_apply, hstep_u, hstep_v, hlab_u, hlab_v, hlab_n]
        exact htri
      · by_cases hyv : y = dv
        · rw [hyv]
          show (N.facePerm ^ 3) (EdgeInsertion.embed D.map dv) = EdgeInsertion.embed D.map dv ∧
            X.Tri (chordLab D du b (EdgeInsertion.embed D.map dv))
              (chordLab D du b (N.facePerm (EdgeInsertion.embed D.map dv)))
              (chordLab D du b ((N.facePerm ^ 2) (EdgeInsertion.embed D.map dv)))
          refine ⟨by rw [perm_pow_three_apply, hstep_v, hstep_n, hstep_u], ?_⟩
          rw [perm_pow_two_apply, hstep_v, hstep_n, hlab_v, hlab_n, hlab_u]
          exact TriangleComplex.tri_rotate htri
        · have hy : y ∉ D.cyc := by
            intro hm
            apply hx
            rw [hL]
            rw [hcyc] at hm
            rcases List.mem_append.mp hm with h | h
            · exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem h))
            · rcases List.mem_cons.mp h with h' | h'
              · exact absurd h' hyu
              · rcases List.mem_cons.mp h' with h'' | h''
                · exact absurd h'' hyv
                · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
                    (List.mem_map_of_mem h'')))
          obtain ⟨h3, htri_y⟩ := D.tri y hy
          show (N.facePerm ^ 3) (EdgeInsertion.embed D.map y) = EdgeInsertion.embed D.map y ∧
            X.Tri (chordLab D du b (EdgeInsertion.embed D.map y))
              (chordLab D du b (N.facePerm (EdgeInsertion.embed D.map y)))
              (chordLab D du b ((N.facePerm ^ 2) (EdgeInsertion.embed D.map y)))
          refine ⟨by rw [hinner_pow y hy, h3], ?_⟩
          rw [hinner_pow y hy 2, hinner y hy]
          exact htri_y
  · show L.map (chordLab D du b) ++ [chordLab D du b (L.head hLcyc.ne_nil)] = _
    have hmap : L.map (chordLab D du b) = s.map D.lab ++ D.lab du :: t.map D.lab := by
      rw [hL, List.map_append, List.map_cons, List.map_map, List.map_map]
      rfl
    have hhead : chordLab D du b (L.head hLcyc.ne_nil) = D.lab (D.cyc.head D.isFaceCycle.ne_nil) := by
      have h1 := List.head?_eq_some_head hLcyc.ne_nil
      have h2 := List.head?_eq_some_head D.isFaceCycle.ne_nil
      rcases s with _ | ⟨c, s'⟩
      · have hL0 : L.head? = some (some none) := by rw [hL]; rfl
        have hc0 : D.cyc.head? = some du := by rw [hcyc]; rfl
        rw [Option.some.inj (h1.symm.trans hL0), Option.some.inj (h2.symm.trans hc0)]
        rfl
      · have hL0 : L.head? = some (EdgeInsertion.embed D.map c) := by rw [hL]; rfl
        have hc0 : D.cyc.head? = some c := by rw [hcyc]; rfl
        rw [Option.some.inj (h1.symm.trans hL0), Option.some.inj (h2.symm.trans hc0)]
        rfl
    rw [hmap, hhead]
    simp only [List.append_assoc, List.cons_append]

end Chord

end CycleDisc

/-- **HC3(b): cutting off a triangle along two consecutive boundary edges.** -/
theorem insertChordStatement : InsertChordStatement X := by
  intro p q u v w htri T
  obtain ⟨D, hD⟩ := CycleDisc.exists_of_triangulatedDisc T
  have h : D.cyc.map D.lab ++ [D.lab (D.cyc.head D.isFaceCycle.ne_nil)] = p ++ u :: v :: w :: q := hD
  rcases split_boundary D.lab _ u p (v :: w :: q) D.cyc h with
    ⟨s, b, t₀, hcyc, rfl, rfl, ht₀⟩ | ⟨_, _, hq⟩
  · rcases t₀ with _ | ⟨dv, t⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq] at ht₀
      exact absurd ht₀.2 (by simp)
    · simp only [List.map_cons, List.cons_append, List.cons.injEq] at ht₀
      obtain ⟨rfl, hwq⟩ := ht₀
      have hw : D.lab (D.map.facePerm dv) = w := by
        have hR : D.map.IsFaceCycle (b :: dv :: (t ++ s)) := by
          have hr := D.isFaceCycle.rotate s.length
          rw [hcyc, List.rotate_append_length_eq] at hr
          exact hr
        rcases t with _ | ⟨c, t'⟩
        · simp only [List.map_nil, List.nil_append, List.cons.injEq] at hwq
          rcases s with _ | ⟨c', s'⟩
          · have hc : D.map.facePerm dv = b := hR.closes
            rw [hc, hwq.1]
            congr 1
            have h2 := List.head?_eq_some_head D.isFaceCycle.ne_nil
            have hc0 : D.cyc.head? = some b := by rw [hcyc]; rfl
            exact (Option.some.inj (h2.symm.trans hc0)).symm
          · have hc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hR.chain).2).1
            rw [hc, hwq.1]
            congr 1
            have h2 := List.head?_eq_some_head D.isFaceCycle.ne_nil
            have hc0 : D.cyc.head? = some c' := by rw [hcyc]; rfl
            exact (Option.some.inj (h2.symm.trans hc0)).symm
        · simp only [List.map_cons, List.cons_append, List.cons.injEq] at hwq
          have hc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hR.chain).2).1
          rw [hc]
          exact hwq.1.symm
      rw [← hw] at htri
      obtain ⟨D', hD'⟩ := CycleDisc.insertChord hcyc htri
      refine ⟨?_⟩
      have hgoal : s.map D.lab ++ D.lab b :: (t.map D.lab ++ [D.lab (D.cyc.head D.isFaceCycle.ne_nil)]) =
          s.map D.lab ++ D.lab b :: w :: q := by rw [hwq]
      exact (hD'.trans hgoal) ▸ D'.toTriangulatedDisc
  · exact absurd hq (by simp)

/-- **HC3(a): gluing a triangle along a boundary edge.** -/
theorem attachTriangleStatement : AttachTriangleStatement X := by
  intro p q u v w htri T
  obtain ⟨T₁⟩ := attachPendantStatement p (w :: q) u v (X.tri_adj htri).1 T
  have h₁ : p ++ u :: v :: u :: w :: q = (p ++ [u]) ++ v :: u :: w :: q := by simp
  obtain ⟨T₂⟩ := insertChordStatement (p ++ [u]) q v u w (X.tri_swap12 htri) (h₁ ▸ T₁)
  have h₂ : (p ++ [u]) ++ v :: w :: q = p ++ u :: v :: w :: q := by simp
  exact ⟨h₂ ▸ T₂⟩

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.CycleDisc.chordLab_sigma
#audit_axioms GroupApproximation.Systolic.CycleDisc.insertChord
#audit_axioms GroupApproximation.Systolic.insertChordStatement
#audit_axioms GroupApproximation.Systolic.attachTriangleStatement
