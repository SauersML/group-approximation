import GroupApproximation.GGT.VanKampen.CombMapEdgeFaces
import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Face cycles after inserting an edge across a face

Let `a` and `b` be distinct darts on one face, enumerated as `a :: xs ++ b :: ys`.
Inserting an edge at the corners before `a` and `b` (`EdgeInsertion.toCombMap M a b`)
splits that face into two faces, enumerated by

* `(a :: xs).map embed ++ [none]` (`isChain_left`, `closes_left`, `nodup_left`), and
* `(b :: ys).map embed ++ [some none]` (`isChain_right`, `closes_right`, `nodup_right`).

The step lemmas `facePerm_embed`, `facePerm_none`, `facePerm_some_none` read the face
rotation dart by dart.  In the literal van Kampen construction this closes a boundary
arc into a new relator face.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open Equiv PermOrbitInsert

universe u

variable {M : CombMap.{u}} [DecidableEq M.Dart] {a b : M.Dart}

/-- Face rotation after inserting an edge between distinct corners, dart by dart. -/
theorem facePerm_apply_of_ne (hab : a ≠ b) (x : Dart M) :
    (toCombMap M a b).facePerm x =
      insertBefore (insertBefore (Equiv.swap a b * M.facePerm) b) (some a) x :=
  congrArg (fun q : Perm (toCombMap M a b).Dart => q x) (facePerm_eq_of_ne M a b hab)

/-- **Old darts.**  The successor `a` is replaced by the new dart `some none`, the
successor `b` by the new dart `none`; every other successor is kept. -/
theorem facePerm_embed (hab : a ≠ b) (x : M.Dart) :
    (toCombMap M a b).facePerm (embed M x) =
      if M.facePerm x = a then some none
      else if M.facePerm x = b then none
      else embed M (M.facePerm x) := by
  rw [facePerm_apply_of_ne hab]
  by_cases ha : M.facePerm x = a
  · simp [embed, insertBefore_some, Perm.mul_apply, ha]
  · by_cases hb : M.facePerm x = b
    · simp [embed, insertBefore_some, Perm.mul_apply, hb, hab, hab.symm]
    · simp [embed, insertBefore_some, Perm.mul_apply, ha, hb,
        Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The new dart `none` is followed by `a`. -/
theorem facePerm_none (hab : a ≠ b) : (toCombMap M a b).facePerm none = embed M a := by
  rw [facePerm_apply_of_ne hab]
  simp [embed, insertBefore_none]

/-- The new dart `some none` is followed by `b`. -/
theorem facePerm_some_none (hab : a ≠ b) :
    (toCombMap M a b).facePerm (some none) = embed M b := by
  rw [facePerm_apply_of_ne hab]
  simp [embed, insertBefore_some, insertBefore_none, hab.symm]

/-- The old face through both corners, enumerated from `a`. -/
structure SplitCycle (M : CombMap.{u}) (a b : M.Dart) (xs ys : List M.Dart) : Prop where
  nodup : ((a :: xs) ++ (b :: ys)).Nodup
  chain : ((a :: xs) ++ (b :: ys)).IsChain fun d e => M.facePerm d = e
  closes : M.facePerm ((b :: ys).getLast (List.cons_ne_nil _ _)) = a

namespace SplitCycle

variable {xs ys : List M.Dart} (h : SplitCycle M a b xs ys)
include h

theorem nodup_left : (a :: xs).Nodup := (List.nodup_append.mp h.nodup).1

theorem nodup_right : (b :: ys).Nodup := (List.nodup_append.mp h.nodup).2.1

theorem b_not_mem_left : b ∉ a :: xs :=
  fun hb => (List.nodup_append.mp h.nodup).2.2 _ hb _ List.mem_cons_self rfl

theorem a_not_mem_right : a ∉ b :: ys :=
  fun ha => (List.nodup_append.mp h.nodup).2.2 _ List.mem_cons_self _ ha rfl

theorem chain_left : (a :: xs).IsChain fun d e => M.facePerm d = e :=
  (List.isChain_append.mp h.chain).1

theorem chain_right : (b :: ys).IsChain fun d e => M.facePerm d = e :=
  (List.isChain_append.mp h.chain).2.1

theorem last_left : M.facePerm ((a :: xs).getLast (List.cons_ne_nil _ _)) = b :=
  (List.isChain_append.mp h.chain).2.2 _
    (List.getLast?_eq_some_getLast (List.cons_ne_nil a xs)) _ rfl

end SplitCycle

variable {xs ys : List M.Dart}

/-- Successors inside one side are unchanged. -/
theorem isChain_side (hab : a ≠ b) {c c' : M.Dart} {zs : List M.Dart}
    (hchain : (c :: zs).IsChain fun d e => M.facePerm d = e) (hnd : (c :: zs).Nodup)
    (hc : c = a ∨ c = b) (hc' : c' = a ∨ c' = b) (hcc' : c ≠ c') (hnot : c' ∉ c :: zs) :
    ((c :: zs).map (embed M)).IsChain fun d e : Dart M => (toCombMap M a b).facePerm d = e := by
  rw [List.isChain_map]
  apply hchain.imp_of_mem_tail_imp
  intro y z _ hz hyz
  show (toCombMap M a b).facePerm (embed M y) = embed M z
  have hzc : z ≠ c := fun hzc => (List.nodup_cons.mp hnd).1 (hzc ▸ hz)
  have hzc' : z ≠ c' := fun hzc' => hnot (hzc' ▸ List.mem_cons_of_mem c hz)
  have hza : z ≠ a := by
    rcases hc with rfl | rfl
    · exact hzc
    · rcases hc' with rfl | rfl
      · exact hzc'
      · exact absurd rfl hcc'
  have hzb : z ≠ b := by
    rcases hc with rfl | rfl
    · rcases hc' with rfl | rfl
      · exact absurd rfl hcc'
      · exact hzc'
    · exact hzc
  rw [facePerm_embed hab, if_neg (fun h => hza (hyz ▸ h)), if_neg (fun h => hzb (hyz ▸ h)), hyz]

/-- **The first new face follows the face rotation.** -/
theorem isChain_left (hab : a ≠ b) (h : SplitCycle M a b xs ys) :
    ((a :: xs).map (embed M) ++ [none]).IsChain
      fun d e : Dart M => (toCombMap M a b).facePerm d = e := by
  rw [List.isChain_append]
  refine ⟨isChain_side hab h.chain_left h.nodup_left (Or.inl rfl) (Or.inr rfl) hab
    h.b_not_mem_left, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  rw [List.getLast?_map, List.getLast?_eq_some_getLast (List.cons_ne_nil a xs)] at hx
  simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hx
  subst hy
  rw [facePerm_embed hab, h.last_left, if_neg hab.symm, if_pos rfl]

/-- **The second new face follows the face rotation.** -/
theorem isChain_right (hab : a ≠ b) (h : SplitCycle M a b xs ys) :
    ((b :: ys).map (embed M) ++ [some none]).IsChain
      fun d e : Dart M => (toCombMap M a b).facePerm d = e := by
  rw [List.isChain_append]
  refine ⟨isChain_side hab h.chain_right h.nodup_right (Or.inr rfl) (Or.inl rfl) hab.symm
    h.a_not_mem_right, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  rw [List.getLast?_map, List.getLast?_eq_some_getLast (List.cons_ne_nil b ys)] at hx
  simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hx
  subst hy
  rw [facePerm_embed hab, h.closes, if_pos rfl]

theorem closes_left (hab : a ≠ b) :
    (toCombMap M a b).facePerm (((a :: xs).map (embed M) ++ [none]).getLast (by simp)) =
      ((a :: xs).map (embed M) ++ [none]).head (by simp) := by
  rw [List.getLast_append_singleton, facePerm_none hab]
  rfl

theorem closes_right (hab : a ≠ b) :
    (toCombMap M a b).facePerm (((b :: ys).map (embed M) ++ [some none]).getLast (by simp)) =
      ((b :: ys).map (embed M) ++ [some none]).head (by simp) := by
  rw [List.getLast_append_singleton, facePerm_some_none hab]
  rfl

theorem embed_injective_faceCycles : Function.Injective (embed M) :=
  fun _ _ h => Option.some.inj (Option.some.inj h)

theorem nodup_map_append (zs : List M.Dart) (hnd : zs.Nodup) (n : Dart M)
    (hn : ∀ z, embed M z ≠ n) : (zs.map (embed M) ++ [n]).Nodup := by
  refine List.nodup_append.mpr ⟨hnd.map embed_injective_faceCycles, List.nodup_singleton n, ?_⟩
  intro x hx y hy hxy
  rw [List.mem_singleton] at hy
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
  exact hn z (hxy.trans hy)

theorem nodup_left (h : SplitCycle M a b xs ys) :
    ((a :: xs).map (embed M) ++ [none]).Nodup :=
  nodup_map_append _ h.nodup_left none fun _ hz => by cases hz

theorem nodup_right (h : SplitCycle M a b xs ys) :
    ((b :: ys).map (embed M) ++ [some none]).Nodup :=
  nodup_map_append _ h.nodup_right (some none) fun _ hz => by cases hz

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_none
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_some_none
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.isChain_left
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.isChain_right
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.closes_left
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.closes_right
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.nodup_left
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.nodup_right
