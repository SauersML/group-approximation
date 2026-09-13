import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The edges with one face on both sides of a planar map form a forest

Osin (math/0411039v3, §9), proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`".  The cutting paths of a
component polygon run along edges with the polygon's own face on both sides.  In a planar map these
edges form a forest, so once there is one of them there are fewer of them than vertices they meet.
This is the one planarity input of the count of cutting sides (`OsinLemma94CuttingSidesStatement`).

* `CombMap.sameFaceDarts`, `CombMap.sameFaceVertices`: the darts with the face `f` on both sides,
  and the vertices they start at.
* `SameFaceDartForestStatement`: in a planar map, once there is such a dart,
  `#darts + 2 ≤ 2 · #vertices`.
* `SameFaceForest.exists_isSimpleClosedWalk`: a successor that never turns back gives a simple
  closed walk.
* `SameFaceForest.exists_leaf`: a nonempty reversal-closed set of same-face darts has a dart that is
  alone at its vertex, since `simpleClosedWalkSides` separates the two sides of a simple closed walk.
* `SameFaceForest.card_add_two_le`, `sameFaceDartForest`: the count, by removing leaves.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, "Hull's small cancellation theorem",
through Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace CombMap

/-- The darts with the face `f` on both sides. -/
noncomputable def sameFaceDarts (M : CombMap.{u}) (f : M.Face) : Finset M.Dart := by
  classical
  exact Finset.univ.filter fun d => M.faceOf d = f ∧ M.faceOf (M.alpha d) = f

theorem mem_sameFaceDarts (M : CombMap.{u}) (f : M.Face) (d : M.Dart) :
    d ∈ M.sameFaceDarts f ↔ M.faceOf d = f ∧ M.faceOf (M.alpha d) = f := by
  classical
  unfold sameFaceDarts
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ d, h⟩⟩

/-- The vertices at which the darts with the face `f` on both sides start. -/
noncomputable def sameFaceVertices (M : CombMap.{u}) (f : M.Face) : Finset M.Vertex := by
  classical
  exact (M.sameFaceDarts f).image M.vertexOf

end CombMap

/-- **The edges with one face on both sides form a forest.**  In a planar map, the darts with
the face `f` on both sides are the darts of the edges with `f` on both sides.  These edges contain
no cycle, so, once there is one of them, there are fewer of them than vertices they meet:
`#darts + 2 ≤ 2 · #vertices`. -/
def SameFaceDartForestStatement : Prop :=
  ∀ (M : CombMap.{u}), M.IsPlanar → ∀ f : M.Face, (M.sameFaceDarts f).Nonempty →
    (M.sameFaceDarts f).card + 2 ≤ 2 * (M.sameFaceVertices f).card

/-! ## The proof -/

namespace SameFaceForest

variable {M : CombMap.{u}}

/-- The darts with the face `f` on both sides are closed under reversal. -/
theorem alpha_mem_sameFaceDarts {f : M.Face} {d : M.Dart} (hd : d ∈ M.sameFaceDarts f) :
    M.alpha d ∈ M.sameFaceDarts f := by
  rw [CombMap.mem_sameFaceDarts] at hd ⊢
  exact ⟨hd.2, by rw [M.alpha_involutive d]; exact hd.1⟩

/-- **A successor that never turns back gives a simple closed walk.**  Let `next` keep a finite
set `T` of darts, start `next d` where `d` ends, and never be the reversal of `d`.  Iterating from a
dart of `T` repeats a vertex.  Between the first repeat and its earlier occurrence the darts form a
simple closed walk inside `T`. -/
theorem exists_isSimpleClosedWalk (T : Finset M.Dart) (next : M.Dart → M.Dart)
    (hmem : ∀ d ∈ T, next d ∈ T)
    (hvertex : ∀ d ∈ T, M.vertexOf (next d) = M.vertexOf (M.alpha d))
    (hback : ∀ d ∈ T, next d ≠ M.alpha d) {d₀ : M.Dart} (hd₀ : d₀ ∈ T) :
    ∃ w : List M.Dart, IsSimpleClosedWalk M w ∧ ∀ d ∈ w, d ∈ T := by
  classical
  have hs : ∀ n, next^[n] d₀ ∈ T := by
    intro n
    induction n with
    | zero => exact hd₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hmem _ ih
  have hsucc : ∀ n, M.vertexOf (next^[n + 1] d₀) = M.vertexOf (M.alpha (next^[n] d₀)) := by
    intro n
    rw [Function.iterate_succ_apply']
    exact hvertex _ (hs n)
  have hnotback : ∀ n, next^[n + 1] d₀ ≠ M.alpha (next^[n] d₀) := by
    intro n
    rw [Function.iterate_succ_apply']
    exact hback _ (hs n)
  have hrep : ∃ j, ∃ i < j, M.vertexOf (next^[i] d₀) = M.vertexOf (next^[j] d₀) := by
    obtain ⟨x, y, hxy, hv⟩ :=
      Finite.exists_ne_map_eq_of_infinite fun n : ℕ => M.vertexOf (next^[n] d₀)
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, hv⟩
    · exact ⟨x, y, h, hv.symm⟩
  have hspec := Nat.find_spec hrep
  have hmin : ∀ {a b : ℕ}, a < b → b < Nat.find hrep →
      M.vertexOf (next^[a] d₀) ≠ M.vertexOf (next^[b] d₀) := by
    intro a b hab hb hv
    exact Nat.find_min (H := hrep) hb ⟨a, hab, hv⟩
  obtain ⟨j, hjeq⟩ : ∃ j, Nat.find hrep = j := ⟨_, rfl⟩
  rw [hjeq] at hspec hmin
  obtain ⟨i, hij, hu⟩ := hspec
  refine ⟨(List.range (j - i)).map fun k => next^[i + k] d₀, ?_, ?_⟩
  swap
  · intro d hd
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hd
    exact hs _
  have hne : (List.range (j - i)).map (fun k => next^[i + k] d₀) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_range, List.length_nil] at hlen
    omega
  refine
    { ne_nil := hne
      chain := ?_
      closes := ?_
      vertex_nodup := ?_
      alpha_not_mem := ?_ }
  · rw [List.isChain_map, List.isChain_range]
    intro m _
    exact (hsucc (i + m)).symm
  · simp only [List.getLast_map, List.head_map, List.getLast_range, List.head_range,
      Nat.add_zero]
    have h := hsucc (i + (j - i - 1))
    rw [show i + (j - i - 1) + 1 = j by omega] at h
    rw [← h]
    exact hu.symm
  · rw [List.map_map]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    by_contra hxne
    rcases Nat.lt_or_gt_of_ne hxne with h | h
    · exact hmin (a := i + x) (b := i + y) (by omega) (by omega) hxy
    · exact hmin (a := i + y) (b := i + x) (by omega) (by omega) hxy.symm
  · intro d hd hα
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hα
    rw [List.mem_range] at ha hb
    have hab' : next^[i + b] d₀ = M.alpha (next^[i + a] d₀) := hab
    have hvb : M.vertexOf (next^[i + b] d₀) = M.vertexOf (next^[i + a + 1] d₀) := by
      rw [hab', hsucc]
    by_cases hlast : a + 1 < j - i
    · have hb' : b = a + 1 := by
        by_contra hbne
        rcases Nat.lt_or_gt_of_ne hbne with h | h
        · exact hmin (a := i + b) (b := i + a + 1) (by omega) (by omega) hvb
        · exact hmin (a := i + a + 1) (b := i + b) (by omega) (by omega) hvb.symm
      subst hb'
      exact hnotback (i + a) hab'
    · have ha' : i + a + 1 = j := by omega
      rw [ha', ← hu] at hvb
      have hb0 : b = 0 := by
        by_contra hbne
        exact hmin (a := i) (b := i + b) (by omega) (by omega) hvb.symm
      subst hb0
      have hab0 : next^[i] d₀ = M.alpha (next^[i + a] d₀) := hab'
      have hα' : M.alpha (next^[i] d₀) = next^[i + a] d₀ := by
        rw [hab0, M.alpha_involutive]
      rcases Nat.eq_zero_or_pos a with ha0 | ha0
      · subst ha0
        exact M.alpha_fixedPointFree _ hα'
      · have hv1 : M.vertexOf (next^[i + 1] d₀) = M.vertexOf (next^[i + a] d₀) := by
          rw [hsucc, hα']
        rcases Nat.lt_or_ge 1 a with h1 | h1
        · exact hmin (a := i + 1) (b := i + a) (by omega) (by omega) hv1
        · obtain rfl : a = 1 := by omega
          exact hnotback i hα'.symm

/-- **A nonempty reversal-closed set of same-face darts has a leaf.**  Some dart of `T` is the only
dart of `T` at its vertex.  Otherwise every dart has a successor in `T` at its end other than its
reversal, which gives a simple closed walk inside `T`.  Both sides of the walk lie on the face `f`,
contradicting the separation of a planar map by a simple closed walk. -/
theorem exists_leaf (hM : M.IsPlanar) {f : M.Face} (T : Finset M.Dart)
    (hT : ∀ d ∈ T, d ∈ M.sameFaceDarts f) (halpha : ∀ d ∈ T, M.alpha d ∈ T)
    (hne : T.Nonempty) : ∃ d ∈ T, ∀ e ∈ T, M.vertexOf e = M.vertexOf d → e = d := by
  classical
  by_contra hleaf
  have hbranch : ∀ d ∈ T, ∃ e ∈ T, M.vertexOf e = M.vertexOf d ∧ e ≠ d := by
    intro d hd
    by_contra h
    exact hleaf ⟨d, hd, fun e he hv => by
      by_contra hed
      exact h ⟨e, he, hv, hed⟩⟩
  have hbranch' : ∀ d : M.Dart, ∃ e : M.Dart, d ∈ T →
      e ∈ T ∧ M.vertexOf e = M.vertexOf (M.alpha d) ∧ e ≠ M.alpha d := by
    intro d
    by_cases hd : d ∈ T
    · obtain ⟨e, he, hv, hed⟩ := hbranch (M.alpha d) (halpha d hd)
      exact ⟨e, fun _ => ⟨he, hv, hed⟩⟩
    · exact ⟨d, fun h => absurd h hd⟩
  choose next hnext using hbranch'
  obtain ⟨d₀, hd₀⟩ := hne
  obtain ⟨w, hw, hwT⟩ := exists_isSimpleClosedWalk T next (fun d hd => (hnext d hd).1)
    (fun d hd => (hnext d hd).2.1) (fun d hd => (hnext d hd).2.2) hd₀
  have hd := List.head_mem hw.ne_nil
  have hface := (CombMap.mem_sameFaceDarts M f _).mp (hT _ (hwT _ hd))
  have hsc : M.facePerm.SameCycle (w.head hw.ne_nil) (M.alpha (w.head hw.ne_nil)) :=
    (M.faceOf_eq_iff _ _).mp (hface.1.trans hface.2.symm)
  exact hw.not_faceClass_alpha hM hd hd
    (SimpleClosedWalkSides.eqvGen_faceClass_of_sameCycle M _ hsc)

/-- **The count, by removing leaves.**  For a nonempty reversal-closed set `T` of darts with the
face `f` on both sides, `#T + 2 ≤ 2 · #(vertices of T)`.  Removing a leaf dart and its reversal
removes two darts and at least the leaf's vertex. -/
theorem card_add_two_le [DecidableEq M.Vertex] (hM : M.IsPlanar) (f : M.Face) :
    ∀ (n : ℕ) (T : Finset M.Dart), T.card = n → (∀ d ∈ T, d ∈ M.sameFaceDarts f) →
      (∀ d ∈ T, M.alpha d ∈ T) → T.Nonempty →
        T.card + 2 ≤ 2 * (T.image M.vertexOf).card := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hcard hT halpha hne
    obtain ⟨d, hd, hleaf⟩ := exists_leaf hM T hT halpha hne
    have hαd : M.alpha d ∈ T := halpha d hd
    have hαne : M.alpha d ≠ d := M.alpha_fixedPointFree d
    have hvne : M.vertexOf (M.alpha d) ≠ M.vertexOf d := fun hv => hαne (hleaf _ hαd hv)
    set T' := (T.erase d).erase (M.alpha d) with hT'
    have hαmem : M.alpha d ∈ T.erase d := Finset.mem_erase.mpr ⟨hαne, hαd⟩
    have hpairT : ({d, M.alpha d} : Finset M.Dart) ⊆ T :=
      Finset.insert_subset_iff.mpr ⟨hd, Finset.singleton_subset_iff.mpr hαd⟩
    have htwo : 2 ≤ T.card := by
      have h := Finset.card_le_card hpairT
      rw [Finset.card_pair_eq_two_iff.mpr hαne.symm] at h
      exact h
    have hcard' : T'.card + 2 = T.card := by
      rw [hT', Finset.card_erase_of_mem hαmem, Finset.card_erase_of_mem hd]
      omega
    have hT'sub : ∀ e ∈ T', e ∈ T ∧ e ≠ d ∧ e ≠ M.alpha d := by
      intro e he
      rw [hT', Finset.mem_erase, Finset.mem_erase] at he
      exact ⟨he.2.2, he.2.1, he.1⟩
    have hvnot : M.vertexOf d ∉ T'.image M.vertexOf := by
      intro hv
      obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
      obtain ⟨heT, hed, -⟩ := hT'sub e he
      exact hed (hleaf e heT hev)
    have himage : (T'.image M.vertexOf).card + 1 ≤ (T.image M.vertexOf).card := by
      rw [← Finset.card_insert_of_notMem hvnot]
      refine Finset.card_le_card (Finset.insert_subset_iff.mpr
        ⟨Finset.mem_image_of_mem _ hd, ?_⟩)
      intro v hv
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image_of_mem _ (hT'sub e he).1
    by_cases hne' : T'.Nonempty
    · have hlt : T'.card < n := by omega
      have hαT' : ∀ e ∈ T', M.alpha e ∈ T' := by
        intro e he
        obtain ⟨heT, hed, heα⟩ := hT'sub e he
        rw [hT', Finset.mem_erase, Finset.mem_erase]
        refine ⟨fun h' => hed ?_, fun h' => heα ?_, halpha e heT⟩
        · have h'' := congrArg M.alpha h'
          rwa [M.alpha_involutive, M.alpha_involutive] at h''
        · have h'' := congrArg M.alpha h'
          rwa [M.alpha_involutive] at h''
      have h := ih T'.card hlt T' rfl (fun e he => hT _ (hT'sub e he).1) hαT' hne'
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne'
      have hTc : T.card = 2 := by
        rw [← hcard', hne', Finset.card_empty]
      have hpair : ({M.vertexOf d, M.vertexOf (M.alpha d)} : Finset M.Vertex) ⊆
          T.image M.vertexOf :=
        Finset.insert_subset_iff.mpr ⟨Finset.mem_image_of_mem _ hd,
          Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hαd)⟩
      have h2 := Finset.card_le_card hpair
      rw [Finset.card_pair_eq_two_iff.mpr hvne.symm] at h2
      omega

end SameFaceForest

/-- **The edges with one face on both sides of a planar map form a forest.**  Once there is a dart
with the face `f` on both sides, `#darts + 2 ≤ 2 · #vertices`. -/
theorem sameFaceDartForest : SameFaceDartForestStatement.{u} := by
  intro M hM f hne
  classical
  have h := SameFaceForest.card_add_two_le hM f _ _ rfl (fun _ hd => hd)
    (fun _ hd => SameFaceForest.alpha_mem_sameFaceDarts hd) hne
  unfold CombMap.sameFaceVertices
  convert h

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.mem_sameFaceDarts
#audit_axioms GroupApproximation.GGT.VanKampen.SameFaceForest.alpha_mem_sameFaceDarts
#audit_axioms GroupApproximation.GGT.VanKampen.SameFaceForest.exists_isSimpleClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.SameFaceForest.exists_leaf
#audit_axioms GroupApproximation.GGT.VanKampen.SameFaceForest.card_add_two_le
#audit_closed_axioms GroupApproximation.GGT.VanKampen.sameFaceDartForest
