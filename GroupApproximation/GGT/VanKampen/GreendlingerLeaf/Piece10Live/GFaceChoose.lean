import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFaceProveCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Loop face sets for the face-set flip statement: generic lemmas

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-52.

Route: a non-canonical choice of `F'` in `extremalGFaceProve_Clauses K F'`
(`Piece10Live/ExtremalGFaceProve`) is read off a simple closed walk `A` that is a consecutive
stretch `c = p ++ A ++ q` of the walk `c` of `K`.  This module holds the map-level facts; the
assembly is `Piece10Live/GFaceChooseLoop`.

* `gfaceChoose_sep_of_bd`: a face set whose boundary darts are on `c` separates no dart off `c`.
* `gfaceChoose_bd_keep`: the boundary darts of `sideFaces A` are the darts of `A`.
* `gfaceChoose_bd_exciseIn`: for `sideFaces A ⊆ F`, the boundary darts of `F \ sideFaces A`
  are the darts of `c` off `A`.
* `gfaceChoose_bd_exciseOut`: for `F ⊆ sideFaces A`, the boundary darts of
  `F ∪ sideOutside A` are the darts of `c` off `A`.
* `gfaceChoose_chain_cut`: cutting a closed stretch out of a walk leaves a walk.
* `gfaceChoose_filter_keep`, `gfaceChoose_filter_cut`: the two filters of `p ++ A ++ q`.

## Truth check

Scratchpad `gl-p10-52/` (`loop.py`, mode `wind`, on the Lean-faithful `gl-p10-49/gface.py`).
The lemmas here are map-level identities; the Python check concerns the assembled construction,
see `Piece10Live/GFaceChooseLoop`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose

universe v

open P10ExtremalWrap
open scoped Classical

variable {M : CombMap.{v}}

/-- **No separation off the walk**: if every boundary dart of `F` is on `c`, then `F` separates
no dart that is off `c` together with its inverse. -/
theorem gfaceChoose_sep_of_bd {c : List M.Dart} {F : Finset M.Face}
    (hB : ∀ d, M.faceOf d ∈ F → M.faceOf (M.alpha d) ∉ F → d ∈ c) (x : M.Dart)
    (hx : ¬ SimpleClosedWalkSides.walkKeep M c x) :
    (M.faceOf x ∈ F ↔ M.faceOf (M.alpha x) ∈ F) := by
  constructor
  · intro h
    by_contra h'
    exact hx (Or.inl (hB x h h'))
  · intro h
    by_contra h'
    refine hx (Or.inr (hB (M.alpha x) h ?_))
    rw [M.alpha_involutive x]
    exact h'

/-- **Keeping one side**: the boundary darts of the side faces of a simple closed walk in a
planar map are the darts of the walk. -/
theorem gfaceChoose_bd_keep {A : List M.Dart} (hw : IsSimpleClosedWalk M A)
    (hM : M.IsPlanar) (x : M.Dart) :
    extremalGFaceProve_bd M (SimpleClosedWalkSides.sideFaces M A) x = true ↔ x ∈ A :=
  (extremalGFaceProve_bd_eq_true_iff M _ x).trans (hw.isBoundaryDart_sideFaces_iff hM x)

/-- **Excising an inner side**: if `c` lists the boundary darts of `F`, `A` lists those of
`S ⊆ F`, and `A` is on `c`, then the boundary darts of `F \ S` are the darts of `c` off `A`. -/
theorem gfaceChoose_bd_exciseIn {c A : List M.Dart} {F S : Finset M.Face}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M S d ↔ d ∈ A) (hAc : ∀ d ∈ A, d ∈ c)
    (hSF : S ⊆ F) (x : M.Dart) :
    extremalGFaceProve_bd M (F \ S) x = true ↔ x ∈ c ∧ x ∉ A := by
  rw [extremalGFaceProve_bd_eq_true_iff, Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxF, hxS⟩, hax⟩
    have haF : M.faceOf (M.alpha x) ∉ F := by
      intro haF
      have haS : M.faceOf (M.alpha x) ∈ S := by
        by_contra h
        exact hax ⟨haF, h⟩
      have hxS' : M.faceOf (M.alpha (M.alpha x)) ∉ S := by
        rw [M.alpha_involutive x]
        exact hxS
      have hA : M.alpha x ∈ A := (hS _).mp ⟨haS, hxS'⟩
      have hb : M.faceOf (M.alpha (M.alpha x)) ∉ F := ((hc _).mp (hAc _ hA)).2
      rw [M.alpha_involutive x] at hb
      exact hb hxF
    exact ⟨(hc x).mpr ⟨hxF, haF⟩, fun hA => hxS ((hS x).mpr hA).1⟩
  · rintro ⟨hxc, hxA⟩
    obtain ⟨hxF, haF⟩ := (hc x).mp hxc
    have hxS : M.faceOf x ∉ S := by
      intro hxS
      have haS : M.faceOf (M.alpha x) ∈ S := by
        by_contra h
        exact hxA ((hS x).mp ⟨hxS, h⟩)
      exact haF (hSF haS)
    exact ⟨⟨hxF, hxS⟩, fun h => haF h.1⟩

/-- **Excising an outer side**: if `c` lists the boundary darts of `F`, `A` lists those of
`S ⊇ F`, `A` is on `c`, and `T` is the complement of `S`, then the boundary darts of `F ∪ T`
are the darts of `c` off `A`. -/
theorem gfaceChoose_bd_exciseOut {c A : List M.Dart} {F S T : Finset M.Face}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M S d ↔ d ∈ A) (hAc : ∀ d ∈ A, d ∈ c)
    (hFS : F ⊆ S) (hT : ∀ f, f ∈ T ↔ f ∉ S) (x : M.Dart) :
    extremalGFaceProve_bd M (F ∪ T) x = true ↔ x ∈ c ∧ x ∉ A := by
  rw [extremalGFaceProve_bd_eq_true_iff, Finset.mem_union, Finset.mem_union, hT, hT]
  constructor
  · rintro ⟨hx, hax⟩
    have haF : M.faceOf (M.alpha x) ∉ F := fun h => hax (Or.inl h)
    have haS : M.faceOf (M.alpha x) ∈ S := by
      by_contra h
      exact hax (Or.inr h)
    rcases hx with hxF | hxS
    · exact ⟨(hc x).mpr ⟨hxF, haF⟩, fun hA => ((hS x).mpr hA).2 haS⟩
    · exfalso
      have hxS' : M.faceOf (M.alpha (M.alpha x)) ∉ S := by
        rw [M.alpha_involutive x]
        exact hxS
      have hA : M.alpha x ∈ A := (hS _).mp ⟨haS, hxS'⟩
      exact haF ((hc _).mp (hAc _ hA)).1
  · rintro ⟨hxc, hxA⟩
    obtain ⟨hxF, haF⟩ := (hc x).mp hxc
    have haS : M.faceOf (M.alpha x) ∈ S := by
      by_contra h
      exact hxA ((hS x).mp ⟨hFS hxF, h⟩)
    exact ⟨Or.inl hxF, fun h => h.elim haF fun h' => h' haS⟩

/-- **Cutting a closed stretch out of a walk**: if `p ++ A ++ q` is a walk and `A` closes up,
then `p ++ q` is a walk. -/
theorem gfaceChoose_chain_cut {p A q : List M.Dart} (hA : A ≠ [])
    (hcl : M.vertexOf (M.alpha (A.getLast hA)) = M.vertexOf (A.head hA))
    (h : (p ++ A ++ q).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    (p ++ q).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
  have hpA := h.left_of_append
  refine hpA.left_of_append.append h.right_of_append fun x hx y hy => ?_
  have hp : p ≠ [] := by
    rintro rfl
    simp at hx
  have hq : q ≠ [] := by
    rintro rfl
    simp at hy
  rw [List.getLast?_eq_getLast hp, Option.mem_some_iff] at hx
  rw [List.head?_eq_head hq, Option.mem_some_iff] at hy
  subst hx hy
  have h1 : M.vertexOf (M.alpha (p.getLast hp)) = M.vertexOf (A.head hA) :=
    hpA.rel_getLast_head_of_append hp hA
  have h2 : M.vertexOf (M.alpha ((p ++ A).getLast (List.append_ne_nil_of_right_ne_nil p hA))) =
      M.vertexOf (q.head hq) :=
    h.rel_getLast_head_of_append (List.append_ne_nil_of_right_ne_nil p hA) hq
  rw [List.getLast_append_of_ne_nil _ hA] at h2
  exact h1.trans (hcl.symm.trans h2)

/-- **The filter keeping a stretch**: on a duplicate-free `p ++ A ++ q`, a test true exactly
on `A` keeps `A`. -/
theorem gfaceChoose_filter_keep {α : Type*} {p A q : List α} {b : α → Bool}
    (hnd : (p ++ A ++ q).Nodup) (hb : ∀ x, b x = true ↔ x ∈ A) :
    (p ++ A ++ q).filter b = A := by
  obtain ⟨hpA', -, hq⟩ := List.nodup_append.mp hnd
  obtain ⟨-, -, hpA⟩ := List.nodup_append.mp hpA'
  have h1 : p.filter b = [] := List.filter_eq_nil_iff.mpr fun x hx hbx =>
    hpA x hx x ((hb x).mp hbx) rfl
  have h2 : A.filter b = A := List.filter_eq_self.mpr fun x hx => (hb x).mpr hx
  have h3 : q.filter b = [] := List.filter_eq_nil_iff.mpr fun x hx hbx =>
    hq x (List.mem_append_right p ((hb x).mp hbx)) x hx rfl
  rw [List.filter_append, List.filter_append, h1, h2, h3, List.nil_append, List.append_nil]

/-- **The filter cutting a stretch**: on a duplicate-free `p ++ A ++ q`, a test true exactly
off `A` keeps `p ++ q`. -/
theorem gfaceChoose_filter_cut {α : Type*} {p A q : List α} {b : α → Bool}
    (hnd : (p ++ A ++ q).Nodup) (hb : ∀ x ∈ p ++ A ++ q, b x = true ↔ x ∉ A) :
    (p ++ A ++ q).filter b = p ++ q := by
  obtain ⟨hpA', -, hq⟩ := List.nodup_append.mp hnd
  obtain ⟨-, -, hpA⟩ := List.nodup_append.mp hpA'
  have h1 : p.filter b = p := List.filter_eq_self.mpr fun x hx =>
    (hb x (List.mem_append_left q (List.mem_append_left A hx))).mpr fun hA =>
      hpA x hx x hA rfl
  have h2 : A.filter b = [] := List.filter_eq_nil_iff.mpr fun x hx hbx =>
    (hb x (List.mem_append_left q (List.mem_append_right p hx))).mp hbx hx
  have h3 : q.filter b = q := List.filter_eq_self.mpr fun x hx =>
    (hb x (List.mem_append_right (p ++ A) hx)).mpr fun hA =>
      hq x (List.mem_append_right p hA) x hx rfl
  rw [List.filter_append, List.filter_append, h1, h2, h3, List.append_nil]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_sep_of_bd
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_bd_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_bd_exciseIn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_bd_exciseOut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_chain_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_filter_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_filter_cut

