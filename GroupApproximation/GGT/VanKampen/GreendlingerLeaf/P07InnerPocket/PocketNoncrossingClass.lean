import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the face class of the pocket keep-set

Lane `gl-p07-05`, first module.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Notation

`M` is a combinatorial map and `keep` an `alpha`-closed dart predicate (for the pocket,
`Q₀ = walkKeep K ∨ walkKeep ∂a ∨ walkKeep ∂b`, `pocketKeep`).  `faceClass M keep c` is the set of
faces reached from the face `c` by advancing around faces and crossing edges off `keep`.

## What this module proves

1. *Membership at a dart* (`faceOf_mem_faceClass_iff`): the face of `x` is in the class iff `x`
   is reached from a dart of `c`.
2. *Closure under crossings off `keep`* (`faceOf_alpha_mem_faceClass`).
3. *Monotonicity against a closed walk* (`faceClass_subset_sideFaces`): if the edges of `K` are
   kept and `c ∈ sideFaces K`, the class lies in `sideFaces K` (fewer kept darts give larger
   classes, `faceClass_mono`).
4. *Avoiding a region* (`faceClass_not_mem_region`): if every boundary edge of a face set `F` is
   kept and `c ∉ F`, no face of the class is in `F`.  The invariant "the face is in `F`" survives
   face moves, and crossing an unkept edge never crosses the boundary of `F`.
5. *No bridge* (`pocketKeep_bridge_free`): a kept edge never has both sides in the class.
   * Edges of `K`: one side is off `sideFaces K` (`isBoundaryDart_sideFaces_iff`), by 3.
   * Edges of `∂a` or `∂b`: one side is in `a` or `b`, by 4.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open Equiv SimpleClosedWalkSides Surgery.MapCollapse

namespace PocketNoncrossing

/-- **The face class of `c`** for a retained dart set `keep`: faces reached from `c` by face moves
and crossings of unretained edges. -/
noncomputable def faceClass (M : CombMap.{u}) (keep : M.Dart → Prop) (c : M.Face) :
    Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧
    ∃ y, M.faceOf y = c ∧ Relation.EqvGen (CombMap.FaceClassStep M keep) y x

theorem mem_faceClass_iff (M : CombMap.{u}) (keep : M.Dart → Prop) (c f : M.Face) :
    f ∈ faceClass M keep c ↔ ∃ x, M.faceOf x = f ∧
      ∃ y, M.faceOf y = c ∧ Relation.EqvGen (CombMap.FaceClassStep M keep) y x := by
  classical
  unfold faceClass
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩

theorem faceOf_mem_faceClass_iff (M : CombMap.{u}) (keep : M.Dart → Prop) (c : M.Face)
    (x : M.Dart) :
    M.faceOf x ∈ faceClass M keep c ↔
      ∃ y, M.faceOf y = c ∧ Relation.EqvGen (CombMap.FaceClassStep M keep) y x := by
  rw [mem_faceClass_iff]
  constructor
  · rintro ⟨x', hx', y, hy, h⟩
    exact ⟨y, hy, .trans _ _ _ h
      (eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff x' x).mp hx'))⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨x, rfl, y, hy, h⟩

/-- Crossing an unretained edge stays in the class. -/
theorem faceOf_alpha_mem_faceClass (M : CombMap.{u}) (keep : M.Dart → Prop) (c : M.Face)
    {x : M.Dart} (hk : ¬ keep x) (hx : M.faceOf x ∈ faceClass M keep c) :
    M.faceOf (M.alpha x) ∈ faceClass M keep c := by
  obtain ⟨y, hy, h⟩ := (faceOf_mem_faceClass_iff M keep c x).mp hx
  exact (faceOf_mem_faceClass_iff M keep c _).mpr
    ⟨y, hy, .trans _ _ _ h (.rel _ _ (Or.inr ⟨hk, rfl⟩))⟩

/-- A predicate invariant under face moves and under the allowed crossings is invariant along a
face class. -/
theorem invariant_of_eqvGen (M : CombMap.{u}) (Q : M.Dart → Prop) {keep : M.Dart → Prop}
    (hface : ∀ x, Q (M.facePerm x) ↔ Q x) (halpha : ∀ x, ¬ keep x → (Q (M.alpha x) ↔ Q x))
    {x y : M.Dart} (h : Relation.EqvGen (CombMap.FaceClassStep M keep) x y) : Q x ↔ Q y := by
  induction h with
  | rel a b hab =>
      rcases hab with rfl | ⟨hk, rfl⟩
      · exact (hface a).symm
      · exact (halpha a hk).symm
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The class lies on the side of a closed walk whose edges are retained.** -/
theorem faceClass_subset_sideFaces (M : CombMap.{u}) (keep : M.Dart → Prop) {K : List M.Dart}
    {c : M.Face} (hk : ∀ x, walkKeep M K x → keep x) (hc : c ∈ sideFaces M K) :
    faceClass M keep c ⊆ sideFaces M K := by
  intro f hf
  obtain ⟨z, hz⟩ := Quotient.exists_rep f
  have hz' : M.faceOf z = f := hz
  subst hz'
  obtain ⟨y, hy, hyz⟩ := (faceOf_mem_faceClass_iff M keep c z).mp hf
  have hy' : M.faceOf y ∈ sideFaces M K := by
    rw [hy]
    exact hc
  obtain ⟨d, hd, hdy⟩ := (mem_sideFaces_iff M K y).mp hy'
  exact (mem_sideFaces_iff M K z).mpr
    ⟨d, hd, .trans _ _ _ hdy
      (faceClass_mono M (keep := keep) (keep' := walkKeep M K) (fun x hx hw => hx (hk x hw))
        hyz)⟩

/-- **The class avoids a face set whose boundary edges are retained.**  `cyc` is the list of
boundary darts of `F`. -/
theorem faceClass_not_mem_region (M : CombMap.{u}) (keep : M.Dart → Prop) {F : Finset M.Face}
    {cyc : List M.Dart}
    (hcyc : ∀ d, d ∈ cyc ↔ M.faceOf d ∈ F ∧ M.faceOf (M.alpha d) ∉ F)
    (hk : ∀ x, walkKeep M cyc x → keep x) {c : M.Face} (hc : c ∉ F) :
    ∀ f ∈ faceClass M keep c, f ∉ F := by
  have halpha : ∀ x, ¬ keep x → (M.faceOf (M.alpha x) ∈ F ↔ M.faceOf x ∈ F) := by
    intro x hx
    have h1 : x ∉ cyc := fun h => hx (hk x (Or.inl h))
    have h2 : M.alpha x ∉ cyc := fun h => hx (hk x (Or.inr h))
    constructor
    · intro ha
      by_contra hxF
      refine h2 ((hcyc _).mpr ⟨ha, ?_⟩)
      rw [M.alpha_involutive x]
      exact hxF
    · intro hxF
      by_contra ha
      exact h1 ((hcyc x).mpr ⟨hxF, ha⟩)
  intro f hf hfF
  obtain ⟨z, hz⟩ := Quotient.exists_rep f
  have hz' : M.faceOf z = f := hz
  subst hz'
  obtain ⟨y, hy, hyz⟩ := (faceOf_mem_faceClass_iff M keep c z).mp hf
  have hinv : M.faceOf y ∈ F ↔ M.faceOf z ∈ F :=
    invariant_of_eqvGen M (fun x => M.faceOf x ∈ F)
      (fun x => by
        show M.faceOf (M.facePerm x) ∈ F ↔ M.faceOf x ∈ F
        rw [M.faceOf_facePerm]) halpha hyz
  have hyF : M.faceOf y ∈ F := hinv.mpr hfF
  rw [hy] at hyF
  exact hc hyF

/-- **The pocket keep-set**: the edges of the walk `K` and of the two region cycles. -/
def pocketKeep (M : CombMap.{u}) (K c₁ c₂ : List M.Dart) (d : M.Dart) : Prop :=
  walkKeep M K d ∨ walkKeep M c₁ d ∨ walkKeep M c₂ d

theorem pocketKeep_alpha (M : CombMap.{u}) (K c₁ c₂ : List M.Dart) (d : M.Dart) :
    pocketKeep M K c₁ c₂ (M.alpha d) ↔ pocketKeep M K c₁ c₂ d := by
  simp only [pocketKeep, walkKeep_alpha]

/-- **No bridge.**  A retained edge never has both sides in the class of a face `c` that lies on
the side of `K` and outside both regions. -/
theorem pocketKeep_bridge_free {M : CombMap.{u}} (hM : M.IsPlanar) {K c₁ c₂ : List M.Dart}
    (hw : IsNoncrossingClosedWalk M K) {F₁ F₂ : Finset M.Face}
    (hcyc₁ : ∀ d, d ∈ c₁ ↔ M.faceOf d ∈ F₁ ∧ M.faceOf (M.alpha d) ∉ F₁)
    (hcyc₂ : ∀ d, d ∈ c₂ ↔ M.faceOf d ∈ F₂ ∧ M.faceOf (M.alpha d) ∉ F₂)
    {c : M.Face} (hcK : c ∈ sideFaces M K) (hc₁ : c ∉ F₁) (hc₂ : c ∉ F₂) :
    ∀ d, pocketKeep M K c₁ c₂ d →
      ¬ (M.faceOf d ∈ faceClass M (pocketKeep M K c₁ c₂) c ∧
        M.faceOf (M.alpha d) ∈ faceClass M (pocketKeep M K c₁ c₂) c) := by
  rintro d hd ⟨hS, hSa⟩
  have hsub := faceClass_subset_sideFaces M (pocketKeep M K c₁ c₂)
    (fun x hx => Or.inl hx) hcK
  have hav₁ := faceClass_not_mem_region M (pocketKeep M K c₁ c₂) hcyc₁
    (fun x hx => Or.inr (Or.inl hx)) hc₁
  have hav₂ := faceClass_not_mem_region M (pocketKeep M K c₁ c₂) hcyc₂
    (fun x hx => Or.inr (Or.inr hx)) hc₂
  rcases hd with hK | h₁ | h₂
  · rcases hK with hdK | haK
    · have hb : M.faceOf d ∈ sideFaces M K ∧ M.faceOf (M.alpha d) ∉ sideFaces M K :=
        (hw.isBoundaryDart_sideFaces_iff hM d).mpr hdK
      exact hb.2 (hsub hSa)
    · have hb : M.faceOf (M.alpha d) ∈ sideFaces M K ∧
          M.faceOf (M.alpha (M.alpha d)) ∉ sideFaces M K :=
        (hw.isBoundaryDart_sideFaces_iff hM (M.alpha d)).mpr haK
      rw [M.alpha_involutive d] at hb
      exact hb.2 (hsub hS)
  · rcases h₁ with hd₁ | ha₁
    · exact hav₁ _ hS ((hcyc₁ d).mp hd₁).1
    · exact hav₁ _ hSa ((hcyc₁ _).mp ha₁).1
  · rcases h₂ with hd₂ | ha₂
    · exact hav₂ _ hS ((hcyc₂ d).mp hd₂).1
    · exact hav₂ _ hSa ((hcyc₂ _).mp ha₂).1

end PocketNoncrossing

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.pocketKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.mem_faceClass_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.faceOf_mem_faceClass_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.faceOf_alpha_mem_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.invariant_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.faceClass_subset_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.faceClass_not_mem_region
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.pocketKeep_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.pocketKeep_bridge_free
