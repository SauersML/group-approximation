import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSeven
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: clean lobes give sign-keeping excision steps

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-65.

Route.  Split the darts of a reached walk `c` as a lobe `W` (a simple closed stretch: the inner
stretch `A` of `c = p ++ A ++ q`, or the wrapping stretch `q ++ p`) and its rest `R`.  The lobe
is **clean** (`gfaceWindEight_Clean`) when its face class (the darts reached from `W` by
advancing around faces and crossing edges off `W`, whose faces are the side of `W`) contains no
dart of an edge of `R`.

* `gfaceWindEight_const`: a face function cobounded by `c` is constant on that face class.
  A face step keeps the face; an alpha step crosses an edge off `W`, hence (cleanliness) off
  `R`, hence off `c`, where the coboundary vanishes.
* `gfaceWindEight_side_pos`: if `g ≥ 0`, then `g ≥ 1` on the side of a clean lobe: at a dart
  `d` of `W`, `g (faceOf d) = g (faceOf (alpha d)) + 1`.
* `gfaceWindEight_nonneg`, `gfaceWindEight_step`: since `g o = 0`, the base face is off the
  side, so `wind_W` is the side indicator and `g - wind_W ≥ 0`: excising a clean lobe is a
  sign-keeping step.  No planarity, sign-only.

## Truth check

Scratchpad `gl-p10-65/eight.py` (reusing `gl-p10-64/seven.py`): excising a clean lobe from a
reached state with `g ≥ 0` kept `g ≥ 0` in every instance (`SANITYFAIL` 0, random seeds 1 and
3, witness seed 2), as this module proves.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A clean lobe** `W` with rest `R`: no dart of the face class of `W` (in the map cut along
the edges of `W`) lies on an edge of `R`. -/
def gfaceWindEight_Clean (M : CombMap.{v}) (W R : List M.Dart) : Prop :=
  ∀ d ∈ W, ∀ y : M.Dart,
    Relation.EqvGen (CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M W)) d y →
      y ∉ R ∧ M.alpha y ∉ R

/-- **Constancy on the face class of a clean lobe**: a face function cobounded by `c`, whose
darts lie on `W` or `R`, is constant along face-class chains of `W` from a dart `d` whose class
avoids the edges of `R`. -/
theorem gfaceWindEight_const {M : CombMap.{v}} {c W R : List M.Dart} {g : M.Face → ℤ}
    (hcov : ∀ x ∈ c, x ∈ W ∨ x ∈ R)
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d)) {d : M.Dart}
    (hcl : ∀ y : M.Dart,
      Relation.EqvGen (CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M W)) d y →
        y ∉ R ∧ M.alpha y ∉ R) :
    ∀ y z : M.Dart,
      Relation.EqvGen (CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M W)) y z →
      Relation.EqvGen (CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M W)) d y →
        g (M.faceOf y) = g (M.faceOf z) := by
  intro y z h
  induction h with
  | rel x₁ _ hst =>
      intro hd
      rcases hst with rfl | ⟨hk, rfl⟩
      · rw [M.faceOf_facePerm x₁]
      · have n1W : x₁ ∉ W := fun h => hk (Or.inl h)
        have n2W : M.alpha x₁ ∉ W := fun h => hk (Or.inr h)
        obtain ⟨h1, h2⟩ := hcl x₁ hd
        have n1 : x₁ ∉ c := fun hx => (hcov x₁ hx).elim n1W h1
        have n2 : M.alpha x₁ ∉ c := fun hx => (hcov _ hx).elim n2W h2
        have h3 := hcob x₁
        linarith [gfaceWind_lind_neg n1, gfaceWind_lind_neg n2]
  | refl _ =>
      intro _
      rfl
  | symm _ _ hrel ih =>
      intro hd
      exact (ih (.trans _ _ _ hd (.symm _ _ hrel))).symm
  | trans _ _ _ h₁₂ _ ih₁ ih₂ =>
      intro hd
      exact (ih₁ hd).trans (ih₂ (.trans _ _ _ hd h₁₂))

/-- **`g ≥ 1` on the side of a clean lobe** of a walk `c` with no reversed dart, for a
nonnegative face function cobounded by `c`. -/
theorem gfaceWindEight_side_pos {M : CombMap.{v}} {c W R : List M.Dart} {g : M.Face → ℤ}
    (hcov : ∀ x ∈ c, x ∈ W ∨ x ∈ R) (hWc : ∀ x ∈ W, x ∈ c)
    (hal : ∀ x ∈ c, M.alpha x ∉ c)
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (hpos : ∀ f, 0 ≤ g f) (hcl : gfaceWindEight_Clean M W R) :
    ∀ f ∈ SimpleClosedWalkSides.sideFaces M W, 1 ≤ g f := by
  intro f hf
  obtain ⟨z, hz⟩ := Quotient.exists_rep f
  have hz' : M.faceOf z = f := hz
  subst hz'
  obtain ⟨d, hd, hdz⟩ := (SimpleClosedWalkSides.mem_sideFaces_iff M W z).mp hf
  have hdc : d ∈ c := hWc d hd
  have h1 := hcob d
  have e : g (M.faceOf d) = g (M.faceOf z) :=
    gfaceWindEight_const hcov hcob (hcl d hd) d z hdz (.refl _)
  have h2 := hpos (M.faceOf (M.alpha d))
  linarith [gfaceWind_lind_pos hdc, gfaceWind_lind_neg (hal d hdc)]

/-- **Subtracting the winding function of a clean lobe keeps `g ≥ 0`**: the base face, where
`g` vanishes, is off the side, so `wind_W` is the side indicator and `g ≥ 1` there. -/
theorem gfaceWindEight_nonneg {M : CombMap.{v}} {o : M.Face} {c W R : List M.Dart}
    {g : M.Face → ℤ} (hcov : ∀ x ∈ c, x ∈ W ∨ x ∈ R) (hWc : ∀ x ∈ W, x ∈ c)
    (hal : ∀ x ∈ c, M.alpha x ∉ c)
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (hpos : ∀ f, 0 ≤ g f) (hcl : gfaceWindEight_Clean M W R) (hog : g o = 0) :
    ∀ f, 0 ≤ g f - gfaceWind_wind M o W f := by
  have hside := gfaceWindEight_side_pos hcov hWc hal hcob hpos hcl
  have hoW : o ∉ SimpleClosedWalkSides.sideFaces M W := fun h => by
    have h' := hside o h
    linarith
  intro f
  have h1 : gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o = 0 := gfaceWind_ind_neg hoW
  have h3 : gfaceWind_wind M o W f = gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) f -
      gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o := rfl
  by_cases hf : f ∈ SimpleClosedWalkSides.sideFaces M W
  · linarith [gfaceWind_ind_pos hf, hside f hf]
  · linarith [gfaceWind_ind_neg hf, hpos f]

/-- **Excising a clean lobe is a sign-keeping step**, at a state satisfying the invariant over a
walk `C` bounding `F`: either the inner stretch `A` is a clean simple lobe with rest `p ++ q`,
or the wrapping stretch `q ++ p` is a clean simple lobe with rest `A`. -/
theorem gfaceWindEight_step {M : CombMap.{v}} {C : List M.Dart} {F : Finset M.Face}
    {o : M.Face} (hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart M F d ↔ d ∈ C)
    {c : List M.Dart} {g : M.Face → ℤ} (hinv : gfaceWind_Inv M C o c g)
    (hpos : ∀ f, 0 ≤ g f) {p A q : List M.Dart} (hseg : c = p ++ A ++ q)
    (h : (IsSimpleClosedWalk M A ∧ gfaceWindEight_Clean M A (p ++ q)) ∨
      (IsSimpleClosedWalk M (q ++ p) ∧ gfaceWindEight_Clean M (q ++ p) A)) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f := by
  obtain ⟨hfil, -, hcob, hog⟩ := hinv
  have hsub : ∀ x ∈ c, x ∈ C := by
    intro x hx
    have hx' : x ∈ C.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hal : ∀ x ∈ c, M.alpha x ∉ c := fun x hx hax =>
    ((hS x).mpr (hsub x hx)).2 ((hS _).mpr (hsub _ hax)).1
  subst hseg
  rcases h with ⟨hA, hcl⟩ | ⟨hB, hcl⟩
  · have hcov : ∀ x ∈ p ++ A ++ q, x ∈ A ∨ x ∈ p ++ q := by
      intro x hx
      simp only [List.mem_append] at hx ⊢
      tauto
    have hWc : ∀ x ∈ A, x ∈ p ++ A ++ q := fun x hx =>
      List.mem_append_left q (List.mem_append_right p hx)
    exact ⟨(p ++ q, fun f => g f - gfaceWind_wind M o A f),
      ⟨p, A, q, rfl, Or.inl ⟨hA, rfl, rfl⟩⟩,
      gfaceWindEight_nonneg hcov hWc hal hcob hpos hcl hog⟩
  · have hcov : ∀ x ∈ p ++ A ++ q, x ∈ q ++ p ∨ x ∈ A := by
      intro x hx
      simp only [List.mem_append] at hx ⊢
      tauto
    have hWc : ∀ x ∈ q ++ p, x ∈ p ++ A ++ q := by
      intro x hx
      simp only [List.mem_append] at hx ⊢
      tauto
    exact ⟨(A, fun f => g f - gfaceWind_wind M o (q ++ p) f),
      ⟨p, A, q, rfl, Or.inr ⟨hB, rfl, rfl⟩⟩,
      gfaceWindEight_nonneg hcov hWc hal hcob hpos hcl hog⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_Clean
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_const
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_side_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_nonneg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEight_step
