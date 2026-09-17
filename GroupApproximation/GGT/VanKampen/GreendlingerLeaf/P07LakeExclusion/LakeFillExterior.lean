import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lake filling: the exterior piece of a noncrossing walk

Infrastructure for `LakeFillSuccStatement` (`GreendlingerLeaf/P07LakeExclusion/Proof.lean`), Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), step 1 (the lakes of a full arc are filled).

## The mathematical proof of `LakeFillSuccStatement`

Notation.  `M` is the planar map of the diagram `X`, `w = s₁ t₁⁻¹ s₂ t₂⁻¹` the noncrossing closed
walk of the pocket, `S = sideFaces M w` its side, `o` the outer face with `o ∉ S`.  An edge is
*on the boundary of `S`* when one of its darts is a boundary dart of `S`; by
`isBoundaryDart_sideFaces_iff` (the boundary darts of `S` are exactly the walk darts) this happens
exactly when the edge carries a walk dart (`walkKeep`).  Let `C` be the *exterior piece*
`component M S o`: the faces reached from `o` by advancing around faces and crossing edges off the
walk, and `F = absorbed M S o` its complement (the side with every lake filled).  Let `N` be the
map on the walk edges (`walkMap M w`) with face permutation `P`.

1. *Walk darts face away from `C`.*  A walk dart `x` lies on the side, and the piece of `o ∉ S`
   stays off `S`, so `faceOf x ∉ C`.
2. *Crossing out of `C`.*  If `faceOf d ∈ C` and `faceOf (α d) ∉ C` then `α d ∈ w`: otherwise
   the edge of `d` is off the walk (`d ∉ w` by 1), and `Reach.alpha` moves into `α d`.
3. *`C` meets the walk.*  Some `d` has `α d ∈ w` and `faceOf d ∈ C`.  Otherwise, by 2, `C` is
   closed under `α`, and under `σ = P ∘ α`, hence (connectivity of `M`) contains every face, in
   particular the face of a walk dart, against 1.
4. *First return.*  For a walk-edge dart `x`, `P x = σ^m (α x)` for the first `m > 0` with
   `σ^m (α x)` on a walk edge; when `facePerm x` is on a walk edge, `m = 1` and `P x = facePerm x`.
   Also `vertexOf (α x) = vertexOf (P x)`.
5. *`C` lies in one face of `N`.*  Two walk-edge darts `x`, `y` with faces in `C` are joined by
   face moves and crossings off the walk, so (restriction face classes,
   `faceOf_eq_of_faceClass`) `N.faceOf x = N.faceOf y`.
6. *`P` preserves `C`.*  If `faceOf x ∈ C` then the run `x, σ(αx), …, σ^m(αx) = P x` only crosses
   edges off the walk, so `faceOf (P x) ∈ C`, and then `α (P x) ∈ w` by 1.
7. *Faces whose darts all face the walk.*  If every dart `x` of a face `f ≠ o` has `α x ∈ w`, then
   `f ∉ C`: no move from `o` enters `f` (a crossing into `f` would cross a walk edge), so the
   invariant "the face is `f`" is preserved along the whole reach.

Walk (module `LakeFillWalk`).  Start from a walk-edge dart `x₀` with face in `C` and let
`L = [x₀, P x₀, …, P^{p-1} x₀]`, `p` the period of `x₀`.  By 3–6:
* `d ∈ L ↔ α d ∈ w ∧ faceOf d ∈ C` (`⊆` by 6, `⊇` by 5 and `faceOf_eq_iff` of `N`);
* this is `faceOf d ∉ F ∧ (faceOf (α d) ∈ F ∨ α d ∈ L)` (the second disjunct is impossible by 1);
* `L` is duplicate free (distinct powers below the period), chains `vertexOf (α d) = vertexOf e`
  and closes (4);
* *turn to the successor*: for `d = L[i]`, the first `m > 0` with `σ^m (α d)` on an edge of `L`
  is the first return `m₀` of 4: below `m₀` nothing is on a walk edge, and `L` only uses walk
  edges; at `m₀` the dart `P d = L[(i+1) % p]` is in `L`.  So `σ^m (α d) = L[(i+1) % p]`.
So `F` with the outer walk `L` is an `EnclosedFaceSetSucc`, and `o ∉ F`.

Arc (module `LakeFillArc`).  Say `t₁` is full (the case `t₂` full is symmetric).  Every dart `x`
of `Π_i` is a dart of `t₁`, so `α x ∈ w`; by 7, `Π_i ∉ C`, i.e. `Π_i ∈ F` (a relator cell inside).
* If `Π_j ∈ C`: then `t₂` is not full (else `Π_j ∉ C` by 7), start `L` at the first dart of `t₂`;
  along `t₂` consecutive darts follow `facePerm`, and are on walk edges, so by 4 the first
  `|t₂|` entries of `L` are `t₂`.  The remaining entries `r` have `α r ∈ w`, and `r` is neither a
  dart of `t₁` (whose face `Π_i ∉ C`) nor of `t₂` (`L` is duplicate free), so `α r ∈ s₁ ++ s₂`;
  as they are distinct, there are at most `|s₁| + |s₂| ≤ 2ε` of them.  Writing
  `L = t₂ ++ R`, `invDarts L = invDarts R ++ invDarts t₂`, split `invDarts R` at `ε` into
  `s₁'`, `s₂'`, each of length at most `ε`: the arc disjunct with `k = j`, `A = t₂`.
* If `Π_j ∉ C` and `Π_i ∈ C`: symmetric, with `A = t₁`, `Π_j ∈ F`.
* If `Π_i, Π_j ∉ C`: start `L` at the dart of 3; no entry is on `t₁` or `t₂`, so `L` has at most
  `2ε` darts, split `invDarts L` at `ε`.  If some cell `Π_k ∉ F` use its empty arc, otherwise all
  relator cells lie in `F`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

universe v

open Equiv Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent SimpleClosedWalkSides

variable {M : CombMap.{v}} {w : List M.Dart}

/-- An edge is on the boundary of the side exactly when it carries a walk dart. -/
theorem boundaryEdge_iff_walkKeep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : M.Dart) : BoundaryEdge M (sideFaces M w) x ↔ walkKeep M w x := by
  show IsBoundaryDart M (sideFaces M w) x ∨ IsBoundaryDart M (sideFaces M w) (M.alpha x) ↔
    x ∈ w ∨ M.alpha x ∈ w
  exact or_congr (hw.isBoundaryDart_sideFaces_iff hM x)
    (hw.isBoundaryDart_sideFaces_iff hM (M.alpha x))

/-- The face of a walk dart is off the exterior piece. -/
theorem faceOf_not_mem_component (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M w) {x : M.Dart} (hx : x ∈ w) :
    M.faceOf x ∉ component M (sideFaces M w) o := fun hc =>
  not_mem_of_mem_component hout hc
    (show M.faceOf x ∈ sideFaces M w ∧ M.faceOf (M.alpha x) ∉ sideFaces M w from
      (hw.isBoundaryDart_sideFaces_iff hM x).mpr hx).1

/-- Leaving the exterior piece across an edge crosses a reversed walk dart. -/
theorem alpha_mem_of_mem_component (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M w) {d : M.Dart}
    (hc : M.faceOf d ∈ component M (sideFaces M w) o)
    (hα : M.faceOf (M.alpha d) ∉ component M (sideFaces M w) o) : M.alpha d ∈ w := by
  by_contra hnot
  have hoff : ¬ BoundaryEdge M (sideFaces M w) d := by
    rw [boundaryEdge_iff_walkKeep hw hM]
    rintro (hd | hd)
    · exact faceOf_not_mem_component hw hM hout hd hc
    · exact hnot hd
  obtain ⟨y, hy, hr⟩ := mem_component_iff.mp hc
  exact hα (mem_component_iff.mpr ⟨_, rfl, (hr.of_faceOf_eq hy).alpha hoff⟩)

/-- **The exterior piece meets the walk**: some dart with face in the piece reverses a walk
dart. -/
theorem exists_alpha_mem_component (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M w) :
    ∃ d, M.alpha d ∈ w ∧ M.faceOf d ∈ component M (sideFaces M w) o := by
  by_contra hE
  have halpha : ∀ x, M.faceOf x ∈ component M (sideFaces M w) o →
      M.faceOf (M.alpha x) ∈ component M (sideFaces M w) o := by
    intro x hx
    by_contra hα
    exact hE ⟨x, alpha_mem_of_mem_component hw hM hout hx hα, hx⟩
  have hiff : ∀ x, M.faceOf (M.alpha x) ∈ component M (sideFaces M w) o ↔
      M.faceOf x ∈ component M (sideFaces M w) o := by
    intro x
    refine ⟨fun h => ?_, halpha x⟩
    have h' := halpha _ h
    rwa [M.alpha_involutive x] at h'
  have hstep : ∀ x y, M.Adjacent x y → (M.faceOf x ∈ component M (sideFaces M w) o ↔
      M.faceOf y ∈ component M (sideFaces M w) o) := by
    rintro x y (rfl | rfl)
    · exact (hiff x).symm
    · have hsig : M.sigma x = M.facePerm (M.alpha x) := by
        show M.sigma x = M.sigma (M.alpha (M.alpha x))
        rw [M.alpha_involutive x]
      rw [hsig, M.faceOf_facePerm]
      exact (hiff x).symm
  have hall : ∀ x y, Relation.EqvGen M.Adjacent x y →
      (M.faceOf x ∈ component M (sideFaces M w) o ↔
        M.faceOf y ∈ component M (sideFaces M w) o) := by
    intro x y h
    induction h with
    | rel a b hab => exact hstep a b hab
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep o
  have hf₀ : M.faceOf x₀ = o := hx₀
  have hc₀ : M.faceOf x₀ ∈ component M (sideFaces M w) o := by
    rw [hf₀]
    exact self_mem_component o
  exact faceOf_not_mem_component hw hM hout (List.head_mem hw.ne_nil)
    ((hall _ _ (M.connected_of_planar hM x₀ (w.head hw.ne_nil))).mp hc₀)

/-- **First return on the walk edges.**  The face permutation of the map on the walk edges is
the first return of `σ ∘ α`. -/
theorem walkMap_facePerm_firstReturn (x : (walkMap M w).Dart) :
    ∃ m, 0 < m ∧ ((walkMap M w).facePerm x).1 = (M.sigma ^ m) (M.alpha x.1) ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha x.1)) := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M w).sigma_firstReturn ⟨M.alpha x.1, (walkKeep_alpha M w x.1).mpr x.2⟩
  exact ⟨m, hm, hpm.symm, fun k hk hkm hkeep => havoid k hk hkm ⟨⟨_, hkeep⟩, rfl⟩⟩

/-- When the ambient face successor is on a walk edge, the restricted face successor is it. -/
theorem walkMap_facePerm_of_keep (x : (walkMap M w).Dart)
    (h : walkKeep M w (M.facePerm x.1)) : ((walkMap M w).facePerm x).1 = M.facePerm x.1 := by
  obtain ⟨m, hm, hpm, havoid⟩ := walkMap_facePerm_firstReturn x
  have hm1 : m = 1 := by
    by_contra hne
    exact havoid 1 Nat.one_pos (by omega) (by rw [pow_one]; exact h)
  rw [hpm, hm1, pow_one, CombMap.facePerm, Equiv.Perm.mul_apply]

/-- Vertex rotations keep the vertex. -/
theorem lake_vertexOf_sigma_pow (m : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ m) d) = M.vertexOf d := by
  induction m with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, M.vertexOf_sigma, ih]

/-- The restricted face successor starts at the end vertex of a dart. -/
theorem vertexOf_walkMap_facePerm (y : (walkMap M w).Dart) :
    M.vertexOf (M.alpha y.1) = M.vertexOf ((walkMap M w).facePerm y).1 := by
  obtain ⟨m, _, hpm, _⟩ := walkMap_facePerm_firstReturn y
  rw [hpm, lake_vertexOf_sigma_pow]

/-- **The exterior piece lies in one face of the walk map.** -/
theorem walkMap_faceOf_eq (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) {o : M.Face}
    {x y : (walkMap M w).Dart} (hx : M.faceOf x.1 ∈ component M (sideFaces M w) o)
    (hy : M.faceOf y.1 ∈ component M (sideFaces M w) o) :
    (walkMap M w).faceOf x = (walkMap M w).faceOf y := by
  obtain ⟨x', hx', x₀, hx₀, hxr⟩ := mem_component_iff.mp hx
  obtain ⟨y', hy', y₀, hy₀, hyr⟩ := mem_component_iff.mp hy
  have hx1 := eqvGen_faceClass_of_sameCycle M (BoundaryEdge M (sideFaces M w))
    ((M.faceOf_eq_iff x' x.1).mp hx')
  have hy1 := eqvGen_faceClass_of_sameCycle M (BoundaryEdge M (sideFaces M w))
    ((M.faceOf_eq_iff y' y.1).mp hy')
  have h₀ := eqvGen_faceClass_of_sameCycle M (BoundaryEdge M (sideFaces M w))
    ((M.faceOf_eq_iff x₀ y₀).mp (hx₀.trans hy₀.symm))
  have h : Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M (sideFaces M w))) x.1 y.1 :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ hxr hx1))
      (Relation.EqvGen.trans _ _ _ h₀ (Relation.EqvGen.trans _ _ _ hyr hy1))
  have h' : Relation.EqvGen
      (CombMap.FaceClassStep M (· ∈ Set.range (Function.Embedding.subtype (walkKeep M w))))
      x.1 y.1 :=
    faceClass_mono M (fun z hz => by
      rintro ⟨z', rfl⟩
      exact hz ((boundaryEdge_iff_walkKeep hw hM _).mpr z'.2)) h
  exact (walkMap_isRestriction M w).faceOf_eq_of_faceClass hM hw.walkMap_connected
    (d := x) (d' := y) h'

/-- **The restricted face successor stays in the exterior piece**, and reverses a walk dart. -/
theorem walkMap_facePerm_exterior (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M w) (x : (walkMap M w).Dart)
    (hx : M.faceOf x.1 ∈ component M (sideFaces M w) o) :
    M.alpha ((walkMap M w).facePerm x).1 ∈ w ∧
      M.faceOf ((walkMap M w).facePerm x).1 ∈ component M (sideFaces M w) o := by
  obtain ⟨m, hm, hpm, havoid⟩ := walkMap_facePerm_firstReturn x
  have hrun := faceClass_run M (walkKeep M w) x.1 m havoid m hm le_rfl
  rw [← hpm] at hrun
  have hrun' : Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M (sideFaces M w)))
      x.1 ((walkMap M w).facePerm x).1 :=
    faceClass_mono M (fun z hz hb => hz ((boundaryEdge_iff_walkKeep hw hM z).mp hb)) hrun
  obtain ⟨y, hy, hr⟩ := mem_component_iff.mp hx
  obtain ⟨x₀, hx₀, hxr⟩ := hr.of_faceOf_eq hy
  have hc : M.faceOf ((walkMap M w).facePerm x).1 ∈ component M (sideFaces M w) o :=
    mem_component_iff.mpr ⟨_, rfl, x₀, hx₀, Relation.EqvGen.trans _ _ _ hxr hrun'⟩
  refine ⟨?_, hc⟩
  rcases ((walkMap M w).facePerm x).2 with hmem | hmem
  · exact absurd hc (faceOf_not_mem_component hw hM hout hmem)
  · exact hmem

/-- A predicate invariant under face moves and under the allowed crossings is invariant along a
face class. -/
theorem eqvGen_invariant (Q : M.Dart → Prop) {keep : M.Dart → Prop}
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

/-- **A face all of whose darts reverse walk darts is off the exterior piece.** -/
theorem faceOf_not_mem_component_of_forall (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {o f : M.Face} (hfo : f ≠ o) (hf : ∀ x, M.faceOf x = f → M.alpha x ∈ w) :
    f ∉ component M (sideFaces M w) o := by
  intro hc
  obtain ⟨y, hy, x, hx, hxy⟩ := mem_component_iff.mp hc
  have halpha : ∀ z, ¬ BoundaryEdge M (sideFaces M w) z →
      (M.faceOf (M.alpha z) = f ↔ M.faceOf z = f) := by
    intro z hz
    constructor
    · intro h2
      have h3 := hf _ h2
      rw [M.alpha_involutive z] at h3
      exact absurd ((boundaryEdge_iff_walkKeep hw hM z).mpr (Or.inl h3)) hz
    · intro h2
      exact absurd ((boundaryEdge_iff_walkKeep hw hM z).mpr (Or.inr (hf z h2))) hz
  have hQ := eqvGen_invariant (fun z => M.faceOf z = f)
    (fun z => by
      show M.faceOf (M.facePerm z) = f ↔ M.faceOf z = f
      rw [M.faceOf_facePerm]) halpha hxy
  have hxf : M.faceOf x = f := hQ.mpr hy
  exact hfo (hxf.symm.trans hx)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.boundaryEdge_iff_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.faceOf_not_mem_component
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.alpha_mem_of_mem_component
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.exists_alpha_mem_component
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_facePerm_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_facePerm_of_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lake_vertexOf_sigma_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.vertexOf_walkMap_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_facePerm_exterior
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.eqvGen_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.faceOf_not_mem_component_of_forall
