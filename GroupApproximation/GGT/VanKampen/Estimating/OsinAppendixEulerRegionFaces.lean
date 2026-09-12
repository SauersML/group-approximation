import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSubdivided
import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.Meta.AxiomGuard

/-!
# Collapsing the selected regions of a diagram into faces

Let `family` be a pairwise compatible family of contiguity regions of a disc diagram.  Delete every
dart both of whose sides lie in one selected region (`RegionCandidate.RegionInternal`).  The result
`collapsedMap family` is a restriction of the diagram's map, in which:

* the darts of a region's boundary cycle form one face, and nothing else does
  (`collapsed_facePerm_of_boundaryStep`, `collapsed_faceOf_eq_of_mem_cycle`,
  `mem_cycle_of_collapsed_faceOf_eq`);
* a dart whose face is in no selected region keeps its face rotation
  (`collapsed_facePerm_of_face_not_mem`);
* the map is still connected, hence planar (`collapsedMap_connected`, `collapsedMap_planar`).

This is the carrier on which Osin's graph `Φ_M` is realized: in the dual of `collapsedMap family`
the cells are vertices and each region is one vertex, its midpoint.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv
universe u w v

namespace PermFirstReturn

/-- **The first return is the first retained iterate.** -/
theorem apply_eq_of_isFirstReturn {A : Type u} {B : Type v} {p : Perm A} {q : Perm B}
    {e : B ↪ A} (h : IsFirstReturn p q e) {b c : B} {m : ℕ} (hm : 0 < m)
    (hreach : (p ^ m) (e b) = e c)
    (hskip : ∀ k, 0 < k → k < m → (p ^ k) (e b) ∉ Set.range e) : q b = c := by
  obtain ⟨m₀, hm₀, hreach₀, hskip₀⟩ := h b
  rcases lt_trichotomy m m₀ with hlt | heq | hgt
  · exact absurd ⟨c, hreach.symm⟩ (hskip₀ m hm hlt)
  · subst heq
    exact e.injective (hreach₀.symm.trans hreach)
  · exact absurd ⟨q b, hreach₀.symm⟩ (hskip m₀ hm₀ hgt)

/-- **A retained point sharing its ambient cycle with another retained point is moved by the first
return.** -/
theorem apply_ne_self_of_sameCycle {A : Type u} {B : Type v} {p : Perm A} {q : Perm B}
    {e : B ↪ A} (h : IsFirstReturn p q e) {b c : B} (hcb : c ≠ b)
    (hcycle : p.SameCycle (e b) (e c)) [Finite A] : q b ≠ b := by
  intro hq
  obtain ⟨m, hm, hreach, hskip⟩ := h b
  rw [hq] at hreach
  obtain ⟨j, hj⟩ := hcycle.exists_nat_pow_eq
  have hpow : ∀ t : ℕ, (p ^ (m * t)) (e b) = e b := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, hreach, ih]
  have hmod : (p ^ (j % m)) (e b) = e c := by
    rw [← hj]
    conv_rhs => rw [← Nat.mod_add_div j m]
    rw [pow_add, Perm.mul_apply, hpow]
  have hlt : j % m < m := Nat.mod_lt j hm
  by_cases hzero : j % m = 0
  · rw [hzero, pow_zero, Perm.one_apply] at hmod
    exact hcb (e.injective hmod).symm
  · exact hskip (j % m) (by omega) hlt ⟨c, hmod.symm⟩

end PermFirstReturn

/-- **Consecutive elements of a chain carry equal values of any `R`-invariant function.** -/
theorem forall_eq_of_isChain_list {α : Type u} {β : Type v} {R : α → α → Prop} (f : α → β)
    (hR : ∀ x y, R x y → f x = f y) :
    ∀ {l : List α}, l.IsChain R → ∀ x ∈ l, ∀ y ∈ l, f x = f y
  | [], _, x, hx, _, _ => by simp at hx
  | [a], _, x, hx, y, hy => by
      simp only [List.mem_singleton] at hx hy
      rw [hx, hy]
  | a :: b :: l, h, x, hx, y, hy => by
      rw [List.isChain_cons_cons] at h
      have ih := forall_eq_of_isChain_list f hR h.2
      have hall : ∀ z ∈ a :: b :: l, f z = f b := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hR _ _ h.1
        · exact ih z hz b List.mem_cons_self
      rw [hall x hx, hall y hy]

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **The successor of a boundary dart.**  Every dart of a face-set boundary cycle is followed, one
boundary step later, by a dart of the same cycle. -/
theorem FaceSetBoundary.exists_boundaryStep_of_mem {faces : Finset Delta.toCombMap.Face}
    (B : FaceSetBoundary Delta faces) {d : Delta.toCombMap.Dart} (hd : d ∈ B.cycle) :
    ∃ e ∈ B.cycle, BoundaryStep Delta faces d e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  by_cases hnext : i + 1 < B.cycle.length
  · exact ⟨B.cycle[i + 1], List.getElem_mem hnext,
      List.isChain_iff_getElem.mp B.cycle_chain i hnext⟩
  · refine ⟨B.cycle.head B.cycle_nonempty, List.head_mem _, ?_⟩
    have hget : B.cycle[i] = B.cycle.getLast B.cycle_nonempty := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hget]
    exact B.cycle_closes

/-- Iterating internal moves is iterating the vertex rotation through darts internal to the face
set. -/
theorem exists_sigma_pow_of_internalMoves {F : Finset Delta.toCombMap.Face}
    {x e : Delta.toCombMap.Dart}
    (h : Relation.ReflTransGen (InternalBoundaryMove Delta F) x e) :
    ∃ k : ℕ, (Delta.toCombMap.sigma ^ k) x = e ∧ ∀ j, j < k →
      Delta.toCombMap.faceOf ((Delta.toCombMap.sigma ^ j) x) ∈ F ∧
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha ((Delta.toCombMap.sigma ^ j) x)) ∈ F := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | @head x y hxy _ ih =>
      obtain ⟨k, hk, hint⟩ := ih
      obtain ⟨h1, h2, hy⟩ := hxy
      have hy' : y = Delta.toCombMap.sigma x := by
        rw [hy]
        change Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha x)) = _
        rw [Delta.toCombMap.alpha_involutive]
      refine ⟨k + 1, ?_, ?_⟩
      · rw [pow_succ, Perm.mul_apply, ← hy', hk]
      · intro j hj
        cases j with
        | zero =>
            simp only [pow_zero, Perm.one_apply]
            exact ⟨h1, h2⟩
        | succ j =>
            rw [pow_succ, Perm.mul_apply, ← hy']
            exact hint j (by omega)

namespace RegionCandidate

/-- **A dart internal to a selected region**: both of its sides lie in the region. -/
def RegionInternal (family : Finset (RegionCandidate D eps Delta))
    (d : Delta.toCombMap.Dart) : Prop :=
  ∃ a ∈ family, Delta.toCombMap.faceOf d ∈ a.1 ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ a.1

theorem regionInternal_alpha (family : Finset (RegionCandidate D eps Delta))
    (d : Delta.toCombMap.Dart) :
    RegionInternal family (Delta.toCombMap.alpha d) ↔ RegionInternal family d := by
  unfold RegionInternal
  rw [Delta.toCombMap.alpha_involutive d]
  constructor <;> rintro ⟨a, ha, h1, h2⟩ <;> exact ⟨a, ha, h2, h1⟩

/-- **The diagram with the selected regions collapsed**: every dart internal to a selected region
is deleted. -/
noncomputable def collapsedMap (family : Finset (RegionCandidate D eps Delta)) : CombMap.{v} :=
  CombMap.PredicateRestriction.toCombMap Delta.toCombMap (fun d => ¬ RegionInternal family d)
    (fun d => by rw [regionInternal_alpha])

theorem collapsedMap_isRestriction (family : Finset (RegionCandidate D eps Delta)) :
    Delta.toCombMap.IsRestriction (collapsedMap family)
      (Function.Embedding.subtype fun d => ¬ RegionInternal family d) :=
  CombMap.PredicateRestriction.isRestriction _ _ _

variable {family : Finset (RegionCandidate D eps Delta)}

/-- A dart of a selected region's boundary cycle is internal to no selected region. -/
theorem not_regionInternal_of_mem_cycle
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    {a : RegionCandidate D eps Delta} (ha : a ∈ family) {d : Delta.toCombMap.Dart}
    (hd : d ∈ a.2.boundary.cycle) : ¬ RegionInternal family d := by
  rintro ⟨b, hb, h1, h2⟩
  have hboundary := (a.2.boundary.cycle_mem_iff d).mp hd
  by_cases hab : a = b
  · subst hab
    exact hboundary.2 h2
  · exact Finset.disjoint_left.mp (hpairwise a ha b hb hab) hboundary.1 h1

/-- A dart whose face is in no selected region is internal to no selected region. -/
theorem not_regionInternal_of_face_not_mem {d : Delta.toCombMap.Dart}
    (hface : ∀ a ∈ family, Delta.toCombMap.faceOf d ∉ a.1) : ¬ RegionInternal family d := by
  rintro ⟨a, ha, h1, -⟩
  exact hface a ha h1

/-- Being internal to a selected region determines the region. -/
theorem eq_of_face_mem_of_face_mem
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    {a b : RegionCandidate D eps Delta} (ha : a ∈ family) (hb : b ∈ family)
    {f : Delta.toCombMap.Face} (hfa : f ∈ a.1) (hfb : f ∈ b.1) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp (hpairwise a ha b hb hab) hfa hfb

/-- **The face rotation of the collapsed map along a region boundary** is the boundary step. -/
theorem collapsed_facePerm_of_boundaryStep
    {a : RegionCandidate D eps Delta} (ha : a ∈ family) {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta a.1 d e) (hd : ¬ RegionInternal family d)
    (he : ¬ RegionInternal family e) :
    (collapsedMap family).facePerm ⟨d, hd⟩ = ⟨e, he⟩ := by
  classical
  obtain ⟨-, -, hmoves⟩ := hstep
  obtain ⟨k, hk, hint⟩ := exists_sigma_pow_of_internalMoves hmoves
  have hkeepAlpha : ¬ RegionInternal family (Delta.toCombMap.alpha d) := by
    rwa [regionInternal_alpha]
  change CombMap.PredicateRestriction.sigma Delta.toCombMap
    (fun d => ¬ RegionInternal family d) ⟨Delta.toCombMap.alpha d, hkeepAlpha⟩ = ⟨e, he⟩
  apply PermFirstReturn.apply_eq_of_isFirstReturn
    (CombMap.PredicateRestriction.sigma_firstReturn _ _) (m := k + 1) (Nat.succ_pos k)
  · show (Delta.toCombMap.sigma ^ (k + 1)) (Delta.toCombMap.alpha d) = e
    rw [pow_succ, Perm.mul_apply]
    exact hk
  · intro j hj0 hjk hmem
    obtain ⟨x, hx⟩ := hmem
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hint' := hint j' (by omega)
    have hxval : x.1 = (Delta.toCombMap.sigma ^ (j' + 1)) (Delta.toCombMap.alpha d) := hx
    apply x.2
    rw [hxval, pow_succ, Perm.mul_apply]
    exact ⟨a, ha, hint'.1, hint'.2⟩

/-- **The face rotation of the collapsed map at a dart outside the regions** is the diagram's. -/
theorem collapsed_facePerm_of_face_not_mem {d : Delta.toCombMap.Dart}
    (hface : ∀ a ∈ family, Delta.toCombMap.faceOf d ∉ a.1) :
    (collapsedMap family).facePerm ⟨d, not_regionInternal_of_face_not_mem hface⟩ =
      ⟨Delta.toCombMap.facePerm d, not_regionInternal_of_face_not_mem
        (by rwa [Delta.toCombMap.faceOf_facePerm])⟩ := by
  have hkeepAlpha : ¬ RegionInternal family (Delta.toCombMap.alpha d) := by
    rw [regionInternal_alpha]
    exact not_regionInternal_of_face_not_mem hface
  change CombMap.PredicateRestriction.sigma Delta.toCombMap
    (fun d => ¬ RegionInternal family d) ⟨Delta.toCombMap.alpha d, hkeepAlpha⟩ = _
  apply PermFirstReturn.apply_eq_of_isFirstReturn
    (CombMap.PredicateRestriction.sigma_firstReturn _ _) (m := 1) Nat.one_pos
  · show (Delta.toCombMap.sigma ^ 1) (Delta.toCombMap.alpha d) = Delta.toCombMap.facePerm d
    rw [pow_one]
    rfl
  · intro k hk0 hk1
    exact absurd hk1 (by omega)

/-- **All darts of a region's boundary cycle lie in one face of the collapsed map.** -/
theorem collapsed_faceOf_eq_of_mem_cycle
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    {a : RegionCandidate D eps Delta} (ha : a ∈ family) {d d' : Delta.toCombMap.Dart}
    (hd : d ∈ a.2.boundary.cycle) (hd' : d' ∈ a.2.boundary.cycle) :
    (collapsedMap family).faceOf ⟨d, not_regionInternal_of_mem_cycle hpairwise ha hd⟩ =
      (collapsedMap family).faceOf ⟨d', not_regionInternal_of_mem_cycle hpairwise ha hd'⟩ := by
  classical
  let f : Delta.toCombMap.Dart → Option (collapsedMap family).Face := fun x =>
    if h : ¬ RegionInternal family x then some ((collapsedMap family).faceOf ⟨x, h⟩) else none
  have hR : ∀ x y, BoundaryStep Delta a.1 x y → f x = f y := by
    intro x y hxy
    have hx : ¬ RegionInternal family x :=
      not_regionInternal_of_mem_cycle hpairwise ha ((a.2.boundary.cycle_mem_iff x).mpr hxy.1)
    have hy : ¬ RegionInternal family y :=
      not_regionInternal_of_mem_cycle hpairwise ha ((a.2.boundary.cycle_mem_iff y).mpr hxy.2.1)
    simp only [f, dif_pos hx, dif_pos hy]
    rw [← collapsed_facePerm_of_boundaryStep ha hxy hx hy, CombMap.faceOf_facePerm]
  have hall := forall_eq_of_isChain_list f hR a.2.boundary.cycle_chain d hd d' hd'
  simp only [f, dif_pos (not_regionInternal_of_mem_cycle hpairwise ha hd),
    dif_pos (not_regionInternal_of_mem_cycle hpairwise ha hd')] at hall
  exact Option.some.inj hall

/-- **Only the boundary darts of a region lie in its face of the collapsed map.** -/
theorem mem_cycle_of_collapsed_faceOf_eq
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    {a : RegionCandidate D eps Delta} (ha : a ∈ family) {d : Delta.toCombMap.Dart}
    (hd : d ∈ a.2.boundary.cycle) (x : (collapsedMap family).Dart)
    (hx : (collapsedMap family).faceOf x =
      (collapsedMap family).faceOf ⟨d, not_regionInternal_of_mem_cycle hpairwise ha hd⟩) :
    x.1 ∈ a.2.boundary.cycle := by
  have hcycle : (collapsedMap family).facePerm.SameCycle
      ⟨d, not_regionInternal_of_mem_cycle hpairwise ha hd⟩ x :=
    ((collapsedMap family).faceOf_eq_iff _ _).mp hx.symm
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  have hstep : ∀ y : (collapsedMap family).Dart, y.1 ∈ a.2.boundary.cycle →
      ((collapsedMap family).facePerm y).1 ∈ a.2.boundary.cycle := by
    intro y hy
    obtain ⟨e, he, hye⟩ := a.2.boundary.exists_boundaryStep_of_mem hy
    have hfp : (collapsedMap family).facePerm y =
        ⟨e, not_regionInternal_of_mem_cycle hpairwise ha he⟩ :=
      collapsed_facePerm_of_boundaryStep ha hye y.2
        (not_regionInternal_of_mem_cycle hpairwise ha he)
    rw [hfp]
    exact he
  have hpow : ∀ m : ℕ, (((collapsedMap family).facePerm ^ m)
      ⟨d, not_regionInternal_of_mem_cycle hpairwise ha hd⟩).1 ∈ a.2.boundary.cycle := by
    intro m
    induction m with
    | zero => exact hd
    | succ m ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hstep _ ih
  rw [← hn]
  exact hpow n

/-- **Faces of the collapsed map outside the regions are faces of the diagram.** -/
theorem collapsed_faceOf_eq_imp_face_eq {d : Delta.toCombMap.Dart}
    (hface : ∀ a ∈ family, Delta.toCombMap.faceOf d ∉ a.1) (x : (collapsedMap family).Dart)
    (hx : (collapsedMap family).faceOf x =
      (collapsedMap family).faceOf ⟨d, not_regionInternal_of_face_not_mem hface⟩) :
    Delta.toCombMap.faceOf x.1 = Delta.toCombMap.faceOf d := by
  have hcycle : (collapsedMap family).facePerm.SameCycle
      ⟨d, not_regionInternal_of_face_not_mem hface⟩ x :=
    ((collapsedMap family).faceOf_eq_iff _ _).mp hx.symm
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  have hpow : ∀ m : ℕ, ∃ hm : ∀ a ∈ family,
      Delta.toCombMap.faceOf (((collapsedMap family).facePerm ^ m)
        ⟨d, not_regionInternal_of_face_not_mem hface⟩).1 ∉ a.1,
      Delta.toCombMap.faceOf (((collapsedMap family).facePerm ^ m)
        ⟨d, not_regionInternal_of_face_not_mem hface⟩).1 = Delta.toCombMap.faceOf d := by
    intro m
    induction m with
    | zero => exact ⟨hface, rfl⟩
    | succ m ih =>
        obtain ⟨hm, hfm⟩ := ih
        have hdef : ((collapsedMap family).facePerm ^ m)
            ⟨d, not_regionInternal_of_face_not_mem hface⟩ =
            ⟨(((collapsedMap family).facePerm ^ m)
              ⟨d, not_regionInternal_of_face_not_mem hface⟩).1,
              not_regionInternal_of_face_not_mem hm⟩ := rfl
        rw [pow_succ', Perm.mul_apply, hdef, collapsed_facePerm_of_face_not_mem hm]
        refine ⟨?_, ?_⟩
        · intro a ha
          simp only [CombMap.faceOf_facePerm]
          exact hm a ha
        · simp only [CombMap.faceOf_facePerm]
          exact hfm
  obtain ⟨-, hfn⟩ := hpow n
  rw [hn] at hfn
  exact hfn

/-- **The collapsed map is connected.**  A path of the diagram through darts internal to a region
is replaced by the region's boundary, all of whose darts lie in one face of the collapsed map. -/
theorem collapsedMap_connected
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    (hconnected : Delta.toCombMap.IsConnected) :
    (collapsedMap family).IsConnected := by
  classical
  let N := collapsedMap family
  -- the representative of an internal dart: the head of its region's boundary cycle
  have hhead : ∀ a ∈ family, ¬ RegionInternal family (a.2.boundary.cycle.head
      a.2.boundary.cycle_nonempty) := fun a ha =>
    not_regionInternal_of_mem_cycle hpairwise ha (List.head_mem _)
  let rep : Delta.toCombMap.Dart → N.Dart := fun x =>
    if h : ¬ RegionInternal family x then ⟨x, h⟩ else
      ⟨(Classical.choose (not_not.mp h)).2.boundary.cycle.head
          (Classical.choose (not_not.mp h)).2.boundary.cycle_nonempty,
        hhead _ (Classical.choose_spec (not_not.mp h)).1⟩
  have hrep_keep : ∀ x (hx : ¬ RegionInternal family x), rep x = ⟨x, hx⟩ := by
    intro x hx
    simp only [rep, dif_pos hx]
  have hrep_internal : ∀ x, ∀ a, ∀ ha : a ∈ family, Delta.toCombMap.faceOf x ∈ a.1 →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ a.1 →
      rep x = ⟨a.2.boundary.cycle.head a.2.boundary.cycle_nonempty, hhead a ha⟩ := by
    intro x a ha h1 h2
    have hint : RegionInternal family x := ⟨a, ha, h1, h2⟩
    have hchoose := Classical.choose_spec hint
    have heq : Classical.choose hint = a :=
      eq_of_face_mem_of_face_mem hpairwise hchoose.1 ha hchoose.2.1 h1
    simp only [rep, dif_neg (not_not.mpr hint)]
    exact Subtype.ext (congrArg
      (fun b : RegionCandidate D eps Delta => b.2.boundary.cycle.head b.2.boundary.cycle_nonempty)
      heq)
  -- a boundary dart of a region is connected to the region's representative
  have hboundary : ∀ a (ha : a ∈ family) (y : N.Dart), y.1 ∈ a.2.boundary.cycle →
      Relation.EqvGen N.Adjacent y
        ⟨a.2.boundary.cycle.head a.2.boundary.cycle_nonempty, hhead a ha⟩ := by
    intro a ha y hy
    apply N.eqvGen_of_sameCycle_facePerm
    apply (N.faceOf_eq_iff _ _).mp
    have h := collapsed_faceOf_eq_of_mem_cycle hpairwise ha hy
      (List.head_mem a.2.boundary.cycle_nonempty)
    exact h
  have hstep : ∀ x y, Delta.toCombMap.Adjacent x y →
      Relation.EqvGen N.Adjacent (rep x) (rep y) := by
    intro x y hxy
    rcases hxy with rfl | rfl
    · -- edge reversal
      by_cases hx : ¬ RegionInternal family x
      · have hy : ¬ RegionInternal family (Delta.toCombMap.alpha x) := by
          rwa [regionInternal_alpha]
        rw [hrep_keep x hx, hrep_keep _ hy]
        exact Relation.EqvGen.rel _ _ (Or.inl rfl)
      · obtain ⟨a, ha, h1, h2⟩ := not_not.mp hx
        rw [hrep_internal x a ha h1 h2,
          hrep_internal (Delta.toCombMap.alpha x) a ha h2
            (by rwa [Delta.toCombMap.alpha_involutive])]
        exact Relation.EqvGen.refl _
    · -- vertex rotation: `sigma x = facePerm (alpha x)`, so its face is the face of `alpha x`
      have hface : Delta.toCombMap.faceOf (Delta.toCombMap.sigma x) =
          Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) := by
        have h := Delta.toCombMap.faceOf_facePerm (Delta.toCombMap.alpha x)
        change Delta.toCombMap.faceOf
          (Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha x))) = _ at h
        rwa [Delta.toCombMap.alpha_involutive] at h
      by_cases hx : ¬ RegionInternal family x
      · by_cases hy : ¬ RegionInternal family (Delta.toCombMap.sigma x)
        · rw [hrep_keep x hx, hrep_keep _ hy]
          apply Relation.EqvGen.rel
          right
          apply PermFirstReturn.apply_eq_of_isFirstReturn
            (CombMap.PredicateRestriction.sigma_firstReturn _ _) (m := 1) Nat.one_pos
          · show (Delta.toCombMap.sigma ^ 1) x = Delta.toCombMap.sigma x
            rw [pow_one]
          · intro k hk0 hk1
            exact absurd hk1 (by omega)
        · obtain ⟨a, ha, h1, h2⟩ := not_not.mp hy
          rw [hrep_keep x hx, hrep_internal _ a ha h1 h2]
          -- `alpha x` is a boundary dart of `a`
          have halpha : Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ a.1 := hface ▸ h1
          have hxa : Delta.toCombMap.faceOf x ∉ a.1 := by
            intro hxa
            exact hx ⟨a, ha, hxa, halpha⟩
          have hmem : Delta.toCombMap.alpha x ∈ a.2.boundary.cycle := by
            refine (a.2.boundary.cycle_mem_iff _).mpr ⟨halpha, ?_⟩
            rwa [Delta.toCombMap.alpha_involutive]
          have hkeepAlpha : ¬ RegionInternal family (Delta.toCombMap.alpha x) := by
            rwa [regionInternal_alpha]
          refine Relation.EqvGen.trans _ ⟨Delta.toCombMap.alpha x, hkeepAlpha⟩ _
            (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
          exact hboundary a ha ⟨Delta.toCombMap.alpha x, hkeepAlpha⟩ hmem
      · obtain ⟨a, ha, h1, h2⟩ := not_not.mp hx
        by_cases hy : ¬ RegionInternal family (Delta.toCombMap.sigma x)
        · rw [hrep_internal x a ha h1 h2, hrep_keep _ hy]
          -- `sigma x` is a boundary dart of `a`
          have hya : Delta.toCombMap.faceOf (Delta.toCombMap.sigma x) ∈ a.1 := hface ▸ h2
          have hmem : Delta.toCombMap.sigma x ∈ a.2.boundary.cycle := by
            refine (a.2.boundary.cycle_mem_iff _).mpr ⟨hya, ?_⟩
            intro hout
            exact hy ⟨a, ha, hya, hout⟩
          exact Relation.EqvGen.symm _ _
            (hboundary a ha ⟨Delta.toCombMap.sigma x, hy⟩ hmem)
        · obtain ⟨b, hb, h1b, h2b⟩ := not_not.mp hy
          have hya : Delta.toCombMap.faceOf (Delta.toCombMap.sigma x) ∈ a.1 := hface ▸ h2
          have hab : a = b := eq_of_face_mem_of_face_mem hpairwise ha hb hya h1b
          subst hab
          rw [hrep_internal x a ha h1 h2, hrep_internal _ a hb h1b h2b]
          exact Relation.EqvGen.refl _
  have hlift : ∀ x y, Relation.EqvGen Delta.toCombMap.Adjacent x y →
      Relation.EqvGen N.Adjacent (rep x) (rep y) := by
    intro x y h
    induction h with
    | rel x y h => exact hstep x y h
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  intro x y
  have h := hlift x.1 y.1 (hconnected x.1 y.1)
  rwa [hrep_keep x.1 x.2, hrep_keep y.1 y.2] at h

/-- **The collapsed map is planar**, as a connected restriction of a planar map with a retained
dart. -/
theorem collapsedMap_planar
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    (d : (collapsedMap family).Dart) : (collapsedMap family).IsPlanar :=
  (collapsedMap_isRestriction family).planar Delta.planar
    (collapsedMap_connected hpairwise Delta.planar.1) d

end RegionCandidate
end Embedded
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.apply_eq_of_isFirstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.apply_ne_self_of_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.forall_eq_of_isChain_list
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.exists_boundaryStep_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_facePerm_of_boundaryStep
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_facePerm_of_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_faceOf_eq_of_mem_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_cycle_of_collapsed_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_faceOf_eq_imp_face_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsedMap_connected
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsedMap_planar
