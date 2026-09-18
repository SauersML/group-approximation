import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillExterior
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lake filling: the outer walk of the filled side

Infrastructure for `LakeFillSuccStatement` (`GreendlingerLeaf/P07LakeExclusion/Proof.lean`); the
mathematical proof is in the docstring of `LakeFillExterior`, paragraph *Walk*.

* `period P x₀`, `orbitMap P x₀ f`: the orbit `[f x₀, f (P x₀), …]` of a point under a permutation of
  a finite type, up to its period; it is duplicate free, chains and closes along any relation the
  steps satisfy, and its successor entry is `f (P (P^i x₀))`.
* `lakeWalk M w x₀`: the orbit of a walk-edge dart `x₀` under the face permutation of the walk map.
* `lakeWalk_enclosedFaceSetSucc`: when `x₀` faces the exterior piece, the absorbed face set with the
  outer walk `lakeWalk` is an `EnclosedFaceSetSucc`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

universe u w v

open Equiv Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent SimpleClosedWalkSides

section Period

open scoped Classical

variable {α : Type*} [Finite α] (P : Perm α) (x₀ : α)

/-- A point of a finite permutation returns to itself. -/
theorem exists_pow_apply_eq_self : ∃ n, 0 < n ∧ (P ^ n) x₀ = x₀ :=
  ⟨orderOf P, orderOf_pos P, by rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]⟩

/-- The period of a point under a permutation of a finite type. -/
noncomputable def period : ℕ :=
  Nat.find (exists_pow_apply_eq_self P x₀)

theorem period_spec : 0 < period P x₀ ∧ (P ^ period P x₀) x₀ = x₀ :=
  Nat.find_spec (exists_pow_apply_eq_self P x₀)

theorem period_le {n : ℕ} (hn : 0 < n) (h : (P ^ n) x₀ = x₀) : period P x₀ ≤ n :=
  Nat.find_min' (exists_pow_apply_eq_self P x₀) ⟨hn, h⟩

theorem pow_period_mul_apply (k : ℕ) : (P ^ (period P x₀ * k)) x₀ = x₀ := by
  rw [pow_mul]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (period_spec P x₀).2 k

theorem pow_mod_period (n : ℕ) : (P ^ (n % period P x₀)) x₀ = (P ^ n) x₀ := by
  have h : (P ^ (n % period P x₀ + period P x₀ * (n / period P x₀))) x₀ = (P ^ n) x₀ := by
    rw [Nat.mod_add_div]
  rwa [pow_add, Equiv.Perm.mul_apply, pow_period_mul_apply] at h

/-- Powers below the period give distinct points. -/
theorem pow_apply_inj {i j : ℕ} (hi : i < period P x₀) (hj : j < period P x₀)
    (h : (P ^ i) x₀ = (P ^ j) x₀) : i = j := by
  have key : ∀ a b, a < b → b < period P x₀ → (P ^ a) x₀ = (P ^ b) x₀ → False := by
    intro a b hab hb hab'
    have h1 : (P ^ (b - a)) x₀ = x₀ := by
      apply (P ^ a).injective
      show (P ^ a * P ^ (b - a)) x₀ = (P ^ a) x₀
      rw [← pow_add, Nat.add_sub_of_le hab.le]
      exact hab'.symm
    have h2 := period_le P x₀ (Nat.sub_pos_of_lt hab) h1
    omega
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

/-- The orbit of `x₀` up to its period, read through `f`. -/
noncomputable def orbitMap {β : Type*} (f : α → β) : List β :=
  (List.range (period P x₀)).map fun n => f ((P ^ n) x₀)

theorem length_orbitMap {β : Type*} (f : α → β) :
    (orbitMap P x₀ f).length = period P x₀ := by
  simp only [orbitMap, List.length_map, List.length_range]

theorem getElem_orbitMap {β : Type*} (f : α → β) (i : ℕ) (hi : i < (orbitMap P x₀ f).length) :
    (orbitMap P x₀ f)[i]'hi = f ((P ^ i) x₀) := by
  simp only [orbitMap, List.getElem_map, List.getElem_range]

theorem mem_orbitMap_iff {β : Type*} (f : α → β) (y : β) :
    y ∈ orbitMap P x₀ f ↔ ∃ n, f ((P ^ n) x₀) = y := by
  unfold orbitMap
  rw [List.mem_map]
  constructor
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n % period P x₀, List.mem_range.mpr (Nat.mod_lt _ (period_spec P x₀).1), ?_⟩
    exact congrArg f (pow_mod_period P x₀ n)

theorem nodup_orbitMap {β : Type*} {f : α → β} (hf : Function.Injective f) :
    (orbitMap P x₀ f).Nodup := by
  unfold orbitMap
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb hab
  exact pow_apply_inj P x₀ (List.mem_range.mp ha) (List.mem_range.mp hb) (hf hab)

theorem orbitMap_getElem_succ_mod {β : Type*} (f : α → β) (i : ℕ)
    (hi : i < (orbitMap P x₀ f).length) :
    (orbitMap P x₀ f)[(i + 1) % (orbitMap P x₀ f).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
      f (P ((P ^ i) x₀)) := by
  rw [getElem_orbitMap, length_orbitMap, pow_mod_period, pow_succ', Equiv.Perm.mul_apply]

theorem orbitMap_isChain {β : Type*} (f : α → β) {R : β → β → Prop}
    (hR : ∀ n, R (f ((P ^ n) x₀)) (f ((P ^ (n + 1)) x₀))) : (orbitMap P x₀ f).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  rw [getElem_orbitMap, getElem_orbitMap]
  exact hR i

theorem orbitMap_closes {β : Type*} (f : α → β) {R : β → β → Prop}
    (hR : ∀ n, R (f ((P ^ n) x₀)) (f ((P ^ (n + 1)) x₀))) (hne : orbitMap P x₀ f ≠ []) :
    R ((orbitMap P x₀ f).getLast hne) ((orbitMap P x₀ f).head hne) := by
  rw [List.getLast_eq_getElem, List.head_eq_getElem, getElem_orbitMap, getElem_orbitMap,
    length_orbitMap, pow_zero, Equiv.Perm.one_apply]
  have h := hR (period P x₀ - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ period P x₀ from (period_spec P x₀).1)] at h
  rwa [(period_spec P x₀).2] at h

end Period

/-- **The outer walk of the filled side**: the face orbit of a walk-edge dart in the walk map. -/
noncomputable def lakeWalk (M : CombMap.{v}) (wk : List M.Dart) (x₀ : (walkMap M wk).Dart) :
    List M.Dart :=
  orbitMap (walkMap M wk).facePerm x₀ fun d : (walkMap M wk).Dart => d.1

section Walk

variable {M : CombMap.{v}} {wk : List M.Dart}

theorem length_lakeWalk (x₀ : (walkMap M wk).Dart) :
    (lakeWalk M wk x₀).length = period (walkMap M wk).facePerm x₀ :=
  length_orbitMap _ _ _

theorem getElem_lakeWalk (x₀ : (walkMap M wk).Dart) (i : ℕ) (hi : i < (lakeWalk M wk x₀).length) :
    (lakeWalk M wk x₀)[i]'hi = (((walkMap M wk).facePerm ^ i) x₀).1 :=
  getElem_orbitMap _ _ _ i hi

theorem lakeWalk_getElem_succ_mod (x₀ : (walkMap M wk).Dart) (i : ℕ)
    (hi : i < (lakeWalk M wk x₀).length) :
    (lakeWalk M wk x₀)[(i + 1) % (lakeWalk M wk x₀).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
      ((walkMap M wk).facePerm (((walkMap M wk).facePerm ^ i) x₀)).1 :=
  orbitMap_getElem_succ_mod _ _ _ i hi

theorem walkMap_facePerm_pow_exterior (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) :
    ∀ n : ℕ, M.faceOf (((walkMap M wk).facePerm ^ n) x₀).1 ∈ component M (sideFaces M wk) o := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact hx₀
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (walkMap_facePerm_exterior hw hM hout _ ih).2

theorem alpha_mem_of_exterior (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) (x : (walkMap M wk).Dart)
    (hx : M.faceOf x.1 ∈ component M (sideFaces M wk) o) : M.alpha x.1 ∈ wk := by
  rcases x.2 with hmem | hmem
  · exact absurd hx (faceOf_not_mem_component hw hM hout hmem)
  · exact hmem

/-- **The darts of the outer walk** are the reverses of walk darts facing the exterior piece. -/
theorem mem_lakeWalk_iff (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) (d : M.Dart) :
    d ∈ lakeWalk M wk x₀ ↔ M.alpha d ∈ wk ∧ M.faceOf d ∈ component M (sideFaces M wk) o := by
  unfold lakeWalk
  rw [mem_orbitMap_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have hc := walkMap_facePerm_pow_exterior hw hM hout hx₀ n
    exact ⟨alpha_mem_of_exterior hw hM hout _ hc, hc⟩
  · rintro ⟨hα, hc⟩
    have hface := walkMap_faceOf_eq hw hM (x := x₀) (y := ⟨d, Or.inr hα⟩) hx₀ hc
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
      (((walkMap M wk).faceOf_eq_iff x₀ ⟨d, Or.inr hα⟩).mp hface)
    exact ⟨n, congrArg (fun z : (walkMap M wk).Dart => z.1) hn⟩

theorem walkKeep_of_walkKeep_lakeWalk (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) {y : M.Dart}
    (h : walkKeep M (lakeWalk M wk x₀) y) : walkKeep M wk y := by
  rcases h with hy | hy
  · exact Or.inr ((mem_lakeWalk_iff hw hM hout hx₀ y).mp hy).1
  · have h2 := ((mem_lakeWalk_iff hw hM hout hx₀ _).mp hy).1
    rw [M.alpha_involutive y] at h2
    exact Or.inl h2

/-- Along a face-chain of darts on walk edges, the restricted face permutation follows the
chain. -/
theorem walkMap_facePerm_pow_getElem {l : List M.Dart}
    (hc : l.IsChain fun d e => M.facePerm d = e) (hkeep : ∀ d ∈ l, walkKeep M wk d)
    {x₀ : (walkMap M wk).Dart} (h0 : 0 < l.length) (hx₀ : x₀.1 = l[0]'h0) :
    ∀ (n : ℕ) (hn : n < l.length), (((walkMap M wk).facePerm ^ n) x₀).1 = l[n]'hn := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [pow_zero, Equiv.Perm.one_apply]
      exact hx₀
  | succ n ih =>
      intro hn
      have h1 : (((walkMap M wk).facePerm ^ n) x₀).1 = l[n] := ih (by omega)
      have hnext : M.facePerm l[n] = l[n + 1] := hc.getElem n hn
      have hk : walkKeep M wk (M.facePerm (((walkMap M wk).facePerm ^ n) x₀).1) := by
        rw [h1, hnext]
        exact hkeep _ (List.getElem_mem _)
      rw [pow_succ', Equiv.Perm.mul_apply, walkMap_facePerm_of_keep _ hk, h1, hnext]

theorem lakeWalk_ne_nil (x₀ : (walkMap M wk).Dart) : lakeWalk M wk x₀ ≠ [] :=
  List.ne_nil_of_length_pos (by
    rw [length_lakeWalk]
    exact (period_spec _ _).1)

theorem lakeWalk_nodup (x₀ : (walkMap M wk).Dart) : (lakeWalk M wk x₀).Nodup :=
  nodup_orbitMap (walkMap M wk).facePerm x₀ (f := fun d : (walkMap M wk).Dart => d.1)
    (fun _ _ h => Subtype.ext h)

theorem lakeWalk_step (x₀ : (walkMap M wk).Dart) (n : ℕ) :
    M.vertexOf (M.alpha (((walkMap M wk).facePerm ^ n) x₀).1) =
      M.vertexOf (((walkMap M wk).facePerm ^ (n + 1)) x₀).1 := by
  rw [pow_succ', Equiv.Perm.mul_apply]
  exact vertexOf_walkMap_facePerm _

theorem lakeWalk_chain (x₀ : (walkMap M wk).Dart) :
    (lakeWalk M wk x₀).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
  orbitMap_isChain (walkMap M wk).facePerm x₀ (fun d : (walkMap M wk).Dart => d.1)
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (lakeWalk_step x₀)

theorem lakeWalk_closes (x₀ : (walkMap M wk).Dart) (hne : lakeWalk M wk x₀ ≠ []) :
    M.vertexOf (M.alpha ((lakeWalk M wk x₀).getLast hne)) =
      M.vertexOf ((lakeWalk M wk x₀).head hne) :=
  orbitMap_closes (walkMap M wk).facePerm x₀ (fun d : (walkMap M wk).Dart => d.1)
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (lakeWalk_step x₀) hne

/-- The membership clause of an enclosed face set, for the filled side. -/
theorem lakeWalk_mem_iff (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) (d : M.Dart) :
    d ∈ lakeWalk M wk x₀ ↔ M.faceOf d ∉ absorbed M (sideFaces M wk) o ∧
      (M.faceOf (M.alpha d) ∈ absorbed M (sideFaces M wk) o ∨
        M.alpha d ∈ lakeWalk M wk x₀) := by
  rw [mem_lakeWalk_iff hw hM hout hx₀, mem_lakeWalk_iff hw hM hout hx₀, mem_absorbed_iff,
    mem_absorbed_iff, not_not, M.alpha_involutive d]
  constructor
  · rintro ⟨hα, hc⟩
    exact ⟨hc, Or.inl (faceOf_not_mem_component hw hM hout hα)⟩
  · rintro ⟨hc, hor⟩
    rcases hor with hα | ⟨hd, _⟩
    · exact ⟨alpha_mem_of_mem_component hw hM hout hc hα, hc⟩
    · exact absurd hc (faceOf_not_mem_component hw hM hout hd)

/-- **Turn to the successor** on the outer walk of the filled side. -/
theorem lakeWalk_turn_next (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) (i : ℕ)
    (hi : i < (lakeWalk M wk x₀).length) (m : ℕ) (hm : 0 < m)
    (hkeep : walkKeep M (lakeWalk M wk x₀) ((M.sigma ^ m) (M.alpha (lakeWalk M wk x₀)[i])))
    (hfirst : ∀ k, 0 < k → k < m →
      ¬ walkKeep M (lakeWalk M wk x₀) ((M.sigma ^ k) (M.alpha (lakeWalk M wk x₀)[i]))) :
    (M.sigma ^ m) (M.alpha (lakeWalk M wk x₀)[i]) =
      (lakeWalk M wk x₀)[(i + 1) % (lakeWalk M wk x₀).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  rw [lakeWalk_getElem_succ_mod x₀ i hi]
  rw [getElem_lakeWalk x₀ i hi] at hkeep hfirst ⊢
  obtain ⟨m₀, hm₀, hpm, havoid⟩ :=
    walkMap_facePerm_firstReturn (((walkMap M wk).facePerm ^ i) x₀)
  rw [hpm]
  rcases lt_trichotomy m m₀ with hlt | heq | hgt
  · exact absurd (walkKeep_of_walkKeep_lakeWalk hw hM hout hx₀ hkeep) (havoid m hm hlt)
  · rw [heq]
  · refine absurd ?_ (hfirst m₀ hm₀ hgt)
    rw [← hpm]
    exact Or.inl ((mem_orbitMap_iff (walkMap M wk).facePerm x₀
      (fun d : (walkMap M wk).Dart => d.1) _).mpr
      ⟨i + 1, by rw [pow_succ', Equiv.Perm.mul_apply]⟩)

theorem lakeWalk_turn_mem (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) :
    ∀ d ∈ lakeWalk M wk x₀, ∀ m : ℕ, 0 < m →
      walkKeep M (lakeWalk M wk x₀) ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M (lakeWalk M wk x₀) ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ lakeWalk M wk x₀ := by
  intro d hd m hm hkeep hfirst
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [lakeWalk_turn_next hw hM hout hx₀ i hi m hm hkeep hfirst]
  exact List.getElem_mem _

end Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The filled side is an enclosed face set turning to successors**, over the outer walk
`lakeWalk` started at a walk-edge dart facing the exterior piece. -/
theorem lakeWalk_enclosedFaceSetSucc (X : DiscDiagram.{u, w, v} W)
    {wk : List X.toCombMap.Dart} (hw : IsNoncrossingClosedWalk X.toCombMap wk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap wk) {x₀ : (walkMap X.toCombMap wk).Dart}
    (hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace) :
    EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap wk) X.outerFace)
      (lakeWalk X.toCombMap wk x₀) :=
  { outerFace_not_mem := fun h => mem_absorbed_iff.mp h (self_mem_component _)
    ne_nil := lakeWalk_ne_nil x₀
    nodup := lakeWalk_nodup x₀
    chain := lakeWalk_chain x₀
    closes := lakeWalk_closes x₀ _
    mem_iff := lakeWalk_mem_iff hw X.planar hout hx₀
    turn_mem := lakeWalk_turn_mem hw X.planar hout hx₀
    turn_next := lakeWalk_turn_next hw X.planar hout hx₀ }

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.exists_pow_apply_eq_self
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.period
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.period_spec
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.period_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.pow_period_mul_apply
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.pow_mod_period
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.pow_apply_inj
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.orbitMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.length_orbitMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.getElem_orbitMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.mem_orbitMap_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.nodup_orbitMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.orbitMap_getElem_succ_mod
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.orbitMap_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.orbitMap_closes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.length_lakeWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.getElem_lakeWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_getElem_succ_mod
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_facePerm_pow_exterior
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.alpha_mem_of_exterior
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.mem_lakeWalk_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkKeep_of_walkKeep_lakeWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.walkMap_facePerm_pow_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_chain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_closes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_turn_next
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_turn_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeWalk_enclosedFaceSetSucc
