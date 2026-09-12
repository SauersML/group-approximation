import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.Meta.AxiomGuard

/-!
# Deleting a spike from a planar map

A dart `a` fixed by the vertex rotation is the tip of a spike: its vertex has
degree one.  Deleting that edge keeps every other dart in its old rotation
order, except that the dart pointing into the deleted edge now skips it
(`EdgeDeletion.value_sigma_of_fixed`), and the remainder stays connected
whenever some dart survives (`EdgeDeletion.connected_of_sigma_fixed`).

A planar map with a single face always has such a tip
(`CombMap.exists_sigma_eq_self_of_planar_faceCount_eq_one`: with one face,
Euler gives `V = E + 1`, so the degree sum `2E` forces a vertex of degree one),
and deleting it leaves a planar map with a single face
(`EdgeDeletion.faceCount_eq_one_of_sigma_fixed`).

These are the map-level steps of the tree case of the easy van Kampen lemma
(the boundary word of a one-face planar map is freely trivial) and of the spike
case of cactus folding.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv PermOrbitErasePoint

universe u

namespace CombMap

variable (M : CombMap.{u})

/-- Every vertex carries a dart. -/
theorem one_le_vertexDegree (v : M.Vertex) : 1 ≤ M.vertexDegree v := by
  classical
  obtain ⟨d, hd⟩ := Quotient.exists_rep v
  haveI : Nonempty {x : M.Dart // (Quotient.mk'' x : Orbit M.sigma) = v} := ⟨⟨d, hd⟩⟩
  have hpos : 0 < Nat.card {x : M.Dart // (Quotient.mk'' x : Orbit M.sigma) = v} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  exact hpos

/-- A dart whose vertex has degree one is fixed by the vertex rotation. -/
theorem sigma_eq_self_of_vertexDegree_eq_one {d : M.Dart}
    (hv : M.vertexDegree (M.vertexOf d) = 1) : M.sigma d = d := by
  have hv' : Nat.card {x : M.Dart //
      (Quotient.mk'' x : Orbit M.sigma) = M.vertexOf d} = 1 := hv
  have hsub := (Nat.card_eq_one_iff_unique.mp hv').1
  have h := hsub.elim ⟨M.sigma d, M.vertexOf_sigma d⟩ ⟨d, rfl⟩
  exact congrArg Subtype.val h

/-- **A planar map with a single face has a dart fixed by the vertex
rotation.**  Euler gives `V = E + 1`; if every vertex had degree at least two,
the degree sum `2E` would be at least `2V`. -/
theorem exists_sigma_eq_self_of_planar_faceCount_eq_one (hM : M.IsPlanar)
    (hF : M.faceCount = 1) : ∃ d : M.Dart, M.sigma d = d := by
  classical
  have heuler := M.euler_eq_two hM
  rw [hF] at heuler
  push_cast at heuler
  have hVE : M.vertexCount = M.edgeCount + 1 := by omega
  by_contra hno
  have hdeg : ∀ v : M.Vertex, 2 ≤ M.vertexDegree v := by
    intro v
    obtain ⟨d, hd⟩ := Quotient.exists_rep v
    have hv : M.vertexOf d = v := hd
    rw [← hv]
    by_contra hlt
    have h1 : M.vertexDegree (M.vertexOf d) = 1 :=
      le_antisymm (by omega) (M.one_le_vertexDegree _)
    exact hno ⟨d, M.sigma_eq_self_of_vertexDegree_eq_one h1⟩
  have hsum := M.sum_vertexDegree_eq_two_mul_edgeCount
  have hge : ∑ _v : M.Vertex, 2 ≤ ∑ v : M.Vertex, M.vertexDegree v :=
    Finset.sum_le_sum fun v _ => hdeg v
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hsum] at hge
  have hcard : M.vertexCount = Fintype.card M.Vertex := Nat.card_eq_fintype_card
  omega

end CombMap

namespace EdgeDeletion

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- Erasing a fixed dart does not change the rotation of the other darts. -/
theorem erase_sigma_val_of_fixed (ha : M.sigma a = a) (x : FirstDart M a) :
    (erase M.sigma a x).1 = M.sigma x.1 := by
  rw [erase_val, isolate, Perm.mul_apply, ha, Equiv.swap_self, Equiv.refl_apply]

/-- **Vertex rotation after deleting a spike.**  Every surviving dart rotates as
before, except the dart that pointed at the reverse of the deleted tip, which
now skips it. -/
theorem value_sigma_of_fixed (ha : M.sigma a = a) (d : Dart M a) :
    value M a ((toCombMap M a).sigma d) =
      if M.sigma (value M a d) = M.alpha a then M.sigma (M.alpha a)
      else M.sigma (value M a d) := by
  change (erase (erase M.sigma a) (reverseDart M a) d).1.1 = _
  rw [erase_val, isolate, Perm.mul_apply, Equiv.swap_apply_def]
  have hd1 : ((erase M.sigma a) d.1).1 = M.sigma (value M a d) :=
    erase_sigma_val_of_fixed M a ha d.1
  have hrd : ((erase M.sigma a) (reverseDart M a)).1 = M.sigma (M.alpha a) :=
    erase_sigma_val_of_fixed M a ha (reverseDart M a)
  by_cases h1 : (erase M.sigma a) d.1 = reverseDart M a
  · rw [if_pos h1, hrd]
    have hval : M.sigma (value M a d) = M.alpha a := by
      rw [← hd1, h1]
      rfl
    rw [if_pos hval]
  · rw [if_neg h1]
    have hne2 : (erase M.sigma a) d.1 ≠ (erase M.sigma a) (reverseDart M a) := by
      intro h
      exact d.2 ((erase M.sigma a).injective h)
    rw [if_neg hne2, hd1]
    have hval : M.sigma (value M a d) ≠ M.alpha a := by
      intro h
      apply h1
      apply Subtype.ext
      rw [hd1]
      exact h
    rw [if_neg hval]

omit [DecidableEq M.Dart] in
/-- The reverse of a spike tip is not fixed as soon as some dart survives. -/
theorem sigma_alpha_ne_alpha_of_fixed (hM : M.IsConnected) (ha : M.sigma a = a)
    (d₀ : Dart M a) : M.sigma (M.alpha a) ≠ M.alpha a :=
  fun hb => not_both_fixed M a hM d₀ ⟨ha, hb⟩

omit [DecidableEq M.Dart] in
/-- The rotation successor of the reverse of a spike tip is not the tip. -/
theorem sigma_alpha_ne_of_fixed (ha : M.sigma a = a) : M.sigma (M.alpha a) ≠ a := by
  intro h
  exact M.alpha_fixedPointFree a (M.sigma.injective (h.trans ha.symm))

omit [DecidableEq M.Dart] in
/-- The surviving dart next to the deleted edge. -/
def spikeAnchor (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a) : Dart M a :=
  ⟨⟨M.sigma (M.alpha a), sigma_alpha_ne_of_fixed M a ha⟩, fun h =>
    sigma_alpha_ne_alpha_of_fixed M a hM ha d₀ (congrArg Subtype.val h)⟩

/-- Project the old darts onto the surviving ones: surviving darts stay put and
the two deleted darts go to the anchor. -/
def project (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a)
    (x : M.Dart) : Dart M a :=
  if h : x ≠ a ∧ x ≠ M.alpha a then ⟨⟨x, h.1⟩, fun h' => h.2 (congrArg Subtype.val h')⟩
  else spikeAnchor M a hM ha d₀

theorem project_value (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a)
    (d : Dart M a) : project M a hM ha d₀ (value M a d) = d := by
  unfold project
  rw [dif_pos ⟨value_ne M a d, value_ne_reverse M a d⟩]
  exact Subtype.ext (Subtype.ext rfl)

theorem project_of_ne (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a)
    {x : M.Dart} (h1 : x ≠ a) (h2 : x ≠ M.alpha a) :
    project M a hM ha d₀ x = ⟨⟨x, h1⟩, fun h' => h2 (congrArg Subtype.val h')⟩ := by
  unfold project
  rw [dif_pos ⟨h1, h2⟩]

theorem project_tip (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a) :
    project M a hM ha d₀ a = spikeAnchor M a hM ha d₀ := by
  unfold project
  rw [dif_neg (fun h => h.1 rfl)]

theorem project_reverse (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a) :
    project M a hM ha d₀ (M.alpha a) = spikeAnchor M a hM ha d₀ := by
  unfold project
  rw [dif_neg (fun h => h.2 rfl)]

/-- One elementary move of the old map projects to at most one elementary move of
the new map. -/
theorem project_adjacent (hM : M.IsConnected) (ha : M.sigma a = a) (d₀ : Dart M a)
    (x y : M.Dart) (hxy : M.Adjacent x y) :
    Relation.EqvGen (toCombMap M a).Adjacent
      (project M a hM ha d₀ x) (project M a hM ha d₀ y) := by
  by_cases hxa : x = a
  · subst hxa
    rcases hxy with hy | hy
    · rw [← hy, project_tip, project_reverse]
      exact Relation.EqvGen.refl _
    · rw [← hy, ha]
      exact Relation.EqvGen.refl _
  by_cases hxb : x = M.alpha a
  · subst hxb
    rcases hxy with hy | hy
    · rw [← hy, M.alpha_involutive, project_tip, project_reverse]
      exact Relation.EqvGen.refl _
    · rw [← hy, project_reverse,
        project_of_ne M a hM ha d₀ (sigma_alpha_ne_of_fixed M a ha)
          (sigma_alpha_ne_alpha_of_fixed M a hM ha d₀)]
      exact Relation.EqvGen.refl _
  rw [project_of_ne M a hM ha d₀ hxa hxb]
  rcases hxy with hy | hy
  · have hy1 : y ≠ a := by
      intro h
      apply hxb
      have h' := congrArg M.alpha (hy.trans h)
      rwa [M.alpha_involutive] at h'
    have hy2 : y ≠ M.alpha a := by
      intro h
      apply hxa
      have h' := congrArg M.alpha (hy.trans h)
      rwa [M.alpha_involutive, M.alpha_involutive] at h'
    rw [project_of_ne M a hM ha d₀ hy1 hy2]
    apply Relation.EqvGen.rel
    left
    apply Subtype.ext
    apply Subtype.ext
    exact (alpha_val M a _).trans hy
  · by_cases hyb : M.sigma x = M.alpha a
    · have hyeq : y = M.alpha a := hy.symm.trans hyb
      rw [hyeq, project_reverse]
      apply Relation.EqvGen.rel
      right
      apply Subtype.ext
      apply Subtype.ext
      have hv : value M a ((toCombMap M a).sigma
          ⟨⟨x, hxa⟩, fun h' => hxb (congrArg Subtype.val h')⟩) =
          if M.sigma x = M.alpha a then M.sigma (M.alpha a) else M.sigma x :=
        value_sigma_of_fixed M a ha ⟨⟨x, hxa⟩, fun h' => hxb (congrArg Subtype.val h')⟩
      rw [if_pos hyb] at hv
      exact hv
    · have hy1 : y ≠ a := by
        intro h
        apply hxa
        exact M.sigma.injective ((hy.trans h).trans ha.symm)
      have hy2 : y ≠ M.alpha a := fun h => hyb (hy.trans h)
      rw [project_of_ne M a hM ha d₀ hy1 hy2]
      apply Relation.EqvGen.rel
      right
      apply Subtype.ext
      apply Subtype.ext
      have hv : value M a ((toCombMap M a).sigma
          ⟨⟨x, hxa⟩, fun h' => hxb (congrArg Subtype.val h')⟩) =
          if M.sigma x = M.alpha a then M.sigma (M.alpha a) else M.sigma x :=
        value_sigma_of_fixed M a ha ⟨⟨x, hxa⟩, fun h' => hxb (congrArg Subtype.val h')⟩
      rw [if_neg hyb] at hv
      exact hv.trans hy

/-- **Deleting a spike keeps the map connected**, provided some dart survives. -/
theorem connected_of_sigma_fixed (hM : M.IsConnected) (ha : M.sigma a = a)
    (d₀ : Dart M a) : (toCombMap M a).IsConnected := by
  intro d e
  have hlift : ∀ x y : M.Dart, Relation.EqvGen M.Adjacent x y →
      Relation.EqvGen (toCombMap M a).Adjacent
        (project M a hM ha d₀ x) (project M a hM ha d₀ y) := by
    intro x y h
    induction h with
    | rel x y h => exact project_adjacent M a hM ha d₀ x y h
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have h := hlift (value M a d) (value M a e) (hM _ _)
  rwa [project_value, project_value] at h

/-- **Deleting a spike from a planar map leaves a planar map**, provided some
dart survives. -/
theorem planar_of_sigma_fixed (hM : M.IsPlanar) (ha : M.sigma a = a)
    (d₀ : Dart M a) : (toCombMap M a).IsPlanar :=
  planar_of_connected M a hM d₀ (connected_of_sigma_fixed M a hM.1 ha d₀)

/-- **Deleting a spike from a planar map with one face leaves one face.** -/
theorem faceCount_eq_one_of_sigma_fixed (hM : M.IsPlanar) (hF : M.faceCount = 1)
    (ha : M.sigma a = a) (d₀ : Dart M a) : (toCombMap M a).faceCount = 1 := by
  have hN := planar_of_sigma_fixed M a hM ha d₀
  have hface : M.faceOf a = M.faceOf (M.alpha a) := by
    have hsub : Subsingleton M.Face := (Nat.card_eq_one_iff_unique.mp hF).1
    exact Subsingleton.elim _ _
  have hbal := faceCount_balance_of_sameFace M a hface
  have hedge := edgeCount_add_one M a
  have hE := M.euler_eq_two hM
  have hEN := (toCombMap M a).euler_eq_two hN
  rw [hF] at hE hbal
  push_cast at hE
  omega

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.one_le_vertexDegree
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.sigma_eq_self_of_vertexDegree_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.exists_sigma_eq_self_of_planar_faceCount_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_sigma_of_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.connected_of_sigma_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.planar_of_sigma_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.faceCount_eq_one_of_sigma_fixed
