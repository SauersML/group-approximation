import GroupApproximation.GGT.VanKampen.CombMapRestrictionComponentFaceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Holding small faces of the contact map: face-class tools

Leaf `OsinLemma94ContactMapHoldingSmallFacesInput` of the Greendlinger least-area leaf (Hull
Thm 7.1, through the contact count of Osin's Lemma 9.4, arXiv:math/0411039v3, §9): the
nondegenerate small faces of `contactMap P` that hold an object number at most `K n`.

## The full proof (a nesting charge over the components)

Write `M` for the dual of the diagram (planar, `dual_planar_diagram`), `keep` for
`P.ContactKeep` and `N = contactMap P`, the predicate restriction of `M` to `keep`.  The vertices
of `M` are the faces of the diagram, the objects `o` (relator cells and the exterior `r = none`)
among them.  For `K : M.Dart → Prop`, `∼_K` is the face class relation
`EqvGen (FaceClassStep M K)`: advance around a face of `M`, or cross an edge off `K`.

For a contact dart `x` let `K_x z := ∃ h : keep z, N.componentOf x ⟨z, h⟩` (`CompKeep`): the
darts of the component of `x`.  We bound *all* holding faces, with `K = 4`, `ε₀ = 0`, `ρ₀ = 1`.

**Tools (this module, any map `M`).**
* Monotonicity: a `∼_K` path is a `∼_{K'}` path when `K' ⊆ K` (`faceClass_mono`).
* A vertex sweep: `d ∼_K σ d` when `¬ K d` (via `d → α d → φ (α d) = σ d`), so if the whole
  vertex orbit of `y` avoids `K`, all darts of that orbit are `∼_K`-joined (`faceClass_of_sameCycle`);
  if the orbit meets `K`, its first `K` dart after `y` is joined to `y` (`exists_keep_faceClass`).
* Transfer: a `∼_{K₁}` class carrying no `K₂` dart is contained in a `∼_{K₂}` class
  (`faceClass_transfer`).
* Reach: if `K` is `α`-invariant, `M` is connected and `K` is inhabited, every dart is `∼_K`-joined
  to some `K` dart (`exists_keep_of_connected`): the property is invariant under `α` and `σ`.

**Components (`ComponentClasses`).**
* Separation inside a component: `x ∼_{K_x} x'` with `x'` in the component of `x` gives
  `faceOf x = faceOf x'` (`faceOf_eq_of_compKeep`, from `IsRestriction.faceOf_eq_of_faceClass`
  applied to the component, as in `faceOf_eq_of_faceClass_of_componentOf`).
* Blocks: if no dart of the component of `x₁` has a `K₂` dart at its vertex, all darts of that
  component lie in one `∼_{K₂}` class (`faceClass_of_componentOf`, induction on adjacency: `α`
  steps cross edges off `K₂`, `σ` steps are vertex sweeps).  This holds when `x₂` is off the
  component of `x₁`, since the kept darts at one vertex of `M` form one vertex of `N`
  (`not_compKeep_of_componentOf`).

**Charge (`ContactCharge`).**  A face `F` of `N` *holds `o` via `x, y`*: `x ∈ F`, `x ∼_keep y`,
`y` at `o`, and no dart of `F` at `o`.  It is *outer* when some `x ∈ F` and `y` at `r` have
`x ∼_{K_x} y` and the vertex orbit of `y` carries no `K_x` dart.
1. *A holding face sees no dart of its component at `o`* (`not_compKeep_of_holds`): otherwise the
   first `K_x` dart after `y` at `o` is joined to `x` and separation puts it on `F`.
2. *Inner faces are charged injectively* (`holds_inj`).  Let `F₁, F₂` be non-outer and hold `o` via
   `x₁, y₁` and `x₂, y₂`.  The orbit of `o` avoids `K_{x₁}`, so `x₁ ∼ y₁ ∼ y₂ ∼ x₂` in `∼_{K_{x₁}}`,
   and symmetrically.  If `x₂` is in the component of `x₁`, separation gives `F₁ = F₂`.
   Otherwise (`false_of_not_componentOf`):
   * If some dart `w` of the component of `x₁` sits at `r`, then `x₂ ∼ x₁ ∼ w` in `∼_{K_{x₂}}` by
     the block of `x₁`, the orbit of `w` avoids `K_{x₂}`, and `F₂` is outer.  Symmetrically if the
     component of `x₂` meets `r`.
   * Otherwise take `y_r` at `r`, whose orbit avoids both.  Reach gives `w` in the component of `x₁`
     with `y_r ∼_{K_{x₁}} w`.  If the `∼_{K_{x₁}}` class of `y_r` had a `K_{x₂}` dart `z`, the block
     of `x₂` would give `x₁ ∼ x₂ ∼ z ∼ y_r` and `F₁` would be outer.  So transfer gives
     `y_r ∼_{K_{x₂}} w`, and the block of `x₁` gives `x₂ ∼ w ∼ y_r`: `F₂` is outer.
   So `F ↦ o` injects the held non-outer faces into `Option (Fin n)`: at most `n + 1`.
3. *Outer faces are charged injectively by an object vertex* (`outer_inj`).  Every face has a dart
   at an object (a dart of colour `false`, or `φ` of a dart of colour `true`), and two outer faces
   with a common object vertex share a component (the kept darts at one vertex of `M` form one
   vertex of `N`); their `r`-darts are swept together and separation identifies the faces.  At
   most `n + 1`.
4. *Endpoint* (`Proof`): the holding faces number at most `2 (n + 1) ≤ 4 n`, since `n ≥ 1`, and
   `n = Δ.rCellCount` by `S.equiv.rCellCount_eq`.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

universe u

/-! ## Equivalence closures along a permutation -/

theorem eqvGen_of_eq {α : Type*} {r : α → α → Prop} {a b : α} (h : a = b) :
    Relation.EqvGen r a b := by
  subst h
  exact Relation.EqvGen.refl _

/-- Steps along a permutation iterate. -/
theorem eqvGen_pow {α : Type*} {r : α → α → Prop} (f : Equiv.Perm α)
    (hf : ∀ d, Relation.EqvGen r d (f d)) (a : α) (i : ℕ) :
    Relation.EqvGen r a ((f ^ i) a) := by
  induction i with
  | zero => exact eqvGen_of_eq (by rw [pow_zero, Equiv.Perm.one_apply])
  | succ i ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.trans _ _ _ (hf ((f ^ i) a))
      (eqvGen_of_eq (by rw [pow_succ', Equiv.Perm.mul_apply])))

/-! ## Components of a map -/

theorem adjacent_facePerm (N : CombMap.{u}) (d : N.Dart) :
    Relation.EqvGen N.Adjacent d (N.facePerm d) :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel d (N.alpha d) (Or.inl rfl))
    (Relation.EqvGen.rel (N.alpha d) (N.facePerm d) (Or.inr rfl))

/-- Darts at one vertex lie in one component. -/
theorem componentOf_of_sameCycle (N : CombMap.{u}) {a b : N.Dart}
    (h : N.sigma.SameCycle a b) : N.componentOf a b := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact eqvGen_pow N.sigma (fun d => Relation.EqvGen.rel d (N.sigma d) (Or.inr rfl)) a i

/-- Darts on one face lie in one component. -/
theorem componentOf_of_faceOf_eq (N : CombMap.{u}) {a b : N.Dart}
    (h : N.faceOf a = N.faceOf b) : N.componentOf a b := by
  obtain ⟨i, rfl⟩ := ((N.faceOf_eq_iff a b).mp h).exists_nat_pow_eq
  exact eqvGen_pow N.facePerm (adjacent_facePerm N) a i

/-! ## Face classes of an arbitrary dart set -/

section FaceClass

variable {M : CombMap.{u}}

/-- A face class off a larger set is a face class off a smaller set. -/
theorem faceClass_mono {K K' : M.Dart → Prop} (hK : ∀ z, K' z → K z) {a b : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M K) a b) :
    Relation.EqvGen (CombMap.FaceClassStep M K') a b := by
  have hmono : CombMap.FaceClassStep M K ≤ CombMap.FaceClassStep M K' := by
    intro x y hxy
    rcases hxy with h1 | ⟨hnk, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨fun hk => hnk (hK x hk), h1⟩
  exact Relation.EqvGen.mono hmono _ _ h

theorem faceClass_facePerm {K : M.Dart → Prop} (d : M.Dart) :
    Relation.EqvGen (CombMap.FaceClassStep M K) d (M.facePerm d) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

theorem faceClass_alpha {K : M.Dart → Prop} {d : M.Dart} (hd : ¬ K d) :
    Relation.EqvGen (CombMap.FaceClassStep M K) d (M.alpha d) :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨hd, rfl⟩)

theorem facePerm_alpha (M : CombMap.{u}) (d : M.Dart) : M.facePerm (M.alpha d) = M.sigma d := by
  show M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive d]

/-- Rotating at a vertex off the set stays in the face class. -/
theorem faceClass_sigma {K : M.Dart → Prop} {d : M.Dart} (hd : ¬ K d) :
    Relation.EqvGen (CombMap.FaceClassStep M K) d (M.sigma d) :=
  Relation.EqvGen.trans _ _ _ (faceClass_alpha hd)
    (Relation.EqvGen.trans _ _ _ (faceClass_facePerm (M.alpha d))
      (eqvGen_of_eq (facePerm_alpha M d)))

/-- Sweeping around a vertex through darts off the set. -/
theorem faceClass_pow {K : M.Dart → Prop} (y : M.Dart) (i : ℕ)
    (h : ∀ j < i, ¬ K ((M.sigma ^ j) y)) :
    Relation.EqvGen (CombMap.FaceClassStep M K) y ((M.sigma ^ i) y) := by
  induction i with
  | zero => exact eqvGen_of_eq (by rw [pow_zero, Equiv.Perm.one_apply])
  | succ i ih =>
    exact Relation.EqvGen.trans _ _ _ (ih fun j hj => h j (by omega))
      (Relation.EqvGen.trans _ _ _ (faceClass_sigma (h i (by omega)))
        (eqvGen_of_eq (by rw [pow_succ', Equiv.Perm.mul_apply])))

/-- **A vertex off the set lies in one face class.** -/
theorem faceClass_of_sameCycle {K : M.Dart → Prop} {y y' : M.Dart}
    (hy : ∀ z, M.sigma.SameCycle y z → ¬ K z) (h : M.sigma.SameCycle y y') :
    Relation.EqvGen (CombMap.FaceClassStep M K) y y' := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact faceClass_pow y i fun j _ => hy _ ⟨(j : ℤ), by rw [zpow_natCast]⟩

/-- **The first dart of the set at a vertex is in the face class of the vertex.** -/
theorem exists_keep_faceClass {K : M.Dart → Prop} {y z : M.Dart} (h : M.sigma.SameCycle y z)
    (hz : K z) :
    ∃ z', K z' ∧ M.sigma.SameCycle y z' ∧ Relation.EqvGen (CombMap.FaceClassStep M K) y z' := by
  classical
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  have hex : ∃ n : ℕ, K ((M.sigma ^ n) y) := ⟨i, hz⟩
  refine ⟨(M.sigma ^ Nat.find hex) y, Nat.find_spec hex,
    ⟨((Nat.find hex : ℕ) : ℤ), by rw [zpow_natCast]⟩, ?_⟩
  exact faceClass_pow y _ fun j hj => Nat.find_min hex hj

/-- **Transfer**: a face class off `K₁` carrying no dart of `K₂` lies in a face class off `K₂`. -/
theorem faceClass_transfer {K₁ K₂ : M.Dart → Prop} {a₀ : M.Dart}
    (hno : ∀ z, Relation.EqvGen (CombMap.FaceClassStep M K₁) a₀ z → ¬ K₂ z) {a b : M.Dart}
    (hab : Relation.EqvGen (CombMap.FaceClassStep M K₁) a b)
    (ha : Relation.EqvGen (CombMap.FaceClassStep M K₁) a₀ a) :
    Relation.EqvGen (CombMap.FaceClassStep M K₂) a b := by
  induction hab with
  | rel x y hxy =>
    rcases hxy with h1 | ⟨_, h1⟩
    · exact Relation.EqvGen.rel _ _ (Or.inl h1)
    · exact Relation.EqvGen.rel _ _ (Or.inr ⟨hno x ha, h1⟩)
  | refl x => exact Relation.EqvGen.refl x
  | symm x y hxy ih =>
    exact Relation.EqvGen.symm _ _
      (ih (Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.symm _ _ hxy)))
  | trans x y z hxy _ ih₁ ih₂ =>
    exact Relation.EqvGen.trans _ _ _ (ih₁ ha) (ih₂ (Relation.EqvGen.trans _ _ _ ha hxy))

theorem reach_congr {K : M.Dart → Prop} {d d' : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M K) d d') :
    (∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) d w) ↔
      ∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) d' w :=
  ⟨fun ⟨w, hw, hp⟩ => ⟨w, hw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hp⟩,
    fun ⟨w, hw, hp⟩ => ⟨w, hw, Relation.EqvGen.trans _ _ _ h hp⟩⟩

theorem reach_alpha {K : M.Dart → Prop} (hKα : ∀ z, K (M.alpha z) ↔ K z) (d : M.Dart) :
    (∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) d w) ↔
      ∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) (M.alpha d) w := by
  by_cases hd : K d
  · exact ⟨fun _ => ⟨M.alpha d, (hKα d).mpr hd, Relation.EqvGen.refl _⟩,
      fun _ => ⟨d, hd, Relation.EqvGen.refl _⟩⟩
  · exact reach_congr (faceClass_alpha hd)

theorem reach_sigma {K : M.Dart → Prop} (hKα : ∀ z, K (M.alpha z) ↔ K z) (d : M.Dart) :
    (∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) d w) ↔
      ∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) (M.sigma d) w :=
  (reach_alpha hKα d).trans (reach_congr (Relation.EqvGen.trans _ _ _
    (faceClass_facePerm (M.alpha d)) (eqvGen_of_eq (facePerm_alpha M d))))

/-- **Reach**: in a connected map, every dart is in the face class of a dart of an inhabited
`α`-invariant set. -/
theorem exists_keep_of_connected {K : M.Dart → Prop} (hKα : ∀ z, K (M.alpha z) ↔ K z)
    (hM : M.IsConnected) {w₀ : M.Dart} (hw₀ : K w₀) (d : M.Dart) :
    ∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) d w := by
  have hall : ∀ a b, Relation.EqvGen M.Adjacent a b →
      ((∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) a w) ↔
        ∃ w, K w ∧ Relation.EqvGen (CombMap.FaceClassStep M K) b w) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      rcases hxy with rfl | rfl
      · exact reach_alpha hKα x
      · exact reach_sigma hKα x
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hall w₀ d (hM w₀ d)).mp ⟨w₀, hw₀, Relation.EqvGen.refl _⟩

end FaceClass

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.exists_keep_of_connected
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.faceClass_transfer
