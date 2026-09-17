import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Direct limits of residually finite (or MF) groups are MF

Manuscript `non_mf_groups_exist.tex`, discussion after `thm:amenable-trace`
(tex lines 284--288): "Since `W_0` is a direct limit of residually finite
groups, it is MF [Korchagin, Corollary 10 and Proposition 13]."

This file proves the two cited facts in the generality of arbitrary directed
colimits of groups, **without** assuming the connecting maps are injective:

* `isLEF_of_isDirectedColimit`, `isOperatorMF_of_isDirectedColimit`: a
  countable direct limit of residually finite groups is LEF, hence MF;
* `isNormApproximable_of_isDirectedColimit`,
  `isOperatorMF_of_isDirectedColimit_operatorMF` (Korchagin, Proposition 13):
  a countable direct limit of MF groups is MF.

A directed colimit is described elementwise (`IsDirectedColimit`): compatible
cocone maps `φ i : A i →* G` that are jointly surjective and whose kernels are
eventually killed by the connecting maps.  The Mathlib direct limit
`DirectLimit A f` is such a colimit (`isDirectedColimit_directLimit`).

The key step is `exists_stage_multiplicative`: every finite subset of the limit
lifts to a single stage by a map that is multiplicative on that subset.
-/

namespace GroupApproximation.Full.NM09

open GroupApproximation

section Colimit

variable {ι : Type*} [Preorder ι] {A : ι → Type*} [∀ i, Group (A i)]
  {G : Type*} [Group G]

/-- Elementwise description of a directed colimit of groups: `φ` is a cocone
over the directed system `f` which is jointly surjective, and an element of a
stage dies in the colimit only if it dies at a later stage. -/
structure IsDirectedColimit (f : ∀ i j, i ≤ j → A i →* A j) (φ : ∀ i, A i →* G) :
    Prop where
  map_map : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x
  compat : ∀ {i j : ι} (h : i ≤ j) (x : A i), φ j (f i j h x) = φ i x
  surj : ∀ g : G, ∃ i, ∃ x : A i, φ i x = g
  eventually_one : ∀ {i : ι} (x : A i), φ i x = 1 → ∃ j, ∃ h : i ≤ j, f i j h x = 1

variable [IsDirectedOrder ι] {f : ∀ i j, i ≤ j → A i →* A j} {φ : ∀ i, A i →* G}

/-- A finite subset of the colimit lifts to a single stage. -/
theorem exists_stage_lift [Nonempty ι] (hC : IsDirectedColimit f φ) (s : Finset G) :
    ∃ (k : ι) (ℓ : G → A k), ∀ g ∈ s, φ k (ℓ g) = g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Classical.arbitrary ι, fun _ => 1, fun g hg => absurd hg (Finset.notMem_empty g)⟩
  | insert a s _ ih =>
    obtain ⟨i, ℓ, hℓ⟩ := ih
    obtain ⟨j, x, hx⟩ := hC.surj a
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, fun g => if g = a then f j k hjk x else f i k hik (ℓ g), fun g hg => ?_⟩
    show φ k (if g = a then f j k hjk x else f i k hik (ℓ g)) = g
    by_cases hga : g = a
    · rw [if_pos hga, hC.compat, hx, hga]
    · rw [if_neg hga, hC.compat, hℓ g ((Finset.mem_insert.mp hg).resolve_left hga)]

/-- Finitely many elements of a stage that die in the colimit die together at
one later stage. -/
theorem exists_stage_kill (hC : IsDirectedColimit f φ) {k : ι} :
    ∀ t : Finset (A k), (∀ y ∈ t, φ k y = 1) →
      ∃ j, ∃ h : k ≤ j, ∀ y ∈ t, f k j h y = 1 := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => exact fun _ => ⟨k, le_rfl, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert a t _ ih =>
    intro ht
    obtain ⟨j, hkj, hj⟩ := ih fun y hy => ht y (Finset.mem_insert_of_mem hy)
    obtain ⟨j', hkj', hj'⟩ := hC.eventually_one a (ht a (Finset.mem_insert_self a t))
    obtain ⟨l, hjl, hj'l⟩ := exists_ge_ge j j'
    refine ⟨l, le_trans hkj hjl, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with hya | hyt
    · have e := hC.map_map hkj' hj'l a
      rw [hj', map_one] at e
      rw [hya]
      exact e.symm
    · have e := hC.map_map hkj hjl y
      rw [hj y hyt, map_one] at e
      exact e.symm

/-- **Finite lifting.**  Every finite subset `s` of the colimit lifts to one
stage by a map that is multiplicative on `s`. -/
theorem exists_stage_multiplicative [Nonempty ι] (hC : IsDirectedColimit f φ) (s : Finset G) :
    ∃ (j : ι) (m : G → A j), (∀ g ∈ s, φ j (m g) = g) ∧
      ∀ x ∈ s, ∀ y ∈ s, m (x * y) = m x * m y := by
  classical
  obtain ⟨k, ℓ, hℓ⟩ := exists_stage_lift hC (s ∪ (s ×ˢ s).image fun p => p.1 * p.2)
  have hs : ∀ x ∈ s, φ k (ℓ x) = x := fun x hx => hℓ x (Finset.mem_union_left _ hx)
  have hp : ∀ x ∈ s, ∀ y ∈ s, φ k (ℓ (x * y)) = x * y := fun x hx y hy =>
    hℓ (x * y) (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : G × G => p.1 * p.2) (Finset.mem_product.mpr ⟨hx, hy⟩)))
  obtain ⟨j, hkj, hj⟩ := exists_stage_kill hC
    ((s ×ˢ s).image fun p => ℓ p.1 * ℓ p.2 * (ℓ (p.1 * p.2))⁻¹) (by
      intro y hy
      obtain ⟨p, hps, hpy⟩ := Finset.mem_image.mp hy
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hps
      rw [← hpy]
      show φ k (ℓ p.1 * ℓ p.2 * (ℓ (p.1 * p.2))⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hs p.1 hp1, hs p.2 hp2, hp p.1 hp1 p.2 hp2,
        mul_inv_cancel])
  refine ⟨j, fun g => f k j hkj (ℓ g), fun g hg => ?_, fun x hx y hy => ?_⟩
  · show φ j (f k j hkj (ℓ g)) = g
    rw [hC.compat, hs g hg]
  · have e := hj (ℓ x * ℓ y * (ℓ (x * y))⁻¹)
      (Finset.mem_image_of_mem (fun p : G × G => ℓ p.1 * ℓ p.2 * (ℓ (p.1 * p.2))⁻¹)
        (Finset.mem_product.mpr ⟨hx, hy⟩))
    rw [map_mul, map_mul, map_inv, mul_inv_eq_one] at e
    show f k j hkj (ℓ (x * y)) = f k j hkj (ℓ x) * f k j hkj (ℓ y)
    exact e.symm

/-- A directed colimit of residually finite groups is LEF. -/
theorem isLEF_of_isDirectedColimit [Nonempty ι] (hC : IsDirectedColimit f φ)
    (hRF : ∀ i, Group.ResiduallyFinite (A i)) : IsLEF G := by
  classical
  intro s
  obtain ⟨j, m, hm, hmul⟩ := exists_stage_multiplicative hC (insert 1 s)
  have h1 : (1 : G) ∈ insert 1 s := Finset.mem_insert_self 1 s
  have hm1 : m 1 = 1 := by
    have e := hmul 1 h1 1 h1
    rw [mul_one] at e
    exact mul_eq_left.mp e.symm
  haveI := hRF j
  obtain ⟨n, ρ, hinj, hρ⟩ :=
    GroupApproximation.isLEF_of_residuallyFinite (G := A j) ((insert 1 s).image m)
  refine ⟨n, fun g => ρ (m g), ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ insert 1 s := Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)
    have hy' : y ∈ insert 1 s := Finset.mem_insert_of_mem (Finset.mem_coe.mp hy)
    have e : m x = m y :=
      hinj (Finset.mem_coe.mpr (Finset.mem_image_of_mem m hx'))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem m hy')) hxy
    calc x = φ j (m x) := (hm x hx').symm
      _ = φ j (m y) := by rw [e]
      _ = y := hm y hy'
  · refine ⟨?_, ?_⟩
    · show ρ (m 1) = 1
      rw [hm1]
      exact hρ.map_one
    · intro x hx y hy
      have hx' : x ∈ insert 1 s := Finset.mem_insert_of_mem hx
      have hy' : y ∈ insert 1 s := Finset.mem_insert_of_mem hy
      show ρ (m (x * y)) = ρ (m x) * ρ (m y)
      rw [hmul x hx' y hy']
      exact hρ.map_mul (m x) (Finset.mem_image_of_mem m hx') (m y)
        (Finset.mem_image_of_mem m hy')

/-- **Korchagin, Corollary 10 + Proposition 13, residually finite form**: a
countable directed colimit of residually finite groups is MF. -/
theorem isOperatorMF_of_isDirectedColimit [Nonempty ι] {G : Type*} [Group G] [Countable G]
    {φ : ∀ i, A i →* G} (hC : IsDirectedColimit f φ)
    (hRF : ∀ i, Group.ResiduallyFinite (A i)) : IsOperatorMF G :=
  GroupApproximation.isOperatorMF_of_isLEF (isLEF_of_isDirectedColimit hC hRF)

/-- Norm approximability at a fixed separation passes to directed colimits. -/
theorem isNormApproximable_of_isDirectedColimit [Nonempty ι] (hC : IsDirectedColimit f φ)
    {δ : ℝ} (hA : ∀ i, IsNormApproximable (A i) δ) : IsNormApproximable G δ := by
  classical
  intro F ε hε
  obtain ⟨j, m, hm, hmul⟩ := exists_stage_multiplicative hC F
  obtain ⟨M⟩ := hA j (F.image m) ε hε
  exact ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g => M.map (m g)
    isUnitary := fun g => M.isUnitary (m g)
    multiplicative := fun g hg h hh => by
      have e := M.multiplicative (m g) (Finset.mem_image_of_mem m hg) (m h)
        (Finset.mem_image_of_mem m hh)
      rw [← hmul g hg h hh] at e
      exact e
    separated := fun g hg h hh hne =>
      M.separated (m g) (Finset.mem_image_of_mem m hg) (m h) (Finset.mem_image_of_mem m hh)
        fun e => hne (calc g = φ j (m g) := (hm g hg).symm
          _ = φ j (m h) := by rw [e]
          _ = h := hm h hh) }⟩

/-- **Korchagin, Proposition 13**: a countable directed colimit of MF groups
is MF.  The stages need not be countable and the connecting maps need not be
injective. -/
theorem isOperatorMF_of_isDirectedColimit_operatorMF [Nonempty ι] {G : Type*} [Group G]
    [Countable G] {φ : ∀ i, A i →* G} (hC : IsDirectedColimit f φ)
    (hMF : ∀ i, IsOperatorMF (A i)) : IsOperatorMF G :=
  OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (isNormApproximable_of_isDirectedColimit hC fun i =>
      OperatorMFLocalNormalization.isNormApproximable_one (hMF i))

end Colimit

section MathlibDirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {A : ι → Type*} [∀ i, Group (A i)] (f : ∀ i j, i ≤ j → A i →* A j)
  [DirectedSystem A (f · · ·)]

/-- The canonical map from a stage to the Mathlib direct limit. -/
noncomputable def directLimitOf (i : ι) : A i →* DirectLimit A f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (DirectLimit.one_def (f := f) i).symm
  map_mul' x y := (DirectLimit.mul_def (f := f) i x y).symm

theorem directLimitOf_apply (i : ι) (x : A i) :
    directLimitOf f i x = (⟦⟨i, x⟩⟧ : DirectLimit A f) :=
  rfl

/-- The Mathlib direct limit of a directed system of groups is a directed
colimit in the sense of `IsDirectedColimit`. -/
theorem isDirectedColimit_directLimit : IsDirectedColimit f (directLimitOf f) where
  map_map hij hjk x := DirectedSystem.map_map' f hij hjk x
  compat h x := by
    rw [directLimitOf_apply, directLimitOf_apply]
    exact DirectLimit.mk_apply (f := f) _ _ x h
  surj g := by
    obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f g
    refine ⟨i, x, ?_⟩
    rw [directLimitOf_apply]
    exact hx.symm
  eventually_one x hx := by
    rw [directLimitOf_apply] at hx
    exact (DirectLimit.exists_eq_one (f := f) ⟨_, x⟩).mp hx

/-- A direct limit of countably many countable groups is countable. -/
theorem countable_directLimit [Countable ι] [∀ i, Countable (A i)] :
    Countable (DirectLimit A f) :=
  inferInstance

/-- A countable Mathlib direct limit of residually finite groups is MF. -/
theorem isOperatorMF_directLimit_of_residuallyFinite [Countable (DirectLimit A f)]
    (hRF : ∀ i, Group.ResiduallyFinite (A i)) : IsOperatorMF (DirectLimit A f) :=
  isOperatorMF_of_isDirectedColimit (isDirectedColimit_directLimit f) hRF

/-- A countable Mathlib direct limit of MF groups is MF (Korchagin, Prop. 13). -/
theorem isOperatorMF_directLimit_of_operatorMF [Countable (DirectLimit A f)]
    (hMF : ∀ i, IsOperatorMF (A i)) : IsOperatorMF (DirectLimit A f) :=
  isOperatorMF_of_isDirectedColimit_operatorMF (isDirectedColimit_directLimit f) hMF

end MathlibDirectLimit

#audit_axioms isOperatorMF_of_isDirectedColimit
#audit_axioms isOperatorMF_of_isDirectedColimit_operatorMF
#audit_axioms isOperatorMF_directLimit_of_residuallyFinite
#audit_axioms isOperatorMF_directLimit_of_operatorMF

end GroupApproximation.Full.NM09
