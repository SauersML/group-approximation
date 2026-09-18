import GroupApproximation.Manuscript.NonMF.ChainA.LoopErasure
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Meta.AxiomGuard

/-!
# A clopen partition separating the points of each class (tex 1502–1504)

`non_mf_groups_exist.tex`, proof of `lem:transient-matrices`, tex 1502–1504:

"Choose a finite clopen partition of $C$ separating distinct points in each class: the finitely
many nonidentity partial shifts have no fixed points, so compactness gives such a partition."

The setting: `T` is a homeomorphism of a compact totally disconnected metric space `X`. `C` is a
clopen set disjoint from the chain recurrent set `Y = CR(T)`, and `E` is a finite set of shift
exponents. The class of `x ∈ C` is `{T^d x : d ∈ R x}`, where
`R = reachableExponents T C E (m - 1)` and `m` is the orbit bound.

Proof route.

* **No fixed points.** If `T^d x = x` with `d ≠ 0` and `x ∈ C`, then all `T^{kd} x = x` lie in
  `C`. That gives `m + 1` distinct exponents returning to `C`, which contradicts the orbit bound.
* **Compactness.** For `x` and `d ∈ R x \ {0}`, zero-dimensionality gives a clopen `A x d` with
  `x ∈ A x d` and `T^d x ∉ A x d`. The set `N x` of points with the same class exponents lying in
  every `A x d ∩ T^{-d}(A x d)ᶜ` is clopen and contains `x`. Finitely many `N z` cover `X`.
* **Atoms.** Membership in the finitely many sets `A z d` is a locally constant map into a finite
  type. Numbering its values gives `atom : X → Fin N`, whose fibres form the clopen partition.
  Distinct points `T^a x ≠ T^b x` of a class lie in distinct atoms: `T^{a-b}` is a nonidentity
  class shift at `T^b x`.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainA

open GroupApproximation.ChainCore Topology

section Separation

variable {X : Type*} [TopologicalSpace X]

/-- The separating neighbourhood of `x`: same class exponents, and on the correct side of every
separating clopen set `A x d`. -/
def separatingNbhd (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) (A : X → ℤ → Set X)
    (x : X) : Set X :=
  {y | reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x} ∩
    ⋂ d ∈ (reachableExponents T C E (m - 1) x).erase 0, (A x d ∩ (T ^ d) ⁻¹' (A x d)ᶜ)

variable {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-- A point with a class exponent lies in `C`. -/
theorem mem_of_mem_reachableExponents {r : ℕ} {x : X} {d : ℤ}
    (hd : d ∈ reachableExponents T C E r x) : x ∈ C := by
  have h := zpow_mem_of_mem_reachableExponents (neg_mem_reachableExponents r hd)
  rwa [GroupApproximation.Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero,
    Homeomorph.one_apply] at h

/-- **Nonidentity shifts have no fixed points on `C`** under the orbit bound. -/
theorem zpow_apply_ne_of_exponentBound (hm : ExponentBound T C m) {x : X} (hx : x ∈ C) {d : ℤ}
    (hd : d ≠ 0) : (T ^ d) x ≠ x := by
  intro h
  have hiter : ∀ k : ℕ, (T ^ ((k : ℤ) * d)) x = x := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_mul, zpow_zero, Homeomorph.one_apply]
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℤ) * d = d + (k : ℤ) * d by push_cast; ring, zpow_add,
        Homeomorph.mul_apply, ih, h]
  have hcard := hm x ((Finset.range (m + 1)).image fun k : ℕ => (k : ℤ) * d) fun e he => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 he
    show (T ^ ((k : ℤ) * d)) x ∈ C
    rw [hiter k]
    exact hx
  rw [Finset.card_image_of_injOn, Finset.card_range] at hcard
  · omega
  · intro k _ l _ hkl
    exact_mod_cast mul_right_cancel₀ hd hkl

/-- Membership in finitely many clopen sets is locally constant. -/
theorem isLocallyConstant_setOf_mem {ι : Type*} [Finite ι] {A : ι → Set X}
    (hA : ∀ i, IsClopen (A i)) : IsLocallyConstant fun y => {i | y ∈ A i} := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : ∀ i, ∀ᶠ y in 𝓝 x, (y ∈ A i ↔ x ∈ A i) := fun i => by
    by_cases hx : x ∈ A i
    · filter_upwards [(hA i).isOpen.mem_nhds hx] with y hy
      exact ⟨fun _ => hx, fun _ => hy⟩
    · have hx' : x ∈ (A i)ᶜ := hx
      filter_upwards [(hA i).isClosed.isOpen_compl.mem_nhds hx'] with y hy
      exact ⟨fun h' => (hy h').elim, fun h' => (hx h').elim⟩
  filter_upwards [Filter.eventually_all.2 h] with y hy
  exact Set.ext fun i => hy i

/-- A locally constant map into a finite type, numbered by `Fin N`. -/
theorem exists_fin_atom {Z : Type*} [Finite Z] {f : X → Z} (hf : IsLocallyConstant f) :
    ∃ (N : ℕ) (atom : X → Fin N), IsLocallyConstant atom ∧ ∀ y z, atom y = atom z → f y = f z :=
  ⟨Nat.card Z, ⇑(Finite.equivFin Z) ∘ f, hf.comp _, fun _ _ h => (Finite.equivFin Z).injective h⟩

theorem isClopen_separatingNbhd (hC : IsClopen C) {A : X → ℤ → Set X}
    (hAc : ∀ x d, IsClopen (A x d)) (x : X) : IsClopen (separatingNbhd T C E m A x) := by
  show IsClopen ({y | reachableExponents T C E (m - 1) y = reachableExponents T C E (m - 1) x} ∩
    ⋂ d ∈ (reachableExponents T C E (m - 1) x).erase 0, (A x d ∩ (T ^ d) ⁻¹' (A x d)ᶜ))
  refine (isClopen_setOf_reachableExponents_eq hC (m - 1) _).inter
    (isClopen_biInter_finset fun d _ => ?_)
  exact (hAc x d).inter ((hAc x d).compl.preimage (T ^ d).continuous)

theorem mem_separatingNbhd_self {A : X → ℤ → Set X}
    (hAs : ∀ x d, x ∈ C → d ≠ 0 → x ∈ A x d ∧ (T ^ d) x ∉ A x d) (x : X) :
    x ∈ separatingNbhd T C E m A x := by
  refine ⟨rfl, Set.mem_iInter₂.2 fun d hd => ?_⟩
  obtain ⟨hd0, hdR⟩ := Finset.mem_erase.1 hd
  exact hAs x d (mem_of_mem_reachableExponents hdR) hd0

/-- **Separating atoms** (tex 1502–1504): a locally constant `atom : X → Fin N` with
`atom (T^d x) ≠ atom x` for every nonidentity class exponent `d` at `x ∈ C`. -/
theorem exists_separating_atoms [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (hC : IsClopen C) (hm : ExponentBound T C m) :
    ∃ (N : ℕ) (atom : X → Fin N), IsLocallyConstant atom ∧
      ∀ x ∈ C, ∀ d ∈ reachableExponents T C E (m - 1) x, d ≠ 0 → atom ((T ^ d) x) ≠ atom x := by
  have hsep : ∀ (x : X) (d : ℤ), ∃ A : Set X, IsClopen A ∧
      (x ∈ C → d ≠ 0 → x ∈ A ∧ (T ^ d) x ∉ A) := by
    intro x d
    by_cases h : x ∈ C ∧ d ≠ 0
    · have hne : (T ^ d) x ≠ x := zpow_apply_ne_of_exponentBound hm h.1 h.2
      have hxU : x ∈ ({(T ^ d) x} : Set X)ᶜ := by
        intro h'
        exact hne (Set.mem_singleton_iff.1 h').symm
      obtain ⟨V, hVc, hxV, hVU⟩ := compact_exists_isClopen_in_isOpen isOpen_compl_singleton hxU
      exact ⟨V, hVc, fun _ _ => ⟨hxV, fun hV => hVU hV (Set.mem_singleton _)⟩⟩
    · exact ⟨Set.univ, isClopen_univ, fun hx hd => (h ⟨hx, hd⟩).elim⟩
  choose A hAc hAs using hsep
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (separatingNbhd T C E m A) (fun x => (isClopen_separatingNbhd (E := E) (m := m) hC hAc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, mem_separatingNbhd_self (E := E) (m := m) hAs x⟩)
  obtain ⟨φ, hφdef⟩ : ∃ φ : X → Set {q : X × ℤ // q ∈ t ×ˢ t.biUnion (reachableExponents T C E (m - 1))},
      φ = fun y => {q | y ∈ A q.1.1 q.1.2} := ⟨_, rfl⟩
  have hφ : IsLocallyConstant φ := by
    rw [hφdef]
    exact isLocallyConstant_setOf_mem fun q => hAc q.1.1 q.1.2
  obtain ⟨N, atom, hatom, hinj⟩ := exists_fin_atom hφ
  refine ⟨N, atom, hatom, fun x _ d hd hd0 heq => ?_⟩
  obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have hRz : reachableExponents T C E (m - 1) x = reachableExponents T C E (m - 1) z := hxz.1
  have hdz : d ∈ reachableExponents T C E (m - 1) z := by
    rw [← hRz]
    exact hd
  have hsepz : x ∈ A z d ∩ (T ^ d) ⁻¹' (A z d)ᶜ :=
    Set.mem_iInter₂.1 hxz.2 d (Finset.mem_erase.2 ⟨hd0, hdz⟩)
  have hq : (z, d) ∈ t ×ˢ t.biUnion (reachableExponents T C E (m - 1)) :=
    Finset.mem_product.2 ⟨hzt, Finset.mem_biUnion.2 ⟨z, hzt, hdz⟩⟩
  have hcode := hinj _ _ heq
  have h4 : (⟨(z, d), hq⟩ : {q : X × ℤ // q ∈ t ×ˢ t.biUnion (reachableExponents T C E (m - 1))})
      ∈ φ ((T ^ d) x) := by
    rw [hcode, hφdef]
    exact hsepz.1
  rw [hφdef] at h4
  exact hsepz.2 h4

/-- Distinct points of a class lie in distinct atoms. -/
theorem atom_ne_of_mem_class (hm : ExponentBound T C m) {N : ℕ} {atom : X → Fin N}
    (hsep : ∀ x ∈ C, ∀ d ∈ reachableExponents T C E (m - 1) x, d ≠ 0 → atom ((T ^ d) x) ≠ atom x)
    {x : X} {a b : ℤ} (ha : a ∈ reachableExponents T C E (m - 1) x)
    (hb : b ∈ reachableExponents T C E (m - 1) x) (hab : a ≠ b) :
    atom ((T ^ a) x) ≠ atom ((T ^ b) x) := by
  have hbx := reachableExponents_zpow_eq hm hb
  have hmem : a - b ∈ reachableExponents T C E (m - 1) ((T ^ b) x) := by
    rw [hbx]
    exact Finset.mem_image_of_mem (· - b) ha
  have h := hsep _ (zpow_mem_of_mem_reachableExponents hb) (a - b) hmem (sub_ne_zero.2 hab)
  rwa [GroupApproximation.Dynamics.zpow_apply_zpow_apply, sub_add_cancel] at h

end Separation

/-- **tex 1502–1504.** "Choose a finite clopen partition of $C$ separating distinct points in
each class: the finitely many nonidentity partial shifts have no fixed points, so compactness
gives such a partition."

The statement gives:
* an orbit bound `m`;
* the absence of fixed points of the nonidentity class shifts;
* a finite clopen partition of `C` into the pieces `C ∩ atom⁻¹(i)`, `i : Fin N`, under which
  distinct points of every class lie in distinct pieces. -/
theorem manuscriptSentence_separatingClopenPartition {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (C : Set X) (hC : IsClopen C)
    (hCY : Disjoint C (GroupApproximation.Dynamics.chainRecurrentSet ⇑T)) (E : Finset ℤ) :
    ∃ m : ℕ, ExponentBound T C m ∧
      (∀ x ∈ C, ∀ d ∈ reachableExponents T C E (m - 1) x, d ≠ 0 → (T ^ d) x ≠ x) ∧
      ∃ (N : ℕ) (atom : X → Fin N), IsLocallyConstant atom ∧
        (∀ i, IsClopen (C ∩ {y | atom y = i})) ∧
        ∀ x ∈ C, ∀ a ∈ reachableExponents T C E (m - 1) x,
          ∀ b ∈ reachableExponents T C E (m - 1) x, a ≠ b → atom ((T ^ a) x) ≠ atom ((T ^ b) x) := by
  obtain ⟨m, -, -, -, -, hm⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_wandering_clopen_cover_of_isCompact T
      hC.isClosed.isCompact hCY
  obtain ⟨N, atom, hatom, hsep⟩ := exists_separating_atoms (E := E) hC hm
  exact ⟨m, hm, fun x hx d _ hd0 => zpow_apply_ne_of_exponentBound hm hx hd0, N, atom, hatom,
    fun i => hC.inter (hatom.isClopen_fiber i),
    fun _ _ _ ha _ hb hab => atom_ne_of_mem_class hm hsep ha hb hab⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_separatingClopenPartition

end GroupApproximation.Manuscript.NonMF.ChainA
