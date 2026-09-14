import GroupApproximation.Dynamics.FiniteMemory
import GroupApproximation.Dynamics.CosetRegion
import GroupApproximation.Dynamics.SubsetSchedule

/-!
# Peeling Boolean strata

All maps act on one common finite fiber alphabet. The local cancellation
argument does not require corrections at different subsets to commute.
-/

namespace GroupApproximation.Surjunctivity

open scoped Pointwise

universe u v w

variable {G : Type u} [Group G] [DecidableEq G]
  {B : Type v} {X : Type w} [DecidableEq X]

/-- A point belongs to every marked stratum after enlarging by a finite window. -/
def stratumRegion (Z : X → Set G) (U : Finset X) (F : Finset G) : Set G :=
  {g | ∀ s ∈ U, ∃ f ∈ F, g * f ∈ Z s}

/-- Correct a map using all already constructed proper-subset inverses. -/
def peeledMap (schedule : SubsetSchedule X) (τ σ : Finset X → WindowMap G B)
    (U : Finset X) : WindowMap G B :=
  (WindowMap.compose ((schedule.proper U).map σ)).comp (τ U)

/-- The support step in Boolean-strata peeling. The cancellation hypotheses
are precisely the inverse identities obtained at earlier proper subsets. -/
theorem peeledMap_support (schedule : SubsetSchedule X)
    (Z : X → Set G) (τ σ : Finset X → WindowMap G B)
    (width : Finset X → Finset G) (U : Finset X)
    (hlower : ∀ V, V ⊂ U →
      Function.LeftInverse (σ V).toFun (peeledMap schedule τ σ V).toFun)
    (hsupport : ∀ V, V ⊂ U → ∀ x g,
      g ∉ stratumRegion Z V (width V) → (σ V).toFun x g = x g)
    (hslice : ∀ V, V ⊆ U → ∀ x g,
      (∀ s ∈ U, s ∉ V → g ∉ Z s) → (τ U).toFun x g = (τ V).toFun x g) :
    ∃ F : Finset G, 1 ∈ F ∧ ∀ x g,
      g ∉ stratumRegion Z U F → (peeledMap schedule τ σ U).toFun x g = x g := by
  classical
  let corrections := WindowMap.compose ((schedule.proper U).map σ)
  let P := (peeledMap schedule τ σ U).memory
  let F := P ∪ (schedule.proper U).toFinset.biUnion (fun W => P * width W)
  have hMP : corrections.memory ⊆ P := by
    intro m hm
    exact (mul_one m) ▸ Finset.mul_mem_mul hm (τ U).one_mem
  have hPF : P ⊆ F := Finset.subset_union_left
  refine ⟨F, hPF (peeledMap schedule τ σ U).one_mem, ?_⟩
  intro x g hg
  let V := U.filter fun s => ∃ f ∈ F, g * f ∈ Z s
  have hVU : V ⊆ U := Finset.filter_subset _ _
  have hVproper : V ⊂ U := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hVU, ?_⟩
    intro hEq
    apply hg
    intro s hs
    have hsV : s ∈ V := hEq.symm ▸ hs
    exact (Finset.mem_filter.mp hsV).2
  have hτeq : corrections.toFun ((τ U).toFun x) g =
      corrections.toFun ((τ V).toFun x) g := by
    apply corrections.hasMemory
    intro m hm
    apply hslice V hVU x (g * m)
    intro s hs hsV hZ
    apply hsV
    exact Finset.mem_filter.mpr ⟨hs, m, hPF (hMP hm), hZ⟩
  have hinactive : ∀ W ∈ schedule.proper U, ¬ W ⊆ V → ∀ y,
      Set.EqOn ((σ W).toFun y) y
        ({g} * (corrections.memory : Set G)) := by
    intro W hW hWV y h hh
    obtain ⟨g', hg', p, hp, rfl⟩ := hh
    have hg' : g' = g := hg'
    subst g'
    have hWU := (schedule.mem_proper U W).mp hW
    apply hsupport W hWU y (g * p)
    intro hregion
    change ¬ ∀ s, s ∈ W → s ∈ V at hWV
    push Not at hWV
    obtain ⟨s, hsW, hsV⟩ := hWV
    obtain ⟨f, hf, hZ⟩ := hregion s hsW
    have hpf : p * f ∈ F := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨W, List.mem_toFinset.mpr hW,
        Finset.mul_mem_mul (hMP hp) hf⟩)
    apply hsV
    exact Finset.mem_filter.mpr ⟨hWU.1 hsW, p * f, hpf,
      (mul_assoc g p f) ▸ hZ⟩
  have hdelete := WindowMap.compose_eqOn_indexed_filter
    (schedule.proper U) σ (fun W => W ⊆ V) {g} hinactive ((τ V).toFun x)
  have hdelete_g := hdelete (Set.mem_singleton g)
  rw [schedule.restrict U V hVproper] at hdelete_g
  have hcancel := congrFun (hlower V hVproper x) g
  exact hτeq.trans (hdelete_g.trans hcancel)

private theorem compose_indexed_injective {I : Type*} (L : List I)
    (f : I → WindowMap G B) (h : ∀ i ∈ L, Function.Injective (f i).toFun) :
    Function.Injective (WindowMap.compose (L.map f)).toFun := by
  induction L with
  | nil => exact Function.injective_id
  | cons i L ih =>
    exact (h i (List.mem_cons_self ..)).comp
      (ih fun j hj => h j (List.mem_cons_of_mem i hj))

private theorem compose_indexed_equivariant {I : Type*} (L : List I)
    (f : I → WindowMap G B) (H : Subgroup G)
    (h : ∀ i ∈ L, ∀ k : H, ∀ x g,
      (f i).toFun (shift (k : G) x) g = (f i).toFun x ((k : G) * g)) :
    ∀ k : H, ∀ x g, (WindowMap.compose (L.map f)).toFun (shift (k : G) x) g =
      (WindowMap.compose (L.map f)).toFun x ((k : G) * g) := by
  induction L with
  | nil => intro k x g; rfl
  | cons i L ih =>
    intro k x g
    have htail := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    have hshift : (WindowMap.compose (L.map f)).toFun (shift (k : G) x) =
        shift (k : G) ((WindowMap.compose (L.map f)).toFun x) :=
      funext fun a => htail k x a
    change (f i).toFun ((WindowMap.compose (L.map f)).toFun (shift (k : G) x)) g = _
    rw [hshift]
    exact h i (List.mem_cons_self ..) k _ g

/-- Partial inverse families, valid below one cardinality threshold. -/
structure PeelingStage (schedule : SubsetSchedule X) (Z : X → Set G)
    (τ : Finset X → WindowMap G B) (K : Finset X → Subgroup G) (n : ℕ) where
  inverse : Finset X → WindowMap G B
  width : Finset X → Finset G
  valid : ∀ U, U.card < n →
    Function.LeftInverse (inverse U).toFun (peeledMap schedule τ inverse U).toFun ∧
    Function.RightInverse (inverse U).toFun (peeledMap schedule τ inverse U).toFun ∧
    (∀ x g, g ∉ stratumRegion Z U (width U) → (inverse U).toFun x g = x g) ∧
    (∀ k : K U, ∀ x g,
      (inverse U).toFun (shift (k : G) x) g = (inverse U).toFun x ((k : G) * g))

section Construction

variable [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
  (schedule : SubsetSchedule X) (Z : X → Set G)
  (τ : Finset X → WindowMap G B) (K : Finset X → Subgroup G)
  (hK : ∀ U, IsSurjunctive (K U))
  (hanti : ∀ V U, V ⊆ U → K U ≤ K V)
  (hinj : ∀ U, Function.Injective (τ U).toFun)
  (hequiv : ∀ U, ∀ k : K U, ∀ x g,
    (τ U).toFun (shift (k : G) x) g = (τ U).toFun x ((k : G) * g))
  (hslice : ∀ U V, V ⊆ U → ∀ x g,
    (∀ s ∈ U, s ∉ V → g ∉ Z s) → (τ U).toFun x g = (τ V).toFun x g)
  (hcover : ∀ U F, ∃ T : Finset G, ∀ g ∈ stratumRegion Z U F,
    ∃ r ∈ T, g * r⁻¹ ∈ K U)

include schedule hK hanti hinj hequiv hslice hcover

private theorem next_peeling_inverse {n : ℕ}
    (stage : PeelingStage schedule Z τ K n) (U : Finset X) (hu : U.card = n) :
    ∃ ψ : WindowMap G B, ∃ F : Finset G,
      Function.LeftInverse ψ.toFun (peeledMap schedule τ stage.inverse U).toFun ∧
      Function.RightInverse ψ.toFun (peeledMap schedule τ stage.inverse U).toFun ∧
      (∀ x g, g ∉ stratumRegion Z U F → ψ.toFun x g = x g) ∧
      (∀ k : K U, ∀ x g,
        ψ.toFun (shift (k : G) x) g = ψ.toFun x ((k : G) * g)) := by
  classical
  have hlt (V : Finset X) (hV : V ⊂ U) : V.card < n := hu ▸ Finset.card_lt_card hV
  have hi : Function.Injective (peeledMap schedule τ stage.inverse U).toFun :=
    (compose_indexed_injective (schedule.proper U) stage.inverse (by
      intro V hV
      exact (stage.valid V (hlt V ((schedule.mem_proper U V).mp hV))).2.1.injective)).comp
        (hinj U)
  have he : ∀ k : K U, ∀ x g,
      (peeledMap schedule τ stage.inverse U).toFun (shift (k : G) x) g =
      (peeledMap schedule τ stage.inverse U).toFun x ((k : G) * g) := by
    have hc := compose_indexed_equivariant (schedule.proper U) stage.inverse (K U) (by
      intro V hV k x g
      have hVU := (schedule.mem_proper U V).mp hV
      exact (stage.valid V (hlt V hVU)).2.2.2
        ⟨k, hanti V U hVU.1 k.property⟩ x g)
    intro k x g
    have ht : (τ U).toFun (shift (k : G) x) = shift (k : G) ((τ U).toFun x) :=
      funext fun a => hequiv U k x a
    change (WindowMap.compose ((schedule.proper U).map stage.inverse)).toFun
      ((τ U).toFun (shift (k : G) x)) g = _
    rw [ht]
    exact hc k _ g
  obtain ⟨F, _, hf⟩ := peeledMap_support schedule Z τ stage.inverse stage.width U
    (fun V hV => (stage.valid V (hlt V hV)).1)
    (fun V hV => (stage.valid V (hlt V hV)).2.2.1) (hslice U)
  obtain ⟨T, hT⟩ := hcover U F
  obtain ⟨_, ψ, ⟨M, hM⟩, hl, hr, hfixed, hsym⟩ := coset_region
    (K U) (hK U) (peeledMap schedule τ stage.inverse U).toFun hi
    ⟨_, (peeledMap schedule τ stage.inverse U).hasMemory⟩
    (stratumRegion Z U F) T hT hf he
  exact ⟨⟨ψ, insert 1 M, Finset.mem_insert_self _ _,
    hM.mono (Finset.subset_insert _ _)⟩, F, hl, hr, hfixed, hsym⟩

private theorem exists_peeling_stage (n : ℕ) : Nonempty (PeelingStage schedule Z τ K n) := by
  classical
  induction n with
  | zero =>
    exact ⟨⟨fun _ => WindowMap.identity, fun _ => {1},
      fun U h => False.elim (Nat.not_lt_zero U.card h)⟩⟩
  | succ n ih =>
    obtain ⟨stage⟩ := ih
    have hnew : ∀ U : Finset X, ∃ ψ : WindowMap G B, ∃ F : Finset G, U.card = n →
        Function.LeftInverse ψ.toFun (peeledMap schedule τ stage.inverse U).toFun ∧
        Function.RightInverse ψ.toFun (peeledMap schedule τ stage.inverse U).toFun ∧
        (∀ x g, g ∉ stratumRegion Z U F → ψ.toFun x g = x g) ∧
        (∀ k : K U, ∀ x g,
          ψ.toFun (shift (k : G) x) g = ψ.toFun x ((k : G) * g)) := by
      intro U
      by_cases hU : U.card = n
      · obtain ⟨ψ, F, hψ⟩ := next_peeling_inverse schedule Z τ K hK hanti hinj hequiv
          hslice hcover stage U hU
        exact ⟨ψ, F, fun _ => hψ⟩
      · exact ⟨WindowMap.identity, {1}, fun h => False.elim (hU h)⟩
    choose ψ F hψ using hnew
    let σ' : Finset X → WindowMap G B := fun U => if U.card = n then ψ U else stage.inverse U
    let F' : Finset X → Finset G := fun U => if U.card = n then F U else stage.width U
    have hres (U : Finset X) (hU : U.card ≤ n) :
        peeledMap schedule τ σ' U = peeledMap schedule τ stage.inverse U := by
      apply congrArg (fun L => (WindowMap.compose L).comp (τ U))
      apply List.map_congr_left
      intro V hV
      have hlt := lt_of_lt_of_le
        (Finset.card_lt_card ((schedule.mem_proper U V).mp hV)) hU
      exact if_neg (Nat.ne_of_lt hlt)
    refine ⟨⟨σ', F', ?_⟩⟩
    intro U hU
    rw [hres U (Nat.le_of_lt_succ hU)]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hU) with hlt | heq
    · simpa only [σ', F', if_neg (Nat.ne_of_lt hlt)] using stage.valid U hlt
    · simpa only [σ', F', if_pos heq] using hψ U heq

/-- The abstract Boolean-strata theorem: every member of the family is bijective. -/
theorem stratified_bijective (U : Finset X) : Function.Bijective (τ U).toFun := by
  classical
  obtain ⟨stage⟩ := exists_peeling_stage schedule Z τ K hK hanti hinj hequiv hslice hcover
    (U.card + 1)
  have hv := stage.valid U (Nat.lt_succ_self U.card)
  have hi : Function.Injective
      (WindowMap.compose ((schedule.proper U).map stage.inverse)).toFun :=
    compose_indexed_injective (schedule.proper U) stage.inverse (by
      intro V hV
      have hlt := lt_trans (Finset.card_lt_card ((schedule.mem_proper U V).mp hV))
        (Nat.lt_succ_self U.card)
      exact (stage.valid V hlt).2.1.injective)
  refine ⟨hinj U, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hv.2.1.surjective
    ((WindowMap.compose ((schedule.proper U).map stage.inverse)).toFun y)
  exact ⟨x, hi hx⟩

end Construction

end GroupApproximation.Surjunctivity
