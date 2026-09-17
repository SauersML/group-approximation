import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse infrastructure (lane sk-flip-03): clopen tower bases

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"); infrastructure
for the Rubin / Matui routes to `SupportDisjointnessTransportStatement`.

## Truth check: the lane statement is FALSE for `n ≥ 2`

The lane asked for `V` clopen nonempty with `T^i V ⊆ W` for all `i < n` and the levels
`T^i V` (`i < n`) pairwise disjoint, for every aperiodic `T` and every nonempty open `W`.
This fails as soon as `W ∩ T⁻¹ W = ∅`: `V ⊆ W` and `T V ⊆ W` force `V = ∅`
(`not_exists_tower_of_disjoint_image`).  Concrete instance: the dyadic odometer
`T` on `{0,1}^ℕ` (add one with carry) is minimal, hence aperiodic, on the Cantor set, and the
cylinder `W = {ω | ω₀ = 0}` satisfies `T W = {ω | ω₀ = 1}`, so `n = 2` already fails.
The error in the route: "pick `x ∈ W`" does not give `T^i x ∈ W` for `i < n`.

## Corrected true statements proved here

* `exists_isClopen_levels`: for finitely many homeomorphisms `f i` and a point `x` whose images
  `f i x` are pairwise distinct and lie in an open `W`, and an open `U ∋ x`, there is a clopen
  `V ∋ x`, `V ⊆ U`, with `f i V ⊆ W` and the `f i V` pairwise disjoint.
  Proof: separate `f i x`, `f j x` by disjoint opens `A`, `B`; the open set
  `U ∩ ⋂ᵢ f i⁻¹ W ∩ ⋂_{i≠j} (f i⁻¹ A_{ij} ∩ f j⁻¹ B_{ij})` contains `x`; take a clopen
  neighbourhood of `x` inside it (`isTopologicalBasis_isClopen`).
* `exists_isClopen_tower_of_exponents` (aperiodic `T`, injective exponents `k`): the case
  `f i = T^{k i}`; aperiodicity gives distinctness of `T^{k i} x`.
* `exists_isClopen_tower_of_mem`: the lane statement with the missing hypothesis
  `∀ i < n, T^i x ∈ W` added.
* `exists_isClopen_tower_base`: the lane statement with `∀ i < n, T^i V ⊆ W` weakened to
  `V ⊆ W` (true for every aperiodic `T`).
* `exists_isClopen_tower_in_open` (file `InfraTowerBaseMinimal`): for minimal `T` on a perfect
  space the levels can be put inside `W` using non-consecutive exponents.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- Refutation certificate for the lane shape: if `W` and `T W` are disjoint, no nonempty `V`
has `T^i V ⊆ W` for `i = 0, 1`. -/
theorem not_exists_tower_of_disjoint_image {T : X ≃ₜ X} {W : Set X}
    (hWT : Disjoint W (T '' W)) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ V : Set X, V.Nonempty ∧ ∀ i < n, (T ^ (i : ℤ)) '' V ⊆ W := by
  rintro ⟨V, ⟨v, hv⟩, hVW⟩
  have h0 : v ∈ W := by
    have h := hVW 0 (by omega) (Set.mem_image_of_mem _ hv)
    rwa [Nat.cast_zero, homeoPow_zero] at h
  have h1 : T v ∈ W := by
    have h := hVW 1 (by omega) (Set.mem_image_of_mem _ hv)
    rwa [Nat.cast_one, homeoPow_one] at h
  exact Set.disjoint_left.1 hWT h1 (Set.mem_image_of_mem T h0)

/-- A clopen neighbourhood of `x` whose images under finitely many homeomorphisms lie in `W`
and are pairwise disjoint, provided the images of `x` lie in `W` and are pairwise distinct. -/
theorem exists_isClopen_levels [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {ι : Type*} [Finite ι] (f : ι → X ≃ₜ X) {W U : Set X} (hW : IsOpen W) (hU : IsOpen U)
    {x : X} (hxU : x ∈ U) (hxW : ∀ i, f i x ∈ W) (hinj : ∀ i j, i ≠ j → f i x ≠ f j x) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U ∧ (∀ i, f i '' V ⊆ W) ∧
      ∀ i j, i ≠ j → Disjoint (f i '' V) (f j '' V) := by
  have hsep : ∀ p : ι × ι, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      (p.1 ≠ p.2 → ∀ z ∈ O, ∀ w ∈ O, f p.1 z ≠ f p.2 w) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun h => absurd hp h⟩
    · obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := t2_separation (hinj p.1 p.2 hp)
      refine ⟨f p.1 ⁻¹' A ∩ f p.2 ⁻¹' B,
        (hA.preimage (f p.1).continuous).inter (hB.preimage (f p.2).continuous),
        ⟨hxA, hxB⟩, fun _ z hz w hw hzw => ?_⟩
      have h1 : f p.1 z ∈ A := hz.1
      have h2 : f p.1 z ∈ B := by
        rw [hzw]
        exact hw.2
      exact Set.disjoint_left.1 hAB h1 h2
  choose O hOo hxO hOsep using hsep
  have hNo : IsOpen (U ∩ (⋂ i, f i ⁻¹' W) ∩ ⋂ p, O p) :=
    (hU.inter (isOpen_iInter_of_finite fun i => hW.preimage (f i).continuous)).inter
      (isOpen_iInter_of_finite hOo)
  have hxN : x ∈ U ∩ (⋂ i, f i ⁻¹' W) ∩ ⋂ p, O p :=
    ⟨⟨hxU, Set.mem_iInter.2 hxW⟩, Set.mem_iInter.2 hxO⟩
  obtain ⟨V, hVc, hxV, hVN⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 (hNo.mem_nhds hxN)
  have hV : IsClopen V := hVc
  refine ⟨V, hV, hxV, fun z hz => (hVN hz).1.1, ?_, ?_⟩
  · rintro i _ ⟨z, hz, rfl⟩
    exact Set.mem_iInter.1 (hVN hz).1.2 i
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact hOsep (i, j) hij z (Set.mem_iInter.1 (hVN hz).2 (i, j)) w
      (Set.mem_iInter.1 (hVN hw).2 (i, j)) hwz.symm

/-- Tower with arbitrary distinct exponents for an aperiodic homeomorphism. -/
theorem exists_isClopen_tower_of_exponents [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {T : X ≃ₜ X} (hT : IsAperiodic T) {ι : Type*} [Finite ι]
    {k : ι → ℤ} (hk : Function.Injective k) {W U : Set X} (hW : IsOpen W) (hU : IsOpen U)
    {x : X} (hxU : x ∈ U) (hxW : ∀ i, (T ^ k i) x ∈ W) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U ∧ (∀ i, (T ^ k i) '' V ⊆ W) ∧
      ∀ i j, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V) :=
  exists_isClopen_levels (fun i => T ^ k i) hW hU hxU hxW
    fun _ _ hij h => hij (hk (zpow_apply_injective hT h))

/-- The lane shape, with the hypothesis that the first `n` orbit points of `x` lie in `W`. -/
theorem exists_isClopen_tower_of_mem [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {T : X ≃ₜ X} (hT : IsAperiodic T) {W : Set X} (hW : IsOpen W) {x : X} {n : ℕ}
    (hx : ∀ i < n, (T ^ (i : ℤ)) x ∈ W) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ (∀ i < n, (T ^ (i : ℤ)) '' V ⊆ W) ∧
      ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V) := by
  obtain ⟨V, hV, hxV, -, hVW, hdisj⟩ :=
    exists_isClopen_levels (fun i : Fin n => T ^ ((i : ℕ) : ℤ)) hW isOpen_univ
      (Set.mem_univ x) (fun i => hx i i.2)
      (fun i j hij h => hij (Fin.ext (by exact_mod_cast zpow_apply_injective hT h)))
  exact ⟨V, hV, ⟨x, hxV⟩, fun i hi => hVW ⟨i, hi⟩,
    fun i hi j hj hij => hdisj ⟨i, hi⟩ ⟨j, hj⟩ fun h => hij (congrArg Fin.val h)⟩

/-- The lane shape with the level condition weakened to `V ⊆ W` (true for aperiodic `T`). -/
theorem exists_isClopen_tower_base [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {T : X ≃ₜ X} (hT : IsAperiodic T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) (n : ℕ) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ V ⊆ W ∧
      ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hxV, hVW, -, hdisj⟩ :=
    exists_isClopen_levels (fun i : Fin n => T ^ ((i : ℕ) : ℤ)) isOpen_univ hW hx
      (fun _ => Set.mem_univ _)
      (fun i j hij h => hij (Fin.ext (by exact_mod_cast zpow_apply_injective hT h)))
  exact ⟨V, hV, ⟨x, hxV⟩, hVW,
    fun i hi j hj hij => hdisj ⟨i, hi⟩ ⟨j, hj⟩ fun h => hij (congrArg Fin.val h)⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.not_exists_tower_of_disjoint_image
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_levels
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_tower_of_exponents
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_tower_of_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_tower_base
