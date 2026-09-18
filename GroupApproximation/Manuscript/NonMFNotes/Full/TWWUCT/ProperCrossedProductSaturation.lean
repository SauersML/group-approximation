import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.ProperCrossedProductSlice
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAmbientAction

/-!
# Saturations and invariant exhaustions for proper actions

Lane TWWUCT-E (WO-TWWUCT-E), manuscript label `thm:fixed-radical-membership` (UCT input,
`non_mf_group_notes.tex` L1370--1378).  Tu (K-Theory 17 (1999), §10) and Higson--Kasparov
(Invent. Math. 144 (2001), §9) put the proper crossed product `A(H) ⋊_r G` in the bootstrap class
by exhausting the proper `G`-space by invariant open sets

`W_n = G · (U_0 ∪ ⋯ ∪ U_{n-1})`,

where the `U_i` are slices.  The quotient step `W_{n+1} \ W_n` lies in the saturation `G · U_n`
of one slice.  This file provides the point-set part of that exhaustion:

* `DiscreteAction.IsInvariantSet`, `DiscreteAction.saturation`: invariant sets and `G · U`.
* `DiscreteAction.exhaustion V n = G · ⋃_{i<n} V i`: open, invariant, increasing, exhausting,
  with `exhaustion_succ`.
* `DiscreteAction.exists_slice_sequence`: an `ℕ`-indexed slice cover.
* `AffineIsometricAction.ambientMap_eq_zero_of_notMem`: the HKT action preserves vanishing off an
  invariant set, so it preserves the ideals `I_W`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

namespace DiscreteAction

variable {G : Type u} [Group G] {Z : Type v} [TopologicalSpace Z] (α : DiscreteAction G Z)

/-- `W` is `G`-invariant (`thm:fixed-radical-membership`, UCT input). -/
def IsInvariantSet (W : Set Z) : Prop :=
  ∀ (g : G) (z : Z), z ∈ W → α.act g z ∈ W

/-- The saturation `G · U` (`thm:fixed-radical-membership`, UCT input). -/
def saturation (U : Set Z) : Set Z :=
  {z : Z | ∃ g : G, α.act g z ∈ U}

theorem mem_saturation {U : Set Z} {z : Z} : z ∈ α.saturation U ↔ ∃ g : G, α.act g z ∈ U :=
  Iff.rfl

/-- `U ⊆ G · U` (`thm:fixed-radical-membership`, UCT input). -/
theorem subset_saturation (U : Set Z) : U ⊆ α.saturation U := by
  intro z hz
  refine ⟨1, ?_⟩
  rw [α.act_one]
  exact hz

/-- Saturation is monotone (`thm:fixed-radical-membership`, UCT input). -/
theorem saturation_mono {U V : Set Z} (h : U ⊆ V) : α.saturation U ⊆ α.saturation V := by
  intro z hz
  obtain ⟨g, hg⟩ := hz
  exact ⟨g, h hg⟩

/-- `G · U` is invariant (`thm:fixed-radical-membership`, UCT input). -/
theorem isInvariantSet_saturation (U : Set Z) : α.IsInvariantSet (α.saturation U) := by
  intro g z hz
  obtain ⟨h, hh⟩ := hz
  refine ⟨h * g⁻¹, ?_⟩
  rw [α.act_mul, α.act_inv_act]
  exact hh

/-- `G · U = ⋃_g g⁻¹ U` (`thm:fixed-radical-membership`, UCT input). -/
theorem saturation_eq_iUnion (U : Set Z) : α.saturation U = ⋃ g : G, α.act g ⁻¹' U := by
  ext z
  exact Set.mem_iUnion.symm

/-- The saturation of an open set is open (`thm:fixed-radical-membership`, UCT input). -/
theorem isOpen_saturation {U : Set Z} (hU : IsOpen U) : IsOpen (α.saturation U) := by
  rw [α.saturation_eq_iUnion]
  exact isOpen_iUnion fun g => hU.preimage (α.continuous_act g)

variable {α}

/-- The complement of an invariant set is invariant (`thm:fixed-radical-membership`,
UCT input). -/
theorem IsInvariantSet.compl {W : Set Z} (hW : α.IsInvariantSet W) : α.IsInvariantSet Wᶜ := by
  intro g z hz
  have hz' : z ∉ W := hz
  show α.act g z ∉ W
  intro hgz
  apply hz'
  have h := hW g⁻¹ (α.act g z) hgz
  rw [α.act_inv_act] at h
  exact h

variable (α)

/-- The invariant exhaustion `W_n = G · ⋃_{i<n} V i` (`thm:fixed-radical-membership`,
UCT input). -/
def exhaustion (V : ℕ → Set Z) (n : ℕ) : Set Z :=
  α.saturation (⋃ (i : ℕ) (_ : i < n), V i)

/-- `W_0 = ∅` (`thm:fixed-radical-membership`, UCT input). -/
theorem exhaustion_zero (V : ℕ → Set Z) : α.exhaustion V 0 = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := hz
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.1 hg
    exact absurd hi (Nat.not_lt_zero i)
  · intro hz
    exact absurd hz (Set.notMem_empty z)

/-- `W_n ⊆ W_m` for `n ≤ m` (`thm:fixed-radical-membership`, UCT input). -/
theorem exhaustion_mono (V : ℕ → Set Z) {n m : ℕ} (h : n ≤ m) :
    α.exhaustion V n ⊆ α.exhaustion V m := by
  refine α.saturation_mono ?_
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hz
  exact Set.mem_iUnion₂.2 ⟨i, Nat.lt_of_lt_of_le hi h, hzi⟩

/-- `W_n` is invariant (`thm:fixed-radical-membership`, UCT input). -/
theorem isInvariantSet_exhaustion (V : ℕ → Set Z) (n : ℕ) :
    α.IsInvariantSet (α.exhaustion V n) :=
  α.isInvariantSet_saturation _

/-- `W_n` is open when the `V i` are (`thm:fixed-radical-membership`, UCT input). -/
theorem isOpen_exhaustion {V : ℕ → Set Z} (hV : ∀ i, IsOpen (V i)) (n : ℕ) :
    IsOpen (α.exhaustion V n) :=
  α.isOpen_saturation (isOpen_iUnion fun i => isOpen_iUnion fun (_ : i < n) => hV i)

/-- `W_{n+1} = W_n ∪ G · V n`: the quotient step lies in one saturated slice
(`thm:fixed-radical-membership`, UCT input). -/
theorem exhaustion_succ (V : ℕ → Set Z) (n : ℕ) :
    α.exhaustion V (n + 1) = α.exhaustion V n ∪ α.saturation (V n) := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := hz
    obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 hg
    rcases Nat.lt_or_ge i n with hin | hin
    · exact Set.mem_union_left _
        (show z ∈ α.exhaustion V n from ⟨g, Set.mem_iUnion₂.2 ⟨i, hin, hgi⟩⟩)
    · have hieq : i = n := Nat.le_antisymm (Nat.lt_add_one_iff.1 hi) hin
      rw [hieq] at hgi
      exact Set.mem_union_right _ (show z ∈ α.saturation (V n) from ⟨g, hgi⟩)
  · intro hz
    rcases hz with hz | hz
    · exact α.exhaustion_mono V (Nat.le_add_right n 1) hz
    · obtain ⟨g, hg⟩ := hz
      exact ⟨g, Set.mem_iUnion₂.2 ⟨n, Nat.lt_add_one n, hg⟩⟩

/-- The `W_n` exhaust the space when the `V i` cover it (`thm:fixed-radical-membership`,
UCT input). -/
theorem iUnion_exhaustion {V : ℕ → Set Z} (hcov : (⋃ i, V i) = Set.univ) :
    (⋃ n, α.exhaustion V n) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  have hz : z ∈ ⋃ i, V i := by
    rw [hcov]
    exact Set.mem_univ z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  refine Set.mem_iUnion.2 ⟨i + 1, α.subset_saturation (⋃ (j : ℕ) (_ : j < i + 1), V j) ?_⟩
  exact Set.mem_iUnion₂.2 ⟨i, Nat.lt_add_one i, hi⟩

/-- The slice conditions at `z` for an open set `U` (`thm:fixed-radical-membership`,
UCT input). -/
def IsSliceAt (z : Z) (U : Set Z) : Prop :=
  IsOpen U ∧ z ∈ U ∧ (∀ k ∈ α.stab z, ∀ x ∈ U, α.act k x ∈ U) ∧
    ∀ (g : G) (x : Z), x ∈ U → α.act g x ∈ U → g ∈ α.stab z

variable {α}

/-- **An `ℕ`-indexed slice cover**: each `V n` is empty or a slice at one of its points, and the
`V n` cover the space (`thm:fixed-radical-membership`, UCT input; Tu 1999, §10). -/
theorem exists_slice_sequence [T2Space Z] [SecondCountableTopology Z] (hα : α.IsProper) :
    ∃ V : ℕ → Set Z, (⋃ n, V n) = Set.univ ∧
      ∀ n, IsOpen (V n) ∧ (V n = ∅ ∨ ∃ z, α.IsSliceAt z (V n)) := by
  obtain ⟨U, T, hTc, hcov, hU⟩ := exists_countable_slice_cover hα
  by_cases hT : T.Nonempty
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hT
    refine ⟨fun n => U (f n), ?_, fun n => ⟨(hU (f n)).1, Or.inr ⟨f n, hU (f n)⟩⟩⟩
    have h : (⋃ n, U (f n)) = ⋃ z ∈ T, U z := by
      rw [hf, Set.biUnion_range]
    show (⋃ n, U (f n)) = Set.univ
    rw [h, hcov]
  · have hT' : T = ∅ := Set.not_nonempty_iff_eq_empty.1 hT
    rw [hT', Set.biUnion_empty] at hcov
    refine ⟨fun _ => ∅, ?_, fun _ => ⟨isOpen_empty, Or.inl rfl⟩⟩
    show (⋃ _ : ℕ, (∅ : Set Z)) = Set.univ
    rw [Set.iUnion_empty]
    exact hcov

end DiscreteAction

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- **The HKT action preserves vanishing off an invariant set**: if `W ⊆ ℝ × H` is invariant
under `(t, h) ↦ (t, g • h)` and `F` vanishes off `W`, so does `α_g F`.  Hence `α_g` preserves the
ideals `I_W` (`thm:fixed-radical-membership`, UCT input; HK 2001, §9). -/
theorem ambientMap_eq_zero_of_notMem {W : Set (ℝ × H)} (hW : b.lineAction.IsInvariantSet W)
    (g : G) {F : ℝ × H →ᵇ C} (hF : ∀ x : ℝ × H, x ∉ W → F x = 0) (x : ℝ × H) (hx : x ∉ W) :
    b.ambientMap g F x = 0 := by
  obtain ⟨t, y⟩ := x
  rw [b.ambientMap_apply]
  have hmem : (t, b.act g⁻¹ y) ∈ Wᶜ := hW.compl g⁻¹ (t, y) hx
  have hnot : (t, b.act g⁻¹ y) ∉ W := hmem
  rw [hF _ hnot, map_zero]

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT
