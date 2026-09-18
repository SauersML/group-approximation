import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.WordEntries
import GroupApproximation.Leavitt.IntegralGeneration
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.ZMod.Basic

/-!
# The marked limit in `thm:general` (b)

`simple_kazhdan_sofic_group.tex`, `thm:general` (b), tex l.178–189, and the section
"Finite simple models", tex l.317–342.

> Suppose that there are maps `φ_k : R → M_{N_k}(𝔽₂)` with `φ_k(1) = I` such that `φ_k(S)`
> generates the ring `M_{N_k}(𝔽₂)`, and for all `r, r' ∈ R` and all large `k` […]
> `φ_k(r + r') = φ_k(r) + φ_k(r')` and `φ_k(r r') = φ_k(r) φ_k(r')`. Then for every `n ≥ 3`,
> `EL_n(R)`, marked by the `e_ij(s)` with `s ∈ S`, is an expander limit of the finite simple
> groups `SL_{nN_k}(𝔽₂)` marked by the `e_ij(φ_k(s))`.

This file proves the *marked-limit* part of the conclusion, with the finite models written as
`EL_n(M_{N_k}(𝔽₂))`, from the simplicity of `EL_n(R)` (`thm:general` (a)):

* forward: a word trivial in `EL_n(R)` is trivial in the models for large `k`
  (`WordEntries.lean`);
* converse: `G` is simple, so `e_12(1)` is a product of conjugates of `w^{±1}`; this relation
  holds in the models for large `k`, where `e_12(I) ≠ I`.

The ring `R` is arbitrary here. The printed statement uses only that `S ∋ 1` generates `R` and
that `EL_n(R)` is simple.

**Convention.** The printed statement calls `SL_{nN_k}(𝔽₂)` *finite simple groups*, so it
implicitly assumes `N_k ≥ 1`. This assumption is necessary. With `N_k = 0` the hypotheses on
`φ_k` hold trivially, but `SL_0(𝔽₂)` is trivial, and the converse fails. It is recorded as the
hypothesis `hN : ∀ k, 0 < N k`.
-/

namespace GroupApproximation.Full.SK04

open Filter

/-- The printed hypotheses of `thm:general` (b) on the maps `φ_k : R → M_{N_k}(𝔽₂)`:
`φ_k(1) = I`, `φ_k(S)` generates the ring `M_{N_k}(𝔽₂)`, and for all `r, r'` and all large `k`
the map `φ_k` is additive and multiplicative on `r, r'`. -/
def IsPrintedMatricial {R : Type*} [Ring R] (S : Finset R) (N : ℕ → ℕ)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) : Prop :=
  (∀ k, φ k 1 = 1) ∧ (∀ k, Subring.closure (φ k '' (S : Set R)) = ⊤) ∧
    ∀ r r' : R, ∀ᶠ k in atTop,
      φ k (r + r') = φ k r + φ k r' ∧ φ k (r * r') = φ k r * φ k r'

/-- The marking alphabet of `thm:general` (b): the `e_ij(s)` with `i ≠ j` and `s ∈ S`. -/
abbrev MarkingIndex {R : Type*} (n : ℕ) (S : Finset R) : Type _ :=
  {p : Fin n × Fin n // p.1 ≠ p.2} × S

/-- The marking of `EL_n(R)` by the `e_ij(s)`, `s ∈ S`. -/
def elementaryMarking {R : Type*} [Ring R] (n : ℕ) (S : Finset R) :
    MarkingIndex n S → elementaryGroup (Fin n) R :=
  fun p => ⟨elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (p.2 : R),
    elementaryUnit_mem p.1.1.1 p.1.1.2 p.1.2 (p.2 : R)⟩

/-- The marking of the finite model `EL_n(M_{N_k}(𝔽₂))` by the `e_ij(φ_k(s))`, `s ∈ S`. -/
def matricialMarking {R : Type*} [Ring R] (n : ℕ) (S : Finset R) (N : ℕ → ℕ)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (k : ℕ) :
    MarkingIndex n S → elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :=
  fun p => ⟨elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (φ k (p.2 : R)),
    elementaryUnit_mem p.1.1.1 p.1.1.2 p.1.2 (φ k (p.2 : R))⟩

/-- Evaluating a word in a subgroup commutes with the inclusion. -/
theorem coe_lift {α G : Type*} [Group G] {K : Subgroup G} (t : α → K) (w : FreeGroup α) :
    ((FreeGroup.lift t w : K) : G) = FreeGroup.lift (fun x => (t x : G)) w := by
  induction w using FreeGroup.induction_on with
  | C1 => rw [map_one, map_one, Subgroup.coe_one]
  | of x => rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  | inv_of x hx => rw [map_inv, map_inv, Subgroup.coe_inv, hx]
  | mul x y hx hy => rw [map_mul, map_mul, Subgroup.coe_mul, hx, hy]

/-- If `T ∋ 1` generates `R` as a ring and a subgroup contains every `e_ij(a)` with `a ∈ T`,
then it contains `EL_n(R)` (`n ≥ 3`): sums, negatives and, through the Steinberg commutator,
products of admissible coefficients are admissible. -/
theorem elementaryGroup_le_of_generators {R : Type*} [Ring R] {n : ℕ} (hn : 2 < n)
    (T : Set R) (h1 : (1 : R) ∈ T) (hT : Subring.closure T = ⊤)
    (K : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hK : ∀ (i j : Fin n) (h : i ≠ j) (a : R), a ∈ T → elementaryUnit i j h a ∈ K) :
    elementaryGroup (Fin n) R ≤ K := by
  have hsub : T ⊆ (elementaryCoefficientSubring n hn K (fun i j h => hK i j h 1 h1) : Set R) := by
    intro a ha i j h
    exact hK i j h a ha
  have hall : ∀ a : R, a ∈ elementaryCoefficientSubring n hn K (fun i j h => hK i j h 1 h1) := by
    intro a
    have ha : a ∈ Subring.closure T := by
      rw [hT]
      exact Subring.mem_top a
    exact Subring.closure_le.mpr hsub ha
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, h, a, rfl⟩
  exact hall a i j h

/-- A family of elements of `EL_n(R)` taking every value `e_ij(a)` with `a` in a ring generating
set `T ∋ 1` generates `EL_n(R)`. -/
theorem closure_range_eq_top_of_generators {R : Type*} [Ring R] {n : ℕ} (hn : 2 < n)
    {α : Type*} (t : α → elementaryGroup (Fin n) R)
    (T : Set R) (h1 : (1 : R) ∈ T) (hT : Subring.closure T = ⊤)
    (hvals : ∀ (i j : Fin n) (h : i ≠ j) (a : R), a ∈ T →
      ∃ x, ((t x : elementaryGroup (Fin n) R) : (Matrix (Fin n) (Fin n) R)ˣ) =
        elementaryUnit i j h a) :
    Subgroup.closure (Set.range t) = ⊤ := by
  have hle : elementaryGroup (Fin n) R ≤
      (Subgroup.closure (Set.range t)).map (elementaryGroup (Fin n) R).subtype := by
    refine elementaryGroup_le_of_generators hn T h1 hT _ ?_
    intro i j h a ha
    obtain ⟨x, hx⟩ := hvals i j h a ha
    exact Subgroup.mem_map.mpr ⟨t x, Subgroup.subset_closure (Set.mem_range_self x), hx⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp (hle g.2)
  have hg : g' = g := Subtype.ext hgg'
  rw [← hg]
  exact hg'

/-- **The converse half of the printed marked-limit argument** (tex l.317–342), for any simple
marked group. Suppose the marking generates, words trivial in `G` are eventually trivial in the
models, and some marker stays nontrivial in every model. Then words nontrivial in `G` are
eventually nontrivial in the models. The proof is the printed one: the marker is a product of
conjugates of `w^{±1}`, and this relation eventually holds in the models. -/
theorem eventually_lift_ne_one {α G : Type*} [Group G] [IsSimpleGroup G] (s : α → G)
    {H : ℕ → Type*} [∀ k, Group (H k)] (σ : ∀ k, α → H k)
    (hs : Subgroup.closure (Set.range s) = ⊤)
    (hfwd : ∀ w : FreeGroup α, FreeGroup.lift s w = 1 →
      ∀ᶠ k in atTop, FreeGroup.lift (σ k) w = 1)
    (i₀ : α) (hi₀ : ∀ k, σ k i₀ ≠ 1) (w : FreeGroup α) (hw : FreeGroup.lift s w ≠ 1) :
    ∀ᶠ k in atTop, FreeGroup.lift (σ k) w ≠ 1 := by
  have hsurj : Function.Surjective (FreeGroup.lift s) := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
    exact hs
  have htop : (Subgroup.normalClosure ({w} : Set (FreeGroup α))).map (FreeGroup.lift s) = ⊤ := by
    rw [Subgroup.map_normalClosure _ _ hsurj, Set.image_singleton]
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({FreeGroup.lift s w} : Set G)) inferInstance).resolve_left ?_
    intro hbot
    apply hw
    have hmem : FreeGroup.lift s w ∈ Subgroup.normalClosure ({FreeGroup.lift s w} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton _)
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hmem : s i₀ ∈ (Subgroup.normalClosure ({w} : Set (FreeGroup α))).map (FreeGroup.lift s) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, hus⟩ := Subgroup.mem_map.mp hmem
  have hv : FreeGroup.lift s ((FreeGroup.of i₀)⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, FreeGroup.lift_apply_of, hus, inv_mul_cancel]
  filter_upwards [hfwd _ hv] with k hk hwk
  have hle : Subgroup.normalClosure ({w} : Set (FreeGroup α)) ≤ (FreeGroup.lift (σ k)).ker :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr hwk))
  have hu1 : FreeGroup.lift (σ k) u = 1 := MonoidHom.mem_ker.mp (hle hu)
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, hu1, mul_one, inv_eq_one] at hk
  exact hi₀ k hk

/-- **`thm:general` (b), marked-limit part** (`simple_kazhdan_sofic_group.tex`, tex l.178–189 and
l.317–342). Let `S ∋ 1` generate the ring `R`, let `n ≥ 3`, and let `EL_n(R)` be simple
(`thm:general` (a)). Let the maps `φ_k : R → M_{N_k}(𝔽₂)` satisfy the printed hypotheses, with
`N_k ≥ 1`. Then `EL_n(R)`, marked by the `e_ij(s)`, is the marked limit of the finite models
`EL_n(M_{N_k}(𝔽₂))` marked by the `e_ij(φ_k(s))`. -/
theorem isMarkedLimit_matricial {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n)
    [IsSimpleGroup (elementaryGroup (Fin n) R)]
    (S : Finset R) (hS1 : (1 : R) ∈ S) (hS : Subring.closure (S : Set R) = ⊤)
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (hφ : IsPrintedMatricial S N φ) :
    SimpleKazhdanSofic.IsMarkedLimit (elementaryMarking n S) (matricialMarking n S N φ) := by
  obtain ⟨hone, hgen, hring⟩ := hφ
  have hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r' :=
    fun r r' => (hring r r').mono fun _ h => h.1
  have hmul : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r * r') = φ k r * φ k r' :=
    fun r r' => (hring r r').mono fun _ h => h.2
  have hn2 : 2 < n := by omega
  have hsrc : Subgroup.closure (Set.range (elementaryMarking n S)) = ⊤ := by
    refine closure_range_eq_top_of_generators hn2 (elementaryMarking n S) (S : Set R)
      (Finset.mem_coe.mpr hS1) hS ?_
    intro i j h a ha
    exact ⟨(⟨(i, j), h⟩, ⟨a, Finset.mem_coe.mp ha⟩), rfl⟩
  have htgt : ∀ k, Subgroup.closure (Set.range (matricialMarking n S N φ k)) = ⊤ := by
    intro k
    refine closure_range_eq_top_of_generators hn2 (matricialMarking n S N φ k)
      (φ k '' (S : Set R)) ?_ (hgen k) ?_
    · rw [← hone k]
      exact Set.mem_image_of_mem (φ k) (Finset.mem_coe.mpr hS1)
    · intro i j h a ha
      obtain ⟨s, hs, rfl⟩ := ha
      exact ⟨(⟨(i, j), h⟩, ⟨s, Finset.mem_coe.mp hs⟩), rfl⟩
  have hfwd : ∀ w : FreeGroup (MarkingIndex n S),
      FreeGroup.lift (elementaryMarking n S) w = 1 →
        ∀ᶠ k in atTop, FreeGroup.lift (matricialMarking n S N φ k) w = 1 := by
    intro w hw
    have hw' : FreeGroup.lift (fun x => ((elementaryMarking n S x : elementaryGroup (Fin n) R) :
        (Matrix (Fin n) (Fin n) R)ˣ)) w = 1 := by
      rw [← coe_lift (elementaryMarking n S) w, hw, Subgroup.coe_one]
    filter_upwards [eventually_lift_eq_one φ hadd hmul hone
      (fun x => ((elementaryMarking n S x : elementaryGroup (Fin n) R) :
        (Matrix (Fin n) (Fin n) R)ˣ))
      (fun k x => ((matricialMarking n S N φ k x :
          elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) :
        (Matrix (Fin n) (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))ˣ))
      (fun x => eventually_entries_elementaryUnit φ hadd hone x.1.1.1 x.1.1.2 x.1.2 (x.2 : R))
      (fun x => eventually_entries_elementaryUnit_inv φ hadd hone x.1.1.1 x.1.1.2 x.1.2
        (x.2 : R))
      w hw'] with k hk
    apply Subtype.ext
    rw [coe_lift, Subgroup.coe_one]
    exact hk
  obtain ⟨i₀, j₀, h₀⟩ : ∃ i j : Fin n, i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => Nat.zero_ne_one (congrArg Fin.val h)⟩
  have hi₀ : ∀ k, matricialMarking n S N φ k (⟨(i₀, j₀), h₀⟩, ⟨1, hS1⟩) ≠ 1 := by
    intro k hk
    haveI : Nonempty (Fin (N k)) := ⟨⟨0, hN k⟩⟩
    have hval : elementaryUnit i₀ j₀ h₀ (φ k 1) =
        elementaryUnit (R := Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) i₀ j₀ h₀ 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val hk
    have h10 : (1 : Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) = 0 := by
      rw [← hone k]
      exact elementaryUnit_injective i₀ j₀ h₀ hval
    exact one_ne_zero h10
  refine ⟨hsrc, htgt, ?_⟩
  intro w
  by_cases hw : FreeGroup.lift (elementaryMarking n S) w = 1
  · filter_upwards [hfwd w hw] with k hk
    exact ⟨fun _ => hw, fun _ => hk⟩
  · filter_upwards [eventually_lift_ne_one (elementaryMarking n S) (matricialMarking n S N φ)
      hsrc hfwd (⟨(i₀, j₀), h₀⟩, ⟨1, hS1⟩) hi₀ w hw] with k hk
    exact ⟨fun h => absurd h hk, fun h => absurd h hw⟩

end GroupApproximation.Full.SK04
