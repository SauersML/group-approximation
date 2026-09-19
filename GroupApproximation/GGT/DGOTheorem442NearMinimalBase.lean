import GroupApproximation.GGT.DGOTheorem442CosetGraphBase
import GroupApproximation.GGT.DGOTheorem442ProjectionDiameter

/-!
# Near-minimal double-coset generators for DGO Theorem 4.42

For every edge from the identity coset in the projection graph, DGO section
4.5 chooses a representative whose displacement is within `kappa` of the
infimum over its `H`-double coset.  It is equivalent, and avoids a choice
function, to take all representatives satisfying that estimate.

This file proves that the resulting base is symmetric and relatively
generates the group.  Every graph edge expands into three relative letters:
an `H`-letter, one near-minimal base letter, and another `H`-letter.
-/

namespace GroupApproximation
namespace GGT
namespace CosetGraph

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- The orbit-point set of the double coset `H g H`. -/
def doubleCosetOrbitAt (H : Subgroup G) (s : S) (g : G) : Set S :=
  {x | ∃ h₁ : G, h₁ ∈ H ∧ ∃ h₂ : G, h₂ ∈ H ∧
    (h₁ * g * h₂) • s = x}

omit [PseudoMetricSpace S] in
@[simp] theorem mem_doubleCosetOrbitAt_iff
    (H : Subgroup G) (s : S) (g : G) (x : S) :
    x ∈ doubleCosetOrbitAt H s g ↔
      ∃ h₁ : G, h₁ ∈ H ∧ ∃ h₂ : G, h₂ ∈ H ∧
        (h₁ * g * h₂) • s = x :=
  Iff.rfl

/-- A group element is within `kappa` of least displacement in its own
`H`-double coset.  This is the representative estimate in DGO section 4.5. -/
def IsDoubleCosetNearMinimal
    (H : Subgroup G) (s : S) (kappa : ℝ) (g : G) : Prop :=
  ∀ h₁ : G, h₁ ∈ H → ∀ h₂ : G, h₂ ∈ H →
    dist s (g • s) ≤ dist s ((h₁ * g * h₂) • s) + kappa

/-- With the trivial peripheral, every element is an exact double-coset
minimum.  This tests the near-minimality predicate on a nonempty model. -/
theorem isDoubleCosetNearMinimal_trivialModel
    (s : S) {kappa : ℝ} (hkappa : 0 ≤ kappa) (g : G) :
    IsDoubleCosetNearMinimal (⊥ : Subgroup G) s kappa g := by
  intro h₁ hh₁ h₂ hh₂
  have hh₁' : h₁ = 1 := Subgroup.mem_bot.mp hh₁
  have hh₂' : h₂ = 1 := Subgroup.mem_bot.mp hh₂
  subst h₁
  subst h₂
  simpa using (show dist s (g • s) ≤ dist s (g • s) + kappa by linarith)

/-- In an isometric action, an element and its inverse move the basepoint by
the same distance. -/
theorem dist_self_inv_smul_eq
    (hiso : IsIsometricAction G S) (s : S) (g : G) :
    dist s (g⁻¹ • s) = dist s (g • s) := by
  have h := hiso g s (g⁻¹ • s)
  simpa only [smul_inv_smul, dist_comm] using h.symm

/-- Near-minimality in a double coset is preserved by inversion. -/
theorem isDoubleCosetNearMinimal_inv
    (hiso : IsIsometricAction G S) (H : Subgroup G) (s : S)
    {kappa : ℝ} {g : G} (hg : IsDoubleCosetNearMinimal H s kappa g) :
    IsDoubleCosetNearMinimal H s kappa g⁻¹ := by
  intro h₁ hh₁ h₂ hh₂
  have hbound := hg h₂⁻¹ (H.inv_mem hh₂) h₁⁻¹ (H.inv_mem hh₁)
  calc
    dist s (g⁻¹ • s) = dist s (g • s) := dist_self_inv_smul_eq hiso s g
    _ ≤ dist s ((h₂⁻¹ * g * h₁⁻¹) • s) + kappa := hbound
    _ = dist s ((h₁ * g⁻¹ * h₂) • s) + kappa := by
      have heq : (h₁ * g⁻¹ * h₂)⁻¹ = h₂⁻¹ * g * h₁⁻¹ := by group
      rw [← heq, dist_self_inv_smul_eq hiso s (h₁ * g⁻¹ * h₂)]

/-- Every double coset has a near-minimal representative for a positive
error. -/
theorem exists_isDoubleCosetNearMinimal
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa) (g : G) :
    ∃ x : G, (∃ h₁ : G, h₁ ∈ H ∧ ∃ h₂ : G, h₂ ∈ H ∧
      x = h₁ * g * h₂) ∧ IsDoubleCosetNearMinimal H s kappa x := by
  have hnonempty : (doubleCosetOrbitAt H s g).Nonempty := by
    refine ⟨g • s, 1, H.one_mem, 1, H.one_mem, ?_⟩
    simp
  obtain ⟨p, hp⟩ :=
    Elementary.exists_isApproxProjectionTo (doubleCosetOrbitAt H s g) s
      hnonempty hkappa
  obtain ⟨h₁, hh₁, h₂, hh₂, hpEq⟩ := hp.1
  let x : G := h₁ * g * h₂
  refine ⟨x, ⟨h₁, hh₁, h₂, hh₂, rfl⟩, ?_⟩
  intro k₁ hk₁ k₂ hk₂
  have hcand : (k₁ * x * k₂) • s ∈ doubleCosetOrbitAt H s g := by
    refine ⟨k₁ * h₁, H.mul_mem hk₁ hh₁,
      h₂ * k₂, H.mul_mem hh₂ hk₂, ?_⟩
    dsimp only [x]
    congr 1
    group
  have hnear := hp.2 ((k₁ * x * k₂) • s) hcand
  dsimp only [x]
  rw [hpEq]
  exact hnear

/-- The DGO base consists of near-minimal representatives of graph edges
leaving the identity coset. -/
def nearMinimalBase
    (H : Subgroup G) (s : S) (kappa : ℝ)
    (Gamma : SimpleGraph (G ⧸ H)) : Set G :=
  {g | g ∈ base H Gamma ∧ IsDoubleCosetNearMinimal H s kappa g}

@[simp] theorem mem_nearMinimalBase_iff
    (H : Subgroup G) (s : S) (kappa : ℝ)
    (Gamma : SimpleGraph (G ⧸ H)) (g : G) :
    g ∈ nearMinimalBase H s kappa Gamma ↔
      g ∈ base H Gamma ∧ IsDoubleCosetNearMinimal H s kappa g :=
  Iff.rfl

/-- The near-minimal base is contained in the full edge base. -/
theorem nearMinimalBase_subset_base
    (H : Subgroup G) (s : S) (kappa : ℝ)
    (Gamma : SimpleGraph (G ⧸ H)) :
    nearMinimalBase H s kappa Gamma ⊆ base H Gamma :=
  fun _ hg ↦ hg.1

/-- Double-coset multiplication by subgroup elements preserves adjacency from
the identity coset. -/
theorem mem_base_of_mem_doubleCoset
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {g x : G} (hg : g ∈ base H Gamma)
    (hx : ∃ h₁ : G, h₁ ∈ H ∧ ∃ h₂ : G, h₂ ∈ H ∧
      x = h₁ * g * h₂) :
    x ∈ base H Gamma := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hx
  have htranslated :=
    (hinv h₁ (QuotientGroup.mk 1) (QuotientGroup.mk g)).mpr hg
  have hh₁Coset : (QuotientGroup.mk h₁ : G ⧸ H) = QuotientGroup.mk 1 := by
    apply QuotientGroup.eq.mpr
    simpa using H.inv_mem hh₁
  have hrightCoset : (QuotientGroup.mk (h₁ * g * h₂) : G ⧸ H) =
      QuotientGroup.mk (h₁ * g) := by
    apply QuotientGroup.eq.mpr
    have heq : (h₁ * g * h₂)⁻¹ * (h₁ * g) = h₂⁻¹ := by group
    rw [heq]
    exact H.inv_mem hh₂
  change Gamma.Adj (QuotientGroup.mk 1)
    (QuotientGroup.mk (h₁ * g * h₂))
  have htranslated' : Gamma.Adj (QuotientGroup.mk h₁)
      (QuotientGroup.mk (h₁ * g)) := by
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using htranslated
  rw [hh₁Coset, ← hrightCoset] at htranslated'
  exact htranslated'

/-- Every full edge-base letter has a near-minimal representative in its
double coset. -/
theorem exists_nearMinimalBase_doubleCoset
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {g : G} (hg : g ∈ base H Gamma) :
    ∃ x : G, x ∈ nearMinimalBase H s kappa Gamma ∧
      ∃ h₁ : G, h₁ ∈ H ∧ ∃ h₂ : G, h₂ ∈ H ∧
        x = h₁ * g * h₂ := by
  obtain ⟨x, hxDouble, hxNear⟩ :=
    exists_isDoubleCosetNearMinimal H s hkappa g
  exact ⟨x, ⟨mem_base_of_mem_doubleCoset H Gamma hinv hg hxDouble,
    hxNear⟩, hxDouble⟩

/-- The near-minimal edge base is closed under inversion. -/
theorem inv_mem_nearMinimalBase
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (kappa : ℝ)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {g : G} (hg : g ∈ nearMinimalBase H s kappa Gamma) :
    g⁻¹ ∈ nearMinimalBase H s kappa Gamma :=
  ⟨inv_mem_base H Gamma hinv hg.1,
    isDoubleCosetNearMinimal_inv hiso H s hg.2⟩

/-- A graph walk lifts to the near-minimal relative alphabet, with three
letters per graph edge and one terminal peripheral letter. -/
theorem exists_nearMinimal_word_of_walk
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {A B : G ⧸ H} (p : Gamma.Walk A B) (a b : G)
    (ha : QuotientGroup.mk a = A) (hb : QuotientGroup.mk b = B) :
    ∃ l : List G,
      IsWord (nearMinimalBase H s kappa Gamma ∪ (H : Set G)) l (a⁻¹ * b) ∧
        l.length ≤ 3 * p.length + 1 := by
  induction p generalizing a b with
  | nil =>
      have habCoset : QuotientGroup.mk a = QuotientGroup.mk b := ha.trans hb.symm
      have habH : a⁻¹ * b ∈ H := QuotientGroup.eq.mp habCoset
      refine ⟨[a⁻¹ * b], isWord_singleton (Set.mem_union_right _ habH), by simp⟩
  | @cons A C B hAC p ih =>
      let c : G := representative H C
      have hc : QuotientGroup.mk c = C := mk_representative H C
      have hAC' : Gamma.Adj (QuotientGroup.mk a) (QuotientGroup.mk c) := by
        rw [ha, hc]
        exact hAC
      have hgBase : a⁻¹ * c ∈ base H Gamma :=
        mem_base_of_adj_mk H Gamma hinv hAC'
      obtain ⟨x, hxBase, h₁, hh₁, h₂, hh₂, hx⟩ :=
        exists_nearMinimalBase_doubleCoset H s hkappa Gamma hinv hgBase
      obtain ⟨l, hl, hlen⟩ := ih c b hc hb
      refine ⟨h₁⁻¹ :: x :: h₂⁻¹ :: l, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | rfl | rfl | hz
          · exact Set.mem_union_right _ (H.inv_mem hh₁)
          · exact Set.mem_union_left _ hxBase
          · exact Set.mem_union_right _ (H.inv_mem hh₂)
          · exact hl.letters z hz
        · simp only [List.prod_cons, hl.prod_eq]
          rw [hx]
          group
      · simp only [List.length_cons, SimpleGraph.Walk.length_cons]
        omega

/-- The relative generating set using DGO's near-minimal edge
representatives. -/
noncomputable def nearMinimalRelGenSet
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) : RelGenSet G Unit where
  base := nearMinimalBase H s kappa Gamma
  fam := fun _ ↦ H
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Set.mem_union_left _
          (inv_mem_nearMinimalBase hiso H s kappa Gamma hinv hx)
      · rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, H.inv_mem hi⟩)
    · rw [eq_top_iff]
      intro g _hg
      obtain ⟨p⟩ := hconn (QuotientGroup.mk 1) (QuotientGroup.mk g)
      obtain ⟨l, hl, _hlen⟩ :=
        exists_nearMinimal_word_of_walk H s hkappa Gamma hinv p 1 g rfl rfl
      have hsub : nearMinimalBase H s kappa Gamma ∪ (H : Set G) ⊆
          nearMinimalBase H s kappa Gamma ∪ ⋃ _i : Unit, (H : Set G) := by
        intro x hx
        rcases hx with hx | hx
        · exact Set.mem_union_left _ hx
        · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨(), hx⟩)
      have hword : IsWord
          (nearMinimalBase H s kappa Gamma ∪ ⋃ _i : Unit, (H : Set G)) l g := by
        refine ⟨fun x hx ↦ hsub (hl.letters x hx), ?_⟩
        simpa using hl.prod_eq
      rw [← hword.prod_eq]
      exact Subgroup.list_prod_mem _ fun x hx ↦
        Subgroup.subset_closure (hword.letters x hx)

@[simp] theorem nearMinimalRelGenSet_base
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).base =
      nearMinimalBase H s kappa Gamma :=
  rfl

@[simp] theorem nearMinimalRelGenSet_fam
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).fam = fun _ ↦ H :=
  rfl

@[simp] theorem nearMinimalRelGenSet_alphabet_carrier
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier =
      nearMinimalBase H s kappa Gamma ∪ (H : Set G) := by
  change nearMinimalBase H s kappa Gamma ∪ ⋃ _i : Unit, (H : Set G) =
    nearMinimalBase H s kappa Gamma ∪ (H : Set G)
  ext x
  simp

end CosetGraph
end GGT
end GroupApproximation
