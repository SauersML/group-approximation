import GroupApproximation.Algebra.HyperbolicQuasiIsometryInvariant
import GroupApproximation.Algebra.WordMetricComparison
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.DGOTheorem442NearMinimalBase

/-!
# Hyperbolicity for the near-minimal DGO generators

The full edge alphabet and the near-minimal alphabet define word metrics that
differ by a multiplicative factor at most three.  Indeed, a full edge letter
lies in the same double coset as a near-minimal representative, so it is a
product of an `H`-letter, that representative, and another `H`-letter.

The repository's proved quasi-isometry invariance theorem then transfers
hyperbolicity from the full-edge relative Cayley graph to the DGO relative
Cayley graph.  The theorem is stated at `Type`, which is the universe required
by `DGOTheorem442.{0,0}`.
-/

namespace GroupApproximation
namespace GGT
namespace CosetGraph

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- The near-minimal relative alphabet is contained in the full edge
alphabet. -/
theorem nearMinimal_alphabet_subset_full
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier ⊆
      (relGenSet H Gamma hinv hconn).alphabet.carrier := by
  rw [nearMinimalRelGenSet_alphabet_carrier,
    relGenSet_alphabet_carrier]
  intro g hg
  rcases hg with hg | hg
  · exact Set.mem_union_left _
      (nearMinimalBase_subset_base H s kappa Gamma hg)
  · exact Set.mem_union_right _ hg

/-- Every letter of the full edge alphabet has near-minimal word norm at most
three. -/
theorem nearMinimal_wordNorm_le_three_of_mem_full
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {g : G}
    (hg : g ∈ (relGenSet H Gamma hinv hconn).alphabet.carrier) :
    wordNorm
      (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier g ≤ 3 := by
  rw [relGenSet_alphabet_carrier] at hg
  let D := nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn
  rcases hg with hgBase | hgH
  · obtain ⟨x, hxBase, h₁, hh₁, h₂, hh₂, hx⟩ :=
      exists_nearMinimalBase_doubleCoset H s hkappa Gamma hinv hgBase
    have hword : IsWord D.alphabet.carrier [h₁⁻¹, x, h₂⁻¹] g := by
      refine ⟨?_, ?_⟩
      · intro z hz
        simp at hz
        rcases hz with rfl | rfl | rfl
        · rw [nearMinimalRelGenSet_alphabet_carrier]
          exact Set.mem_union_right _ (H.inv_mem hh₁)
        · rw [nearMinimalRelGenSet_alphabet_carrier]
          exact Set.mem_union_left _ hxBase
        · rw [nearMinimalRelGenSet_alphabet_carrier]
          exact Set.mem_union_right _ (H.inv_mem hh₂)
      · simp only [List.prod_cons, List.prod_nil, mul_one]
        rw [hx]
        group
    have hle := wordNorm_le_length hword
    change wordNorm D.alphabet.carrier g ≤ 3
    simpa only [List.length_cons, List.length_nil] using hle
  · have hmem : g ∈ D.alphabet.carrier := by
      rw [nearMinimalRelGenSet_alphabet_carrier]
      exact Set.mem_union_right _ hgH
    exact (wordNorm_le_one_of_mem hmem).trans (by omega)

/-- The near-minimal word norm is at most three times the full-edge word
norm. -/
theorem nearMinimal_wordNorm_le_three_mul_full
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) (g : G) :
    wordNorm
        (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier g ≤
      3 * wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier g := by
  let Dfull := relGenSet H Gamma hinv hconn
  let Dnear := nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq Dfull.alphabet.symmetricGenerating g
  have hbound : ∀ n ∈ l.map (wordNorm Dnear.alphabet.carrier), n ≤ 3 := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    apply nearMinimal_wordNorm_le_three_of_mem_full
      hiso H s hkappa Gamma hinv hconn
    exact hl.letters x hx
  calc
    wordNorm Dnear.alphabet.carrier g = wordNorm Dnear.alphabet.carrier l.prod := by
      rw [hl.prod_eq]
    _ ≤ (l.map (wordNorm Dnear.alphabet.carrier)).sum :=
      wordNorm_prod_le Dnear.alphabet.symmetricGenerating l
    _ ≤ (l.map (wordNorm Dnear.alphabet.carrier)).length * 3 :=
      sum_le_length_mul _ 3 hbound
    _ = 3 * wordNorm Dfull.alphabet.carrier g := by
      rw [List.length_map, hlen]
      omega

/-- The identity map is a `(3,0)` quasi-isometry from the full-edge word
metric to the near-minimal word metric. -/
theorem nearMinimal_isQuasiIsometry_full
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    Hyperbolic.IsQuasiIsometry
      (relGenSet H Gamma hinv hconn).alphabet.carrier
      (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier
      id 3 0 := by
  refine ⟨?_, ?_⟩
  · intro a b
    constructor
    · change wordNorm
          (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier
          (a⁻¹ * b) ≤
        3 * wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier
          (a⁻¹ * b) + 0
      simpa only [add_zero] using
        nearMinimal_wordNorm_le_three_mul_full
          hiso H s hkappa Gamma hinv hconn (a⁻¹ * b)
    · have hmono := wordNorm_mono
          (nearMinimal_alphabet_subset_full
            hiso H s hkappa Gamma hinv hconn)
          (wordLengths_nonempty
            (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.symmetricGenerating
            (a⁻¹ * b))
      change wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier (a⁻¹ * b) ≤
        3 * wordNorm
          (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet.carrier
          (a⁻¹ * b) + 0
      omega
  · intro y
    refine ⟨y, ?_⟩
    simp only [id_eq, wordDist_self]
    exact le_rfl

section UniverseZero

variable {G₀ : Type} [Group G₀] {S₀ : Type v} [PseudoMetricSpace S₀]
  [MulAction G₀ S₀]

/-- Hyperbolicity of the full-edge relative Cayley graph transfers to the
near-minimal DGO relative Cayley graph. -/
theorem exists_nearMinimalRelGenSet_hyperbolic_of_full
    (hiso : IsIsometricAction G₀ S₀)
    (H : Subgroup G₀) (s : S₀) {kappa : ℝ} (hkappa : 0 < kappa)
    (Gamma : SimpleGraph (G₀ ⧸ H))
    (hinv : ∀ (a : G₀) (A B : G₀ ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected)
    (hfull : ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (relGenSet H Gamma hinv hconn).alphabet)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley
        (nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn).alphabet) := by
  let Dfull := relGenSet H Gamma hinv hconn
  let Dnear := nearMinimalRelGenSet hiso H s hkappa Gamma hinv hconn
  obtain ⟨delta, hdelta⟩ := hfull
  have hfour : Hyperbolic.IsFourPointHyperbolic Dfull.alphabet.carrier ⌈delta⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley Dfull.alphabet hdelta
  have hqi : Hyperbolic.IsQuasiIsometry Dfull.alphabet.carrier
      Dnear.alphabet.carrier id 3 0 :=
    nearMinimal_isQuasiIsometry_full hiso H s hkappa Gamma hinv hconn
  obtain ⟨delta', hdelta'⟩ :=
    Hyperbolic.quasiIsometryInvariant G₀ G₀ inferInstance inferInstance
      Dfull.alphabet.carrier Dnear.alphabet.carrier id 3 0
      Dfull.alphabet.symmetricGenerating Dnear.alphabet.symmetricGenerating
      hqi ⟨⌈delta⌉₊, hfour⟩
  exact ⟨(delta' : ℝ),
    isHyperbolicSpace_cayley_of_fourPoint Dnear.alphabet hdelta'⟩

end UniverseZero

end CosetGraph
end GGT
end GroupApproximation
