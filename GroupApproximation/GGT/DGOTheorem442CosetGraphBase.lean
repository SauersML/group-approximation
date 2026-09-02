import Mathlib.Combinatorics.SimpleGraph.Metric
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# Relative generators from a connected coset graph

Let a group act on its left-coset space and let `Gamma` be a connected graph
whose adjacency relation is invariant under that action.  The elements taking
the identity coset across one edge form a symmetric relative generating set.

This is the generating-set construction in Dahmani--Guirardel--Osin's proof of
Theorem 4.42.  The main estimates say that projection to the coset graph does
not increase word distance, while a graph walk lifts to a relative word with
only one additional peripheral letter at its terminal coset.
-/

namespace GroupApproximation
namespace GGT
namespace CosetGraph

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- Elements taking the identity coset across an edge of `Gamma`. -/
def base (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H)) : Set G :=
  {g | Gamma.Adj (QuotientGroup.mk 1) (QuotientGroup.mk g)}

@[simp] theorem mem_base_iff (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (g : G) :
    g ∈ base H Gamma ↔
      Gamma.Adj (QuotientGroup.mk 1) (QuotientGroup.mk g) :=
  Iff.rfl

/-- Translating an edge between represented cosets back to the identity coset
makes the difference of the representatives a base letter. -/
theorem mem_base_of_adj_mk (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {a b : G} (hab : Gamma.Adj (QuotientGroup.mk a) (QuotientGroup.mk b)) :
    a⁻¹ * b ∈ base H Gamma := by
  have htranslated := (hinv a⁻¹ (QuotientGroup.mk a) (QuotientGroup.mk b)).mpr hab
  change Gamma.Adj (QuotientGroup.mk 1) (QuotientGroup.mk (a⁻¹ * b))
  simpa using htranslated

/-- The edge-defined base is closed under inversion. -/
theorem inv_mem_base (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {g : G} (hg : g ∈ base H Gamma) :
    g⁻¹ ∈ base H Gamma := by
  have htranslated :=
    (hinv g⁻¹ (QuotientGroup.mk 1) (QuotientGroup.mk g)).mpr hg
  have hreverse := htranslated.symm
  change Gamma.Adj (QuotientGroup.mk 1) (QuotientGroup.mk g⁻¹)
  simpa using hreverse

/-- A fixed representative of a left coset. -/
noncomputable def representative (H : Subgroup G) (q : G ⧸ H) : G :=
  Classical.choose (QuotientGroup.mk_surjective q)

@[simp] theorem mk_representative (H : Subgroup G) (q : G ⧸ H) :
    QuotientGroup.mk (representative H q) = q :=
  Classical.choose_spec (QuotientGroup.mk_surjective q)

/-- A graph walk from `aH` to `bH` spells `a⁻¹b` by one base letter per
edge and one final `H`-letter. -/
theorem exists_word_of_walk (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    {A B : G ⧸ H} (p : Gamma.Walk A B) (a b : G)
    (ha : QuotientGroup.mk a = A) (hb : QuotientGroup.mk b = B) :
    ∃ l : List G,
      IsWord (base H Gamma ∪ (H : Set G)) l (a⁻¹ * b) ∧
        l.length ≤ p.length + 1 := by
  induction p generalizing a b with
  | nil =>
      have habCoset : QuotientGroup.mk a = QuotientGroup.mk b := ha.trans hb.symm
      have habH : a⁻¹ * b ∈ H := QuotientGroup.eq.mp habCoset
      refine ⟨[a⁻¹ * b], ?_, by simp⟩
      exact isWord_singleton (Set.mem_union_right _ habH)
  | @cons A C B hAC p ih =>
      let c : G := representative H C
      have hc : QuotientGroup.mk c = C := mk_representative H C
      have hAC' : Gamma.Adj (QuotientGroup.mk a) (QuotientGroup.mk c) := by
        rw [ha, hc]
        exact hAC
      have hacBase : a⁻¹ * c ∈ base H Gamma :=
        mem_base_of_adj_mk H Gamma hinv hAC'
      obtain ⟨l, hl, hlen⟩ := ih c b hc hb
      refine ⟨(a⁻¹ * c) :: l, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with hxa | hxl
          · subst x
            exact Set.mem_union_left _ hacBase
          · exact hl.letters x hxl
        · simp only [List.prod_cons, hl.prod_eq]
          group
      · simp only [List.length_cons, SimpleGraph.Walk.length_cons]
        omega

/-- The relative generating set supplied by an invariant connected coset
graph. -/
noncomputable def relGenSet (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) : RelGenSet G Unit where
  base := base H Gamma
  fam := fun _ => H
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Set.mem_union_left _ (inv_mem_base H Gamma hinv hx)
      · rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, H.inv_mem hi⟩)
    · rw [eq_top_iff]
      intro g _hg
      obtain ⟨p⟩ := hconn (QuotientGroup.mk 1) (QuotientGroup.mk g)
      obtain ⟨l, hl, _hlen⟩ := exists_word_of_walk H Gamma hinv p 1 g rfl rfl
      have hsub : base H Gamma ∪ (H : Set G) ⊆
          base H Gamma ∪ ⋃ _i : Unit, (H : Set G) := by
        intro x hx
        rcases hx with hx | hx
        · exact Set.mem_union_left _ hx
        · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨(), hx⟩)
      have hword : IsWord (base H Gamma ∪ ⋃ _i : Unit, (H : Set G)) l g := by
        refine ⟨fun x hx ↦ hsub (hl.letters x hx), ?_⟩
        simpa using hl.prod_eq
      rw [← hword.prod_eq]
      exact Subgroup.list_prod_mem _ fun x hx ↦
        Subgroup.subset_closure (hword.letters x hx)

@[simp] theorem relGenSet_base (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (relGenSet H Gamma hinv hconn).base = base H Gamma :=
  rfl

@[simp] theorem relGenSet_fam (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (relGenSet H Gamma hinv hconn).fam = fun _ => H :=
  rfl

@[simp] theorem relGenSet_alphabet_carrier
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) :
    (relGenSet H Gamma hinv hconn).alphabet.carrier =
      base H Gamma ∪ (H : Set G) := by
  change base H Gamma ∪ ⋃ _i : Unit, (H : Set G) =
    base H Gamma ∪ (H : Set G)
  ext x
  simp

/-- A represented graph edge changes the relative word metric by at most one. -/
theorem wordDist_le_one_of_adj_mk
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {a b : G}
    (hab : Gamma.Adj (QuotientGroup.mk a) (QuotientGroup.mk b)) :
    wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ≤ 1 := by
  change wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier (a⁻¹ * b) ≤ 1
  apply wordNorm_le_one_of_mem
  rw [relGenSet_alphabet_carrier]
  exact Set.mem_union_left _ (mem_base_of_adj_mk H Gamma hinv hab)

/-- Two representatives of the same coset differ by one peripheral letter. -/
theorem wordDist_le_one_of_mk_eq
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {a b : G}
    (hab : (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b) :
    wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ≤ 1 := by
  change wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier (a⁻¹ * b) ≤ 1
  apply wordNorm_le_one_of_mem
  rw [relGenSet_alphabet_carrier]
  exact Set.mem_union_right _ (QuotientGroup.eq.mp hab)

/-- A graph walk gives the converse distance estimate with one terminal
peripheral letter. -/
theorem wordDist_le_walk_length_add_one
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {A B : G ⧸ H}
    (p : Gamma.Walk A B) (a b : G)
    (ha : QuotientGroup.mk a = A) (hb : QuotientGroup.mk b = B) :
    wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ≤
      p.length + 1 := by
  obtain ⟨l, hl, hlen⟩ := exists_word_of_walk H Gamma hinv p a b ha hb
  change wordNorm (relGenSet H Gamma hinv hconn).alphabet.carrier (a⁻¹ * b) ≤
    p.length + 1
  apply le_trans (wordNorm_le_length ?_) hlen
  rw [relGenSet_alphabet_carrier]
  exact hl

end CosetGraph
end GGT
end GroupApproximation
