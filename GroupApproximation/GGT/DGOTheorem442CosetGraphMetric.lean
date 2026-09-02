import GroupApproximation.GGT.DGOTheorem442CosetGraphBase

/-!
# Comparing a coset graph with its relative word metric

For the edge-defined relative generating set, projection `g |-> gH` changes
distance by at most one.  One inequality projects a relative word to the graph;
the other lifts a shortest graph walk and uses its single terminal peripheral
letter.  This is the metric comparison used in the proof of DGO Theorem 4.42.
-/

namespace GroupApproximation
namespace GGT
namespace CosetGraph

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- A preconnected coset graph is connected because its vertex type contains
the identity coset. -/
theorem connected_of_preconnected (H : Subgroup G)
    (Gamma : SimpleGraph (G ⧸ H)) (hconn : Gamma.Preconnected) :
    Gamma.Connected where
  preconnected := hconn
  nonempty := ⟨QuotientGroup.mk 1⟩

/-- Multiplication by one relative letter changes the projected coset by graph
distance at most one. -/
theorem dist_mk_mul_le_one
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) {a z : G}
    (hz : z ∈ (relGenSet H Gamma hinv hconn).alphabet.carrier) :
    Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk (a * z)) ≤ 1 := by
  rw [relGenSet_alphabet_carrier] at hz
  rcases hz with hzBase | hzH
  · have hbase : Gamma.Adj (QuotientGroup.mk 1) (QuotientGroup.mk z) := hzBase
    have htranslated :=
      (hinv a (QuotientGroup.mk 1) (QuotientGroup.mk z)).mpr hbase
    have hadj : Gamma.Adj (QuotientGroup.mk a) (QuotientGroup.mk (a * z)) := by
      simpa using htranslated
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
  · have heq : (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk (a * z) := by
      apply QuotientGroup.eq.mpr
      simpa using hzH
    rw [heq]
    simp

/-- Projecting a relative word to the coset graph costs at most one graph edge
per letter. -/
theorem dist_mk_mul_prod_le_length
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) (a : G) :
    ∀ (l : List G),
      (∀ z ∈ l, z ∈ (relGenSet H Gamma hinv hconn).alphabet.carrier) →
      Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk (a * l.prod)) ≤
        l.length := by
  intro l
  induction l generalizing a with
  | nil =>
      intro _hletters
      simp
  | cons z l ih =>
      intro hletters
      have hz := hletters z (by simp)
      have hl : ∀ w ∈ l,
          w ∈ (relGenSet H Gamma hinv hconn).alphabet.carrier := by
        intro w hw
        exact hletters w (List.mem_cons_of_mem z hw)
      have hstep := dist_mk_mul_le_one H Gamma hinv hconn (a := a) hz
      have htail := ih (a * z) hl
      have htriangle :=
        (connected_of_preconnected H Gamma hconn).dist_triangle
          (u := QuotientGroup.mk a) (v := QuotientGroup.mk (a * z))
          (w := QuotientGroup.mk ((a * z) * l.prod))
      simp only [List.prod_cons, List.length_cons]
      have hend : a * (z * l.prod) = (a * z) * l.prod := by group
      rw [hend]
      omega

/-- Projection to the coset graph is one-Lipschitz for the relative word
metric. -/
theorem graph_dist_le_wordDist
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) (a b : G) :
    Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk b) ≤
      wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b := by
  let D := relGenSet H Gamma hinv hconn
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq D.alphabet.symmetricGenerating (a⁻¹ * b)
  have hproject := dist_mk_mul_prod_le_length H Gamma hinv hconn a l hl.letters
  have hend : a * l.prod = b := by
    rw [hl.prod_eq]
    group
  rw [hend, hlen] at hproject
  exact hproject

/-- Lifting a shortest graph walk gives the reverse comparison, with the one
terminal peripheral letter from `exists_word_of_walk`. -/
theorem wordDist_le_graph_dist_add_one
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) (a b : G) :
    wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ≤
      Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk b) + 1 := by
  obtain ⟨p, hp⟩ :=
    (connected_of_preconnected H Gamma hconn).exists_walk_length_eq_dist
      (QuotientGroup.mk a) (QuotientGroup.mk b)
  have hword := wordDist_le_walk_length_add_one H Gamma hinv hconn p a b rfl rfl
  rw [hp] at hword
  exact hword

/-- The two integer-valued metrics differ by at most one. -/
theorem wordDist_graph_dist_bounds
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hconn : Gamma.Preconnected) (a b : G) :
    Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk b) ≤
        wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ∧
      wordDist (relGenSet H Gamma hinv hconn).alphabet.carrier a b ≤
        Gamma.dist (QuotientGroup.mk a) (QuotientGroup.mk b) + 1 :=
  ⟨graph_dist_le_wordDist H Gamma hinv hconn a b,
    wordDist_le_graph_dist_add_one H Gamma hinv hconn a b⟩

end CosetGraph
end GGT
end GroupApproximation
