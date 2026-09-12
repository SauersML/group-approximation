import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.DGOTheorem442BBFGuessingPaths
import GroupApproximation.GGT.HyperbolicAdditiveTransfer

/-!
# Hyperbolicity of the BBF projection graph

The lifted BBF standard walks satisfy Bowditch's guessing-path criterion in
the relative Cayley graph.  The representative map from the coset graph to
that Cayley graph changes every distance by at most one, so additive-distortion
transfer gives hyperbolicity of the projection graph itself.

This proves the hyperbolicity part of Bestvina--Bromberg--Fujiwara Theorem 3.16
in the form needed for DGO Theorem 4.42.
-/

namespace GroupApproximation
namespace GGT
namespace CosetGraph

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u v

/-! ## The real graph metric -/

/-- A connected graph regarded as a pseudo-metric space using its integer
graph distance cast to the reals. -/
def Space {V : Type v} (Gamma : SimpleGraph V) (_hconn : Gamma.Connected) := V

/-- A graph vertex regarded as a point of its graph-metric space. -/
def Space.of {V : Type v} {Gamma : SimpleGraph V} (hconn : Gamma.Connected)
    (x : V) : Space Gamma hconn := x

/-- The graph vertex naming a point of the graph-metric space. -/
def Space.val {V : Type v} {Gamma : SimpleGraph V} {hconn : Gamma.Connected}
    (x : Space Gamma hconn) : V := x

@[simp] theorem Space.val_of {V : Type v} {Gamma : SimpleGraph V}
    (hconn : Gamma.Connected) (x : V) :
    Space.val (Space.of hconn x) = x :=
  rfl

noncomputable instance instPseudoMetricSpaceSpace
    {V : Type v} {Gamma : SimpleGraph V} (hconn : Gamma.Connected) :
    PseudoMetricSpace (Space Gamma hconn) where
  dist x y := (Gamma.dist (Space.val x) (Space.val y) : ℝ)
  dist_self x := by
    show ((Gamma.dist (Space.val x) (Space.val x) : ℕ) : ℝ) = 0
    simp
  dist_comm x y := by
    show ((Gamma.dist (Space.val x) (Space.val y) : ℕ) : ℝ) =
      ((Gamma.dist (Space.val y) (Space.val x) : ℕ) : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show ((Gamma.dist (Space.val x) (Space.val z) : ℕ) : ℝ) ≤
      ((Gamma.dist (Space.val x) (Space.val y) : ℕ) : ℝ) +
        ((Gamma.dist (Space.val y) (Space.val z) : ℕ) : ℝ)
    exact_mod_cast hconn.dist_triangle (u := Space.val x)
      (v := Space.val y) (w := Space.val z)

@[simp] theorem Space.dist_eq {V : Type v} {Gamma : SimpleGraph V}
    {hconn : Gamma.Connected} (x y : Space Gamma hconn) :
    dist x y = (Gamma.dist (Space.val x) (Space.val y) : ℝ) :=
  rfl

@[simp] theorem Space.dist_of {V : Type v} {Gamma : SimpleGraph V}
    {hconn : Gamma.Connected} (x y : V) :
    dist (Space.of hconn x) (Space.of hconn y) = (Gamma.dist x y : ℝ) :=
  rfl

/-! ## Additive comparison with the relative Cayley graph -/

variable {G : Type u} [Group G] {H : Subgroup G}

/-- Choose a group representative for each coset and regard it as a Cayley
vertex. -/
noncomputable def representativeMap
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hpre : Gamma.Preconnected) :
    Space Gamma (connected_of_preconnected H Gamma hpre) →
      Cayley (relGenSet H Gamma hinv hpre).alphabet :=
  fun q ↦ Cayley.of _ (representative H (Space.val q))

/-- The representative map has additive distortion one. -/
theorem representativeMap_additiveDistortion
    (H : Subgroup G) (Gamma : SimpleGraph (G ⧸ H))
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      Gamma.Adj (a • A) (a • B) ↔ Gamma.Adj A B)
    (hpre : Gamma.Preconnected) :
    HasAdditiveDistortion 1 (representativeMap H Gamma hinv hpre) := by
  intro q r
  let a := representative H (Space.val q)
  let b := representative H (Space.val r)
  have ha : QuotientGroup.mk a = Space.val q := mk_representative H _
  have hb : QuotientGroup.mk b = Space.val r := mk_representative H _
  have hlower := graph_dist_le_wordDist H Gamma hinv hpre a b
  have hupper := wordDist_le_graph_dist_add_one H Gamma hinv hpre a b
  rw [abs_le]
  constructor
  · simp only [representativeMap, Cayley.dist_eq, Cayley.val_of, Space.dist_eq]
    change -1 ≤
      ((wordDist (relGenSet H Gamma hinv hpre).alphabet.carrier a b : ℕ) : ℝ) -
        (Gamma.dist (Space.val q) (Space.val r) : ℝ)
    rw [ha, hb] at hlower hupper
    have hlowerR : (Gamma.dist (Space.val q) (Space.val r) : ℝ) ≤
        (wordDist (relGenSet H Gamma hinv hpre).alphabet.carrier a b : ℝ) := by
      exact_mod_cast hlower
    linarith
  · simp only [representativeMap, Cayley.dist_eq, Cayley.val_of, Space.dist_eq]
    change
      ((wordDist (relGenSet H Gamma hinv hpre).alphabet.carrier a b : ℕ) : ℝ) -
        (Gamma.dist (Space.val q) (Space.val r) : ℝ) ≤ 1
    rw [ha, hb] at hlower hupper
    have hupperR :
        (wordDist (relGenSet H Gamma hinv hpre).alphabet.carrier a b : ℝ) ≤
          (Gamma.dist (Space.val q) (Space.val r) : ℝ) + 1 := by
      exact_mod_cast hupper
    linarith

/-! ## The BBF hyperbolicity conclusions -/

namespace Projection

/-- The relative Cayley graph of an equivariant BBF coset graph is
hyperbolic, by the lifted standard walks and Bowditch's criterion. -/
theorem exists_cayley_hyperbolic_of_bbf
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (relGenSet H ((ProjectionPerturbation.bbf P).graph K) hinv
        (P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos]))).alphabet) := by
  obtain ⟨delta, hfour⟩ := P.exists_fourPoint_of_bbf_coset_graph hK hinv
  exact ⟨delta, isHyperbolicSpace_cayley_of_fourPoint _ hfour⟩

/-- **BBF Theorem 3.16, hyperbolicity conclusion.**  The projection graph at
threshold at least `64 xi`, equipped with its graph metric, is hyperbolic. -/
theorem exists_graph_hyperbolic_of_bbf
    (P : ProjectionSystem (G ⧸ H)) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    (hinv : ∀ (a : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P).graph K).Adj (a • A) (a • B) ↔
        ((ProjectionPerturbation.bbf P).graph K).Adj A B) :
    let Gamma := (ProjectionPerturbation.bbf P).graph K
    let hpre : Gamma.Preconnected :=
      P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos])
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Space Gamma (connected_of_preconnected H Gamma hpre)) := by
  dsimp only
  let Gamma := (ProjectionPerturbation.bbf P).graph K
  have hpre : Gamma.Preconnected :=
    P.bbf_graph_preconnected (by linarith [hK, P.ξ_pos])
  obtain ⟨delta, hCayley⟩ :=
    exists_cayley_hyperbolic_of_bbf (H := H) P hK hinv
  refine ⟨delta + 3, ?_⟩
  change IsHyperbolicSpace (delta + 3)
    (Space Gamma (connected_of_preconnected H Gamma hpre))
  simpa only [mul_one] using
    (isHyperbolicSpace_of_additiveDistortion
      (representativeMap_additiveDistortion H Gamma hinv hpre) hCayley)

end Projection
end CosetGraph
end GGT
end GroupApproximation
