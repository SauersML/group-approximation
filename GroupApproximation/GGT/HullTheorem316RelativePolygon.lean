import GroupApproximation.GGT.HullYiCyclicPairGeometry
import GroupApproximation.GGT.OlshanskiiLemma25
import GroupApproximation.GGT.DGOPolygonCutFamily
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# The relative word polygon in Hull's Theorem 3.16

Hull's proof of Theorem 3.16 takes an admissible relative word from `1` to an
element `h` of a peripheral subgroup, replaces every relative edge by a
geodesic over the *prescribed* alphabet, and adds the geodesic from `h` back
to `1`.  This file constructs that polygon in the geodesic realization of the
prescribed Cayley graph.

The distinction between the two alphabets is essential.  In the cone-off
metric every peripheral edge has length at most one, whereas Hull applies the
long-side polygon lemma to its length over the original alphabet.  The
construction below therefore uses `CayleyGeodesicModel.PointQuot A`, not the
geodesic model of `(coneOffFamily A K).alphabet`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Vertices of Hull's closed polygon.  Side zero runs from the endpoint of
the relative word back to its initial vertex.  Side `j+1` is the prescribed-
alphabet geodesic replacing relative letter `j`. -/
noncomputable def relativeClosingVertex (A : Alphabet G)
    (q : List (RelLetter G Λ)) : ℕ → CayleyGeodesicModel.PointQuot A
  | 0 => iotaG A (RelLetter.listVal q)
  | j + 1 => iotaG A (vertex 1 q j)

@[simp] theorem relativeClosingVertex_zero (A : Alphabet G)
    (q : List (RelLetter G Λ)) :
    relativeClosingVertex A q 0 = iotaG A (RelLetter.listVal q) := rfl

@[simp] theorem relativeClosingVertex_succ (A : Alphabet G)
    (q : List (RelLetter G Λ)) (j : ℕ) :
    relativeClosingVertex A q (j + 1) = iotaG A (vertex 1 q j) := rfl

/-- The extra closing side really closes the relative-word path. -/
theorem relativeClosingVertex_last (A : Alphabet G)
    (q : List (RelLetter G Λ)) :
    relativeClosingVertex A q (q.length + 1) = relativeClosingVertex A q 0 := by
  rw [relativeClosingVertex_succ, relativeClosingVertex_zero,
    vertex_eq_mul_listVal_take, List.take_length, one_mul]

/-- Every relative word, without a reducedness or admissibility assumption,
has Hull's closed geodesic `(q.length+1)`-gon over the prescribed alphabet. -/
theorem exists_relativeClosingPolygon (A : Alphabet G)
    (q : List (RelLetter G Λ)) :
    ∃ sides : ℕ → ℝ → CayleyGeodesicModel.PointQuot A,
      IsClosedPolygonAt (relativeClosingVertex A q) sides 0 (q.length + 1) := by
  let vs := relativeClosingVertex A q
  obtain ⟨sides, hsides⟩ := exists_isSideFamily
    (CayleyGeodesicModel.isGeodesicRealisationQuot A) vs (q.length + 1)
  refine ⟨sides, ?_, ?_⟩
  · intro i hi0 hi
    exact hsides i (by omega)
  · simpa using relativeClosingVertex_last A q

/-- Indices (other than the distinguished closing side zero) which replace a
peripheral letter.  Using `get?` makes the class independent of proof terms
carried by `getElem`. -/
def relativeCompSides (q : List (RelLetter G Λ)) : Set ℕ :=
  {i | ∃ lam h, q[i - 1]? = some (RelLetter.comp lam h)}

omit [Group G] in
/-- Membership in the long-side class names the underlying relative letter. -/
theorem mem_relativeCompSides_iff (q : List (RelLetter G Λ)) (i : ℕ) :
    i ∈ relativeCompSides q ↔
      ∃ lam h, q[i - 1]? = some (RelLetter.comp lam h) := Iff.rfl

/-- A non-peripheral side of the relative-word polygon has length at most two
in the quotient geodesic model.  One unit is the base letter and one is the
additive distortion of the vertex inclusion. -/
theorem dist_relativeClosingVertex_le_two_of_not_comp
    (A : Alphabet G) (K : Λ → Subgroup G)
    (q : List (RelLetter G Λ))
    (hlet : ∀ a ∈ q, (coneOffFamily A K).IsLetter a)
    {i : ℕ} (hi0 : 0 < i) (hi : i < q.length + 1)
    (hnot : i ∉ relativeCompSides q) :
    dist (relativeClosingVertex A q i) (relativeClosingVertex A q (i + 1)) ≤ 2 := by
  let j := i - 1
  have hj : j < q.length := by
    dsimp [j]
    omega
  have hij : i = j + 1 := by
    dsimp [j]
    omega
  have hget : q[j]? = some (q[j]'hj) := List.getElem?_eq_getElem hj
  cases hletter : q[j]'hj with
  | comp lam h =>
      exfalso
      apply hnot
      rw [mem_relativeCompSides_iff, hij]
      have hsub : j + 1 - 1 = j := by omega
      rw [hsub]
      exact ⟨lam, h, hget.trans (congrArg some hletter)⟩
  | base x =>
      have hx : x ∈ A.carrier := by
        have hqlet := hlet (q[j]'hj) (List.getElem_mem hj)
        rw [hletter] at hqlet
        exact hqlet
      have hv1 : relativeClosingVertex A q i = iotaG A (vertex 1 q j) := by
        rw [hij, relativeClosingVertex_succ]
      have hv2 : relativeClosingVertex A q (i + 1) =
          iotaG A (vertex 1 q (j + 1)) := by
        rw [show i + 1 = (j + 1) + 1 by omega, relativeClosingVertex_succ]
      rw [hv1, hv2, vertex_succ q 1 j hj, hletter]
      change dist (iotaG A (vertex 1 q j))
        (iotaG A (vertex 1 q j * x)) ≤ 2
      have hword : wordDist A.carrier (vertex 1 q j)
          (vertex 1 q j * x) ≤ 1 := by
        have heq : wordDist A.carrier (vertex 1 q j) (vertex 1 q j * x)
            = wordNorm A.carrier x := by
          show wordNorm A.carrier ((vertex 1 q j)⁻¹ * (vertex 1 q j * x)) = _
          rw [inv_mul_cancel_left]
        rw [heq]
        exact wordNorm_le_one_of_mem hx
      have hup := dist_iotaG_le A (vertex 1 q j) (vertex 1 q j * x)
      have hcast : ((wordDist A.carrier (vertex 1 q j)
          (vertex 1 q j * x) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hword
      linarith

omit [Group G] in
/-- The total short-side budget in Hull's polygon is at most twice the
relative-word length. -/
theorem relative_short_side_budget (q : List (RelLetter G Λ)) :
    ∑ _j ∈ Finset.range q.length, (2 : ℝ) ≤ 2 * (q.length : ℝ) := by
  simp [mul_comm]

/-- The direct output of Ol'shanskii's long-side lemma for Hull's relative
word polygon.  If the prescribed-alphabet geodesic from `h` to `1` is long,
it fellow-travels a long subsegment of a side which replaces an actual
peripheral letter of the relative word.

This is the geometric alternative immediately before Hull invokes
quasiconvexity and geometric separation. -/
theorem exists_peripheral_side_close_to_long_closing_side
    (A : Alphabet G) (K : Λ → Subgroup G) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A.carrier δ)
    (q : List (RelLetter G Λ))
    (hlet : ∀ a ∈ q, (coneOffFamily A K).IsLetter a)
    (hq : 0 < q.length) {θ ξ : ℝ}
    (hξ0 : 0 < ξ)
    (hξ : 30000 * (3 * ((δ : ℝ) + 6) *
        ((Nat.clog 2 q.length : ℝ) + 1)) ≤ ξ)
    (hθn : ((q.length + 1 : ℕ) : ℝ) * ξ < θ)
    (hθρ : 1000 * (2 * (q.length : ℝ)) < θ)
    (hθb : θ ≤ dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)) :
    ∃ i lam h, 0 < i ∧ i < q.length + 1 ∧
      q[i - 1]? = some (RelLetter.comp lam h) ∧
      ∃ u ∈ Set.Icc (0 : ℝ)
          (dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)),
        ∃ u' ∈ Set.Icc (0 : ℝ)
            (dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)),
          ∃ s ∈ Set.Icc (0 : ℝ)
              (dist (relativeClosingVertex A q i)
                (relativeClosingVertex A q (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ)
                (dist (relativeClosingVertex A q i)
                  (relativeClosingVertex A q (i + 1))),
              ξ / 1000 ≤ u' - u ∧ ξ / 1000 ≤ |s' - s| ∧
                dist ((Classical.choose (exists_relativeClosingPolygon A q)) 0 u)
                    ((Classical.choose (exists_relativeClosingPolygon A q)) i s)
                  ≤ ξ / 30000 ∧
                dist ((Classical.choose (exists_relativeClosingPolygon A q)) 0 u')
                    ((Classical.choose (exists_relativeClosingPolygon A q)) i s')
                  ≤ ξ / 30000 := by
  let sides := Classical.choose (exists_relativeClosingPolygon A q)
  have hpoly : IsClosedPolygonAt (relativeClosingVertex A q) sides 0
      (q.length + 1) := Classical.choose_spec (exists_relativeClosingPolygon A q)
  have hhypC : IsHyperbolicSpace ((δ : ℝ)) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hδ
  have hhyp : IsHyperbolicSpace ((δ : ℝ) + 6)
      (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A hhypC)
  have hgeo : IsGeodesicSpace (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isGeodesicRealisationQuot A
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) + 6 := by positivity
  have hn : 2 ≤ q.length + 1 := by omega
  have hshort : ∀ i, 0 < i → i < q.length + 1 →
      i ∉ relativeCompSides q →
      dist (relativeClosingVertex A q i)
        (relativeClosingVertex A q (i + 1)) ≤ (fun _ => (2 : ℝ)) i := by
    intro i hi0 hi hin
    exact dist_relativeClosingVertex_le_two_of_not_comp A K q hlet hi0 hi hin
  have hρ : ∑ j ∈ Finset.range ((q.length + 1) - 1),
      (fun _ => (2 : ℝ)) (0 + 1 + j) ≤ 2 * (q.length : ℝ) := by
    simpa using relative_short_side_budget (G := G) (Λ := Λ) q
  have hθb' : θ ≤ dist (relativeClosingVertex A q 0)
      (relativeClosingVertex A q (0 + 1)) := by
    simpa [relativeClosingVertex] using hθb
  obtain ⟨i, hi0, hi, hiS, u, hu, u', hu', s, hs, s', hs',
      huu', hss', hclose, hclose'⟩ :=
    exists_long_close_pair_of_short_complement hhyp hδ0 hgeo hn hpoly
      (relativeCompSides q) (fun _ => (2 : ℝ)) (fun _ => by positivity)
      (fun i hi0 hi hiS => hshort i hi0 (by omega) hiS)
      hρ hξ0 hξ hθn hθρ hθb'
  obtain ⟨lam, h, hletter⟩ := hiS
  refine ⟨i, lam, h, hi0, (by omega), hletter, u, ?_, u', ?_, s, hs, s', hs',
    huu', hss', ?_, ?_⟩
  · simpa [relativeClosingVertex] using hu
  · simpa [relativeClosingVertex] using hu'
  · simpa [sides] using hclose
  · simpa [sides] using hclose'

end HullSC
end GroupApproximation
