import GroupApproximation.GGT.DGOPolygonCutFamily
import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.DGOSubdivisionLinear
import GroupApproximation.GGT.DGOAssemblySubdivision
import GroupApproximation.GGT.DGOAssemblyCharge

/-!
# DGO Proposition 4.14: the least-cost function and final assembly

This module joins the already authored parts of the Proposition 4.14 campaign
at their exact mathematical interface.

* `exists_sumBound` makes the set of admissible constants nonempty.  It uses
  the existing all-side-count component bound separately on every
  distinguished side.  The resulting cubic estimate is intentionally crude;
  its only purpose is to justify minimisation.
* `sumCost` is the least admissible constant at a fixed side count.
* `sumBound_linear_of_subdivision` applies DGO's Lemma 4.19, formalized as
  `DGO.linear_of_subdivision`, to that least-cost function and returns the
  uniform linear conclusion of Proposition 4.14.

The remaining premise is displayed in the final theorem.  The old geometric
obstruction is gone: `DGOAssemblySubdivision.exists_interior_half_polygon_data`
inserts the two selected graph vertices, pays exactly two sides, and supplies
the closed half-polygons without a uniform side-length hypothesis.  What is
still missing is DGO's component surgery and witness addition: transfer the
distinguished components to the cycles cut along the chord, charge every broken
component by its chord partner and two connector edges, and add the resulting
`SumBound` witnesses.  The last theorem below states exactly that remaining
premise as one admissible bound, rather than hiding it as a numerical
inequality.  No base-case, minimisation, rounding, or arithmetic premise
remains hidden.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Promoting a `SumBound` input to the geometric cut shape -/

/-- **The polygon quantified by `SumBound` is a named `(1,b+1)`-polygon.**

Off the distinguished set this only weakens the supplied `(1,b)` inequality.
On the distinguished set the side is one edge, so every subsegment has length
at most one and the extra `+1` makes the lower bound automatic.  This is the
bridge that lets `exists_balanced_interior_cut_word` apply to the actual
Proposition 4.14 input rather than to a stronger all-sides-quasi-geodesic
variant. -/
theorem isCutPolygon_of_sumBound_shape (D : RelGenSet G Λ) (b n : ℕ)
    (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (I : Finset ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hcut : IsPolygonCut n w c)
    (hedge : ∀ s ∈ I, c (s + 1) = c s + 1)
    (hquasi : ∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) :
    IsCutPolygon D ((b + 1 : ℕ) : ℝ) n v w c := by
  refine ⟨hlet, hclosed, hcut, ?_⟩
  intro s hs p q hp hpq hq
  by_cases hsI : s ∈ I
  · have hpq1 : q - p ≤ 1 := by
      have he := hedge s hsI
      omega
    have hpq1R : ((q - p : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hpq1
    have hdist0 : (0 : ℝ) ≤
        ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  · have h := hquasi s hs hsI p q hp hpq hq
    push_cast
    linarith

/-! ## Nonemptiness of the admissible constants -/

/-- **A sum bound exists at every side count.**

For the purpose of nonemptiness only, apply the already proved one-component
bound to each distinguished side and add the radii.  The one-component theorem
asks for every side to be quasi-geodesic, whereas `SumBound` exempts the
distinguished sides.  Enlarging `b` to `b + 1` fills precisely that gap: a
distinguished side is one letter, hence every subsegment has length at most
one and is automatically `(1,b+1)`-quasi-geodesic.

The estimate is cubic in `n`; Proposition 4.14 does not use this estimate, only
the fact that some estimate exists so that the least one can be selected. -/
theorem exists_sumBound (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    ∃ K : ℕ, SumBound D (b : ℝ) n K := by
  let R : ℕ := (n + 1) * (25 * (δ + (b + 1) + 1)) * (n + 2)
  refine ⟨n * R, ?_⟩
  intro v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  have hcutpoly : IsCutPolygon D ((b + 1 : ℕ) : ℝ) n v w c :=
    isCutPolygon_of_sumBound_shape D b n v w c I hlet hclosed hcut hedge hquasi
  have hpoly : IsQuasiGeodesicPolygon D 1 ((b + 1 : ℕ) : ℝ) n v w :=
    hcutpoly.toPolygon
  refine ⟨fun _ ↦ R, ?_, ?_⟩
  · intro s hs
    exact isolatedComponentBound_nGon_of_fourPointHyperbolic D hsymm (b + 1) hδ n
      v w hpoly (lam s) (c s) (c (s + 1)) (hcomp s hs) (hiso s hs)
  · have hsubset : I ⊆ Finset.range n := by
      intro s hs
      exact Finset.mem_range.mpr (hI s hs)
    have hcard : I.card ≤ n := by
      simpa using Finset.card_le_card hsubset
    have hconst : ∑ _s ∈ I, R = I.card * R :=
      Finset.sum_const_nat (fun _ _ ↦ rfl)
    rw [hconst]
    exact Nat.mul_le_mul hcard le_rfl

/-! ## The least admissible sum constant -/

/-- The least constant for which the sum bound holds at side count `n`. -/
noncomputable def sumCost (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_sumBound D hsymm b hδ n)

/-- The least constant is itself admissible. -/
theorem sumBound_sumCost (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    SumBound D (b : ℝ) n (sumCost D hsymm b hδ n) :=
  by
    classical
    exact Nat.find_spec (exists_sumBound D hsymm b hδ n)

/-- Minimality of `sumCost`. -/
theorem sumCost_le (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n K : ℕ} (hK : SumBound D (b : ℝ) n K) :
    sumCost D hsymm b hδ n ≤ K :=
  by
    classical
    exact Nat.find_min' (exists_sumBound D hsymm b hδ n) hK

/-! ## Honest auxiliary-cycle family certificates -/

/-- **One auxiliary cycle with every premise needed by `SumBound` exposed.**

The word and cut are the concrete output of `auxiliaryCycleWord` and
`auxiliaryCycleCut` (or an endpoint-degenerate instance of them).  In
particular `quasi` is not inferred from closure, admissibility, or isolation:
it explicitly records the `(1,b)` estimate on every non-distinguished side.
This is the premise missing from the current local auxiliary-cycle modules. -/
structure AuxiliaryCycleCertificate (D : RelGenSet G Λ) (b : ℝ) (m : ℕ) where
  basepoint : G
  word : List (RelLetter G Λ)
  cut : ℕ → ℕ
  target : Finset ℕ
  label : ℕ → Λ
  letters : ∀ a ∈ word, D.IsLetter a
  closed : RelLetter.listVal word = 1
  polygonCut : IsPolygonCut m word cut
  target_lt : ∀ s ∈ target, s < m
  target_edge : ∀ s ∈ target, cut (s + 1) = cut s + 1
  target_component : ∀ s ∈ target,
    IsComp (label s) word (cut s) (cut (s + 1))
  target_isolated : ∀ s ∈ target,
    IsIsolated D.fam (label s) basepoint word (cut s)
  quasi : ∀ s : ℕ, s < m → s ∉ target → ∀ p q : ℕ,
    cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
    ((q - p : ℕ) : ℝ) - b ≤
      ((wordDist D.alphabet.carrier
        (vertex basepoint word p) (vertex basepoint word q) : ℕ) : ℝ)

namespace AuxiliaryCycleCertificate

/-- The group element represented by a distinguished side of a certified
auxiliary cycle. -/
def sideSpan {D : RelGenSet G Λ} {b : ℝ} {m : ℕ}
    (A : AuxiliaryCycleCertificate D b m) (s : ℕ) : G :=
  (vertex A.basepoint A.word (A.cut s))⁻¹ *
    vertex A.basepoint A.word (A.cut (s + 1))

/-- Applying a `SumBound` to a fully certified child cycle produces its local
radius witnesses. -/
theorem exists_radius {D : RelGenSet G Λ} {b : ℝ} {m K : ℕ}
    (A : AuxiliaryCycleCertificate D b m) (hK : SumBound D b m K) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ A.target,
        A.sideSpan s ∈ D.relBall (A.label s) (r s)) ∧
      ∑ s ∈ A.target, r s ≤ K := by
  exact hK A.basepoint A.word A.cut A.target A.label A.letters A.closed
    A.polygonCut A.target_lt A.target_edge A.target_component
    A.target_isolated A.quasi

/-- A canonical choice of the child witness at the least admissible bound. -/
noncomputable def radius (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {m : ℕ}
    (A : AuxiliaryCycleCertificate D (b : ℝ) m) : ℕ → ℕ :=
  Classical.choose (A.exists_radius (sumBound_sumCost D hsymm b hδ m))

theorem sideSpan_mem_radius (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {m : ℕ}
    (A : AuxiliaryCycleCertificate D (b : ℝ) m) :
    ∀ s ∈ A.target,
      A.sideSpan s ∈ D.relBall (A.label s) (A.radius D hsymm b hδ s) :=
  (Classical.choose_spec
    (A.exists_radius (sumBound_sumCost D hsymm b hδ m))).1

theorem sum_radius_le_sumCost (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {m : ℕ}
    (A : AuxiliaryCycleCertificate D (b : ℝ) m) :
    ∑ s ∈ A.target, A.radius D hsymm b hδ s ≤
      sumCost D hsymm b hδ m :=
  (Classical.choose_spec
    (A.exists_radius (sumBound_sumCost D hsymm b hδ m))).2

end AuxiliaryCycleCertificate

/-- **A local family of auxiliary cycles with all charging and count data.**

This is deliberately a certificate for one input polygon.  `children` are
fully checkable cycles, including the off-target quasi-geodesic clause.
`original_mem` and `charge` are the output of survivor transfer and the
quadrilateral charging lemmas: every original distinguished side receives a
radius, and their total is charged injectively to the selected sides of the
children.

The structure does *not* claim that such a certificate has been constructed
from the two greedy half enumerations.  Nor does it turn polygon-dependent
child sizes into the one uniform tuple required by `SumBound`; those are the
remaining construction and uniform-maximisation boundaries. -/
structure AuxiliaryCycleFamilyCertificate (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (n : ℕ) (v : G) (word : List (RelLetter G Λ)) (cut : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ) where
  k : ℕ
  childSides : Fin k → ℕ
  chordLength : ℕ
  partners : List ℕ
  children : ∀ j : Fin k,
    AuxiliaryCycleCertificate D (b : ℝ) (childSides j)
  owner : ℕ → Fin k
  originalRadius : Fin k → ℕ → ℕ
  original_mem : ∀ s ∈ I,
    (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) ∈
      D.relBall (lam s) (originalRadius (owner s) s)
  charge : ∀ j : Fin k,
    ∑ s ∈ I, (if owner s = j then originalRadius j s else 0) ≤
      ∑ t ∈ (children j).target, (children j).radius D hsymm b hδ t
  count_lower : n ≤ ∑ j, childSides j
  count_upper : ChordPartnerQuadraticTraversalBound chordLength partners →
    ∑ j, childSides j ≤ n + 6 * (chordLength * chordLength)
  child_small : ∀ j, 5 * childSides j ≤ 4 * n
  traversal : ChordPartnerQuadraticTraversalBound chordLength partners

/-- **What a local auxiliary-cycle family certificate proves.**

The child `SumBound` witnesses add, the charging injection transfers them to
the original distinguished components, and the four numerical conclusions
needed by the quadratic subdivision route are exported unchanged. -/
theorem consequences_of_auxiliaryCycleFamilyCertificate (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} {v : G} {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    {I : Finset ℕ} {lam : ℕ → Λ}
    (A : AuxiliaryCycleFamilyCertificate D hsymm b hδ n v word cut I lam) :
    n ≤ ∑ j, A.childSides j ∧
    (∑ j, A.childSides j ≤
      n + 6 * (A.chordLength * A.chordLength)) ∧
    (∀ j, 5 * A.childSides j ≤ 4 * n) ∧
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) ∈
          D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤
        ∑ j, sumCost D hsymm b hδ (A.childSides j) := by
  obtain ⟨r, hrmem, hrsum⟩ := combine_relBall_witnesses_finite D I A.owner lam
    (fun s => (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)))
    A.originalRadius
    (fun j => ∑ t ∈ (A.children j).target,
      (A.children j).radius D hsymm b hδ t)
    A.original_mem A.charge
  refine ⟨A.count_lower, A.count_upper A.traversal, A.child_small,
    r, hrmem, hrsum.trans ?_⟩
  exact Finset.sum_le_sum fun j _ =>
    AuxiliaryCycleCertificate.sum_radius_le_sumCost D hsymm b hδ (A.children j)

/-! ## The final `dgo-cycle` arithmetic assembly -/

/-- **DGO Proposition 4.14 from the balanced subdivision inequality.**

The hypothesis `H` is the entire remaining subdivision inequality.
`DGOAssemblySubdivision` now supplies the interior graph-vertex refinement,
geodesic chord, two closed words, and the estimates
`m₁ + m₂ = n + 2 + 2L` and `4mᵢ ≤ 3n + 4 + 4L`, with no side-length bound.
Component surgery must still transfer the isolated distinguished components
and add their witnesses.  `sumBound_linear_of_transferred_subdivision` below
exposes that stronger, structural form of the premise.

Everything after `H` is closed here.  `nat_linear_of_subdivision` performs the
real-to-natural rounding once in the arithmetic module and absorbs the
additive term for `n ≥ 1`; this assembly only applies minimality of `sumCost`
and monotonicity of `SumBound`. -/
theorem sumBound_linear_of_subdivision (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (C : ℝ) (N : ℕ) (α : ℝ) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ C * Real.log n ∧
      (sumCost D hsymm b hδ n : ℝ) ≤
        ∑ i, (sumCost D hsymm b hδ (m i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + C * Real.log n ∧
      ∀ i, (m i : ℝ) ≤ α * n) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  obtain ⟨L, hlin⟩ :=
    DGO.nat_linear_of_subdivision (sumCost D hsymm b hδ) C N α hC hα0 hα1 H
  refine ⟨L, ?_⟩
  intro n hn
  apply SumBound.mono (sumBound_sumCost D hsymm b hδ n)
  exact hlin n hn

/-- **DGO Proposition 4.14 from the actual transferred `SumBound`.**

This is the strongest honest assembly interface after the interior split.  Its
premise does not assume the desired inequality for `sumCost`; it asks the
geometry/component lane to construct what the printed proof constructs: an
admissible `SumBound` at `n` whose radius is the sum of the least bounds of the
smaller cycles.  Minimality of `sumCost` turns that object into the numerical
subdivision inequality, and all remaining work is discharged above.

Thus the last non-arithmetic obligation is exactly the final conjunct of `H`:
component transfer, chord-partner charging, and witness addition must prove
`SumBound D (b : ℝ) n (∑ i, sumCost ... (m i))`. -/
theorem sumBound_linear_of_transferred_subdivision (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (C : ℝ) (N : ℕ) (α : ℝ) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ C * Real.log n ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + C * Real.log n ∧
      (∀ i, (m i : ℝ) ≤ α * n) ∧
      SumBound D (b : ℝ) n (∑ i, sumCost D hsymm b hδ (m i))) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply sumBound_linear_of_subdivision D hsymm b hδ C N α hC hα0 hα1
  intro n hn
  obtain ⟨k, m, hk, hnle, hsumle, hm, hbound⟩ := H n hn
  have hcostNat : sumCost D hsymm b hδ n ≤
      ∑ i, sumCost D hsymm b hδ (m i) :=
    sumCost_le D hsymm b hδ hbound
  have hcost : (sumCost D hsymm b hδ n : ℝ) ≤
      ∑ i, (sumCost D hsymm b hδ (m i) : ℝ) := by
    exact_mod_cast hcostNat
  exact ⟨k, m, hk, hcost, hnle, hsumle, hm⟩

/-- **Conditional final assembly with the literature gap named explicitly.**

The auxiliary-cycle modules provide the closure, admissibility, component
exhaustion, Target-vs-All isolation (including arbitrary type-(2) components),
connector charging, and witness-addition lemmas used by the transferred
certificate.  What the printed proof additionally uses in its line
`∑ n_j ≤ n + 6 length(t)` is a bounded-total-variation fact for the greedily
selected chord partners.  It is recorded here as
`ChordPartnerTraversalBound` rather than being silently inferred from partner
injectivity.

The final conjunct is the transferred `SumBound` certificate produced by those
local constructions; the preceding named conjunct is the extra fact needed to
put its cycle sizes inside DGO's logarithmic subdivision budget.  Once both are
present, the already completed minimisation and Lemma 4.19 assembly yield
Proposition 4.14. -/
theorem sumBound_linear_of_chordPartnerTraversal (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (C : ℝ) (N : ℕ) (α : ℝ) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∀ n : ℕ, N < n →
      ∃ (k : ℕ) (m : Fin k → ℕ) (chordLength : ℕ) (partners : List ℕ),
        (k : ℝ) ≤ C * Real.log n ∧
        (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
        (ChordPartnerTraversalBound chordLength partners →
          (∑ i, (m i : ℝ)) ≤ (n : ℝ) + 6 * chordLength) ∧
        (6 * chordLength : ℝ) ≤ C * Real.log n ∧
        (∀ i, (m i : ℝ) ≤ α * n) ∧
        ChordPartnerTraversalBound chordLength partners ∧
        SumBound D (b : ℝ) n (∑ i, sumCost D hsymm b hδ (m i))) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply sumBound_linear_of_transferred_subdivision D hsymm b hδ
    C N α hC hα0 hα1
  intro n hn
  obtain ⟨k, m, chordLength, partners, hk, hnle, hsize, hchord, hm,
    htraversal, hbound⟩ := H n hn
  have hsumle : (∑ i, (m i : ℝ)) ≤ (n : ℝ) + C * Real.log n := by
    have hs := hsize htraversal
    exact hs.trans (by
      simpa [add_comm] using (add_le_add_left hchord (n : ℝ)))
  exact ⟨k, m, hk, hnle, hsumle, hm, hbound⟩

/-- **Sound Proposition 4.14 assembly with unordered chord partners.**

The published proof's linear traversal assertion is deliberately not used.
Instead, the component-surgery constructor supplies the unconditional
quadratic bound `chordTraversalCost partners ≤ chordLength²` through
`exists_greedy_incidenceEnumeration_quadratic`.  The resulting cycle-size
overhead is allowed to be squared-logarithmic; the robust form of Lemma 4.19
only asks that the number-of-pieces overhead plus the size overhead is
eventually smaller than the square-root gain.

Thus this theorem is the repair path for DGO Proposition 4.14.  The preceding
`sumBound_linear_of_chordPartnerTraversal` remains as an explicit record of the
stronger, unproved line in the source. -/
theorem sumBound_linear_of_quadraticChordTraversal (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (pieceOverhead sizeOverhead : ℕ → ℝ) (N : ℕ) (α ε : ℝ) (M₁ : ℕ)
    (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε)
    (hgain : Real.sqrt α * (1 + ε) ≤ 1)
    (hthresh : ∀ n : ℕ, M₁ < n →
      sizeOverhead n + pieceOverhead n ≤ ε * Real.sqrt n)
    (H : ∀ n : ℕ, N < n →
      ∃ (k : ℕ) (m : Fin k → ℕ) (chordLength : ℕ) (partners : List ℕ),
        (k : ℝ) ≤ pieceOverhead n ∧
        (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
        (ChordPartnerQuadraticTraversalBound chordLength partners →
          (∑ i, (m i : ℝ)) ≤
            (n : ℝ) + 6 * (chordLength * chordLength)) ∧
        (6 * (chordLength * chordLength) : ℝ) ≤ sizeOverhead n ∧
        (∀ i, (m i : ℝ) ≤ α * n) ∧
        ChordPartnerQuadraticTraversalBound chordLength partners ∧
        SumBound D (b : ℝ) n (∑ i, sumCost D hsymm b hδ (m i))) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  obtain ⟨L, hlinear⟩ :=
    DGO.nat_linear_of_subdivision_of_sqrt_overhead
      (sumCost D hsymm b hδ) pieceOverhead sizeOverhead N α ε M₁
      hα0 hα1 hε0 hgain hthresh (by
        intro n hn
        obtain ⟨k, m, chordLength, partners, hk, hnle, hsize, hquadratic,
          hm, htraversal, hbound⟩ := H n hn
        have hsumle : (∑ i, (m i : ℝ)) ≤ (n : ℝ) + sizeOverhead n :=
          (hsize htraversal).trans (by
            simpa using (add_le_add_left hquadratic (n : ℝ)))
        have hcostNat : sumCost D hsymm b hδ n ≤
            ∑ i, sumCost D hsymm b hδ (m i) :=
          sumCost_le D hsymm b hδ hbound
        have hcost : (sumCost D hsymm b hδ n : ℝ) ≤
            ∑ i, (sumCost D hsymm b hδ (m i) : ℝ) := by
          exact_mod_cast hcostNat
        exact ⟨k, m, hk, hcost, hnle, hsumle, hm⟩)
  refine ⟨L, ?_⟩
  intro n hn
  exact SumBound.mono (sumBound_sumCost D hsymm b hδ n) (hlinear n hn)

end DGOProposition414
end GGT
end GroupApproximation
