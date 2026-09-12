import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPower

/-!
# Least-area power diagrams for Hull's Lemma 4.9

`HullSC.Lemma49ReducedPowerDiagram` records the reducedness that least area
implies but not the least area itself: `exists_lemma49ReducedPowerDiagram`
builds the minimality of `Nat.find` and spends it only on `reduced` and
`no_cancelling_pair`.  A Greendlinger waist stated at least-area planar diagrams
needs the minimality, so this module keeps it, **without adding a field to any
landed structure**:

* `Lemma49LeastAreaPowerDiagram` extends `Lemma49GeodesicPowerDiagram` by
  `area_minimal`, over the singleton relator `{listVal v}` the power diagram is
  built over.
* `exists_lemma49LeastAreaPowerDiagram` re-runs
  `exists_lemma49ReducedPowerDiagram`, `exists_oriented` and
  `exists_geodesicBoundary`, keeping the minimality.
* `isRelatorProduct_singleton_of_symmetrized`: a relator product over the
  symmetrized family `listVal '' symmetrized v` is one over `{listVal v}` with
  the same number of factors, because every cyclic permutation of `v` or of its
  formal inverse reads a signed conjugate of `listVal v`.
* `Lemma49LeastAreaPowerDiagram.cactus_leastArea`: the explicit power cactus of
  such a diagram is least area in the planar sense (the unfolded
  `GGT.VanKampen.DiscDiagram.LeastArea` over the symmetrized family).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The symmetrized family reads signed conjugates of the relator -/

/-- **Every member of the symmetrized closure reads a signed conjugate of the
relator.**  A cyclic permutation `v.rotate k` reads `p⁻¹ · listVal v · p` for the
prefix value `p`; a cyclic permutation of `revInv v` reads the same conjugate of
`(listVal v)⁻¹`. -/
theorem signedConjugate_listVal_of_mem_symmetrized
    {G : Type u} [Group G] {Λ : Type w}
    {v w : List (GGT.RelLetter G Λ)} (hw : w ∈ RelWord.symmetrized v) :
    RelatorDefectBudget.IsSignedConjugate ({GGT.RelLetter.listVal v} : Set G)
      (GGT.RelLetter.listVal w) := by
  have hrot : ∀ (u : List (GGT.RelLetter G Λ)) (k : ℕ),
      ∃ c : G, GGT.RelLetter.listVal (u.rotate k) =
        c * GGT.RelLetter.listVal u * c⁻¹ := by
    intro u k
    rcases Nat.eq_zero_or_pos u.length with hzero | hpos
    · have hnil : u = [] := List.length_eq_zero_iff.mp hzero
      subst hnil
      exact ⟨1, by simp⟩
    · have hle : k % u.length ≤ u.length := le_of_lt (Nat.mod_lt k hpos)
      refine ⟨(GGT.RelLetter.listVal (u.take (k % u.length)))⁻¹, ?_⟩
      rw [← List.rotate_mod, RelWord.listVal_rotate u hle, inv_inv]
  rcases (RelWord.mem_symmetrized.mp hw).exists_rotate with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, hc⟩ := hrot v k
    exact ⟨c, GGT.RelLetter.listVal v, Set.mem_singleton _, Or.inl hc⟩
  · obtain ⟨c, hc⟩ := hrot (RelWord.revInv v) k
    refine ⟨c, GGT.RelLetter.listVal v, Set.mem_singleton _, Or.inr ?_⟩
    rw [hc, RelWord.listVal_revInv]

/-- **Relator products over the symmetrized family are relator products over
the singleton relator**, with the same number of factors. -/
theorem isRelatorProduct_singleton_of_symmetrized
    {G : Type u} [Group G] {Λ : Type w} {v : List (GGT.RelLetter G Λ)}
    {m : ℕ} {x : G}
    (h : RelatorDefectBudget.IsRelatorProduct
      (GGT.RelLetter.listVal '' RelWord.symmetrized v) m x) :
    RelatorDefectBudget.IsRelatorProduct
      ({GGT.RelLetter.listVal v} : Set G) m x := by
  induction h with
  | one => exact .one
  | base hr =>
      obtain ⟨w, hw, rfl⟩ := hr
      obtain ⟨c, r, hr', hx | hx⟩ := signedConjugate_listVal_of_mem_symmetrized hw
      · rw [hx]
        exact .conj c (.base hr')
      · rw [hx]
        exact .conj c (.inv (.base hr'))
  | inv _ ih => exact .inv ih
  | conj c _ ih => exact .conj c ih
  | mul _ _ iha ihb => exact .mul iha ihb

/-! ## The least-area power diagram -/

/-- **A geodesic power diagram with least area.**  The extra field is the
minimality `exists_lemma49ReducedPowerDiagram` builds and does not store. -/
structure Lemma49LeastAreaPowerDiagram
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    (v : List (GGT.RelLetter G Λ)) (g : G) (n : ℕ)
    extends Lemma49GeodesicPowerDiagram D v g n where
  area_minimal : ∀ {m : ℕ},
    RelatorDefectBudget.IsRelatorProduct ({GGT.RelLetter.listVal v} : Set G) m
      (g ^ n) → area ≤ m

/-- **A nontrivial power in the normal closure of one relator has a least-area
geodesic power diagram**, with no geometric or literature input: the
construction of `exists_lemma49ReducedPowerDiagram`, orientation and a geodesic
boundary word, keeping the minimality. -/
theorem exists_lemma49LeastAreaPowerDiagram
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ} (hn : 0 < n)
    (hpow : g ^ n ∈ Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G))
    (hne : g ^ n ≠ 1) :
    Nonempty (Lemma49LeastAreaPowerDiagram D v g n) := by
  classical
  have hex : ∃ area : ℕ, RelatorDefectBudget.IsRelatorProduct
      ({GGT.RelLetter.listVal v} : Set G) area (g ^ n) :=
    RelatorDefectBudget.exists_isRelatorProduct hpow
  have hcertificate : RelatorDefectBudget.IsRelatorProduct
      ({GGT.RelLetter.listVal v} : Set G) (Nat.find hex) (g ^ n) := Nat.find_spec hex
  obtain ⟨factors, hlength, hprod, hcells⟩ := hcertificate.exists_flatten
  have harea_pos : 0 < Nat.find hex := by
    by_contra hnot
    have hzero : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hnot
    have hcertificate0 : RelatorDefectBudget.IsRelatorProduct
        ({GGT.RelLetter.listVal v} : Set G) 0 (g ^ n) := by
      simpa only [hzero] using hcertificate
    exact hne hcertificate0.eq_one_of_index_zero
  have hminimal : ∀ {m : ℕ}, RelatorDefectBudget.IsRelatorProduct
      ({GGT.RelLetter.listVal v} : Set G) m (g ^ n) → Nat.find hex ≤ m := by
    intro m hm
    exact Nat.find_min' hex hm
  let P₀ : Lemma49ReducedPowerDiagram ({GGT.RelLetter.listVal v} : Set G) g n :=
    { exponent_pos := hn
      power_ne_one := hne
      area := Nat.find hex
      area_pos := harea_pos
      factors := factors
      factors_length := hlength
      factors_prod := hprod
      factors_cells := hcells
      reduced := RelatorDefectBudget.no_trivial_subproduct_of_minimal
        hlength hprod hcells hminimal
      no_cancelling_pair := RelatorDefectBudget.no_cancelling_pair_of_minimal
        hlength hprod hcells hminimal }
  obtain ⟨cells, hcellValues⟩ :=
    exists_lemma49OrientedCells v P₀.factors P₀.factors_cells
  obtain ⟨boundaryWord, hboundary⟩ := GGT.OsinComponents.existsGeodesicWord D 1 g
  exact ⟨{
    toLemma49GeodesicPowerDiagram :=
      { toLemma49OrientedPowerDiagram :=
          { toLemma49ReducedPowerDiagram := P₀
            cells := cells
            cell_values := hcellValues }
        boundaryWord := boundaryWord
        boundary_geodesic := hboundary }
    area_minimal := fun hm => hminimal hm }⟩

/-- **The explicit power cactus of a least-area power diagram is least area**:
`GGT.VanKampen.DiscDiagram.LeastArea` over the symmetrized family, unfolded.
Its boundary value is `g ^ n` and its relator-cell count is the area. -/
theorem Lemma49LeastAreaPowerDiagram.cactus_leastArea
    {G : Type u} [Group G] {Λ : Type w} {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49LeastAreaPowerDiagram D v g n) :
    ∀ {m : ℕ},
      RelatorDefectBudget.IsRelatorProduct
          (GGT.RelLetter.listVal '' RelWord.symmetrized v) m
          Z.toLemma49GeodesicPowerDiagram.cactusDiscDiagram.boundaryValue →
        Z.toLemma49GeodesicPowerDiagram.cactusDiscDiagram.rCellCount ≤ m := by
  intro m hm
  have hbv :
      Z.toLemma49GeodesicPowerDiagram.cactusDiscDiagram.boundaryValue = g ^ n := by
    show GGT.RelLetter.listVal
        Z.toLemma49GeodesicPowerDiagram.cactusDiscDiagram.boundaryWord = g ^ n
    rw [Lemma49GeodesicPowerDiagram.cactusDiscDiagram_boundaryWord,
      listVal_lemma49BoundaryPower]
    have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
      simpa using Z.boundary_geodesic.2.1
    rw [hvalue]
  have hcount :
      Z.toLemma49GeodesicPowerDiagram.cactusDiscDiagram.rCellCount = Z.area := by
    change Z.toLemma49GeodesicPowerDiagram.cactusRelatorCells.length = Z.area
    rw [Lemma49GeodesicPowerDiagram.cactusRelatorCells, List.length_ofFn]
    have hcells : Z.cells.length = Z.factors.length := by
      have hlength := congrArg List.length Z.cell_values
      simpa only [List.length_map] using hlength
    rw [hcells, Z.factors_length]
  rw [hbv] at hm
  rw [hcount]
  exact Z.area_minimal (isRelatorProduct_singleton_of_symmetrized hm)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.signedConjugate_listVal_of_mem_symmetrized
#audit_axioms GroupApproximation.HullSC.isRelatorProduct_singleton_of_symmetrized
#audit_axioms GroupApproximation.HullSC.exists_lemma49LeastAreaPowerDiagram
#audit_axioms GroupApproximation.HullSC.Lemma49LeastAreaPowerDiagram.cactus_leastArea
