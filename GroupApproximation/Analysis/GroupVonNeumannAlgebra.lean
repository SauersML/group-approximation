import GroupApproximation.Analysis.TwoSidedRegularCommutant
import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# The group von Neumann algebra, and generation in standard form

Second module of the `LI.06d` lane (`p:limits-trace`).  The sentence needs a
von Neumann algebra in standard form whose left and right actions generate all
of `B(L²)`.  This module packages the group von Neumann algebra `L(G)` as a
Mathlib `VonNeumannAlgebra` — the double-centralizer definition, which is
exactly Murray–von Neumann's — and proves the generation statement over an ICC
group, on the commutant computed in
`Analysis/TwoSidedRegularCommutant.lean`.

* `star_leftRegularOperator` — the adjoint of a left translation is the
  translation by the inverse (the right-translation half is already in
  `Analysis/ReducedGroupCStarTraceFaithful.lean`).
* `groupVonNeumannAlgebra` — `L(G) = λ(G)''`, a `VonNeumannAlgebra` on
  `ℓ²(G)`: the double centralizer of the left regular image, star-closed
  because the image is, equal to its own double commutant by the triple
  centralizer identity.
* `leftRegularOperator_mem`, `commutes_rightRegularOperator` — `λ(G) ⊆ L(G)`,
  and every element of `L(G)` commutes with every right translation (the
  right regular image lies in `λ(G)'`).
* `centralizer_union_eq_smul_one`, `doubleCentralizer_union_eq_univ` — over an
  ICC group the commutant of `λ(G) ∪ ρ(G)` is exactly the scalars, so the von
  Neumann algebra the two regular representations generate is all of
  `B(ℓ²(G))`.
* `exists_smul_one_of_mem_center` — factoriality: a central element of `L(G)`
  is a scalar, because it commutes with both regular representations.

The trace on `L(G)`, its faithfulness and finiteness, and the II₁ assembly are
the next modules' work.
-/

namespace GroupApproximation
namespace GroupVonNeumann

open ReducedGroupCStarTrace TwoSidedRegularCommutant

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-! ## Adjoints of the translations -/

/-- The adjoint of a left translation is translation by the inverse. -/
theorem star_leftRegularOperator (g : G) :
    star (leftRegularOperator G g) = leftRegularOperator G g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
    (leftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change f (g * x) = f ((g⁻¹)⁻¹ * x)
  rw [inv_inv]

/-- The left regular image is star-closed. -/
theorem star_mem_range_leftRegularOperator {a : GroupHilbert G →L[ℂ] GroupHilbert G}
    (ha : a ∈ Set.range (leftRegularOperator G)) :
    star a ∈ Set.range (leftRegularOperator G) := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨g⁻¹, (star_leftRegularOperator G g).symm⟩

/-- The right regular image is star-closed. -/
theorem star_mem_range_rightRegularOperator {a : GroupHilbert G →L[ℂ] GroupHilbert G}
    (ha : a ∈ Set.range (rightRegularOperator G)) :
    star a ∈ Set.range (rightRegularOperator G) := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨g⁻¹, (star_rightRegularOperator G g).symm⟩

/-! ## `L(G)` as a von Neumann algebra -/

/-- **The group von Neumann algebra** `L(G) = λ(G)''`: the double centralizer
of the left regular image, as a concrete `VonNeumannAlgebra` on `ℓ²(G)`. -/
def groupVonNeumannAlgebra : VonNeumannAlgebra (GroupHilbert G) where
  toStarSubalgebra :=
    { Subalgebra.centralizer ℂ
        (Set.centralizer (Set.range (leftRegularOperator G))) with
      star_mem' := fun {_} ha ↦
        Set.star_mem_centralizer'
          (fun _ hb ↦ Set.star_mem_centralizer'
            (fun _ hm ↦ star_mem_range_leftRegularOperator G hm) hb) ha }
  centralizer_centralizer' :=
    Set.centralizer_centralizer_centralizer
      (Set.centralizer (Set.range (leftRegularOperator G)))

theorem mem_groupVonNeumannAlgebra_iff {T : GroupHilbert G →L[ℂ] GroupHilbert G} :
    T ∈ groupVonNeumannAlgebra G ↔
      T ∈ Set.centralizer
        (Set.centralizer (Set.range (leftRegularOperator G))) :=
  Iff.rfl

/-- `λ(G) ⊆ L(G)`. -/
theorem leftRegularOperator_mem (g : G) :
    leftRegularOperator G g ∈ groupVonNeumannAlgebra G :=
  Set.subset_centralizer_centralizer ⟨g, rfl⟩

/-- Every right translation lies in the commutant `λ(G)'`. -/
theorem rightRegularOperator_mem_centralizer (g : G) :
    rightRegularOperator G g ∈
      Set.centralizer (Set.range (leftRegularOperator G)) := by
  rintro m ⟨h, rfl⟩
  exact leftRegularOperator_comm_rightRegularOperator G h g

/-- Every element of `L(G)` commutes with every right translation. -/
theorem commutes_rightRegularOperator
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G) (g : G) :
    rightRegularOperator G g * T = T * rightRegularOperator G g :=
  hT _ (rightRegularOperator_mem_centralizer G g)

/-! ## Generation in standard form -/

/-- **The commutant of the two regular representations is exactly the
scalars** over an ICC group.  One inclusion is the coefficient computation of
`Analysis/TwoSidedRegularCommutant.lean`; the other is that scalars commute
with everything. -/
theorem centralizer_union_eq_smul_one (hG : IsICC G) :
    Set.centralizer (Set.range (leftRegularOperator G)
        ∪ Set.range (rightRegularOperator G))
      = Set.range
          (fun c : ℂ ↦ c • (1 : GroupHilbert G →L[ℂ] GroupHilbert G)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨c, hc⟩ := exists_smul_one_of_mem_centralizer G hG hT
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    intro m _hm
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- **The two regular representations generate `B(ℓ²(G))`** over an ICC
group: the double centralizer of `λ(G) ∪ ρ(G)` — the von Neumann algebra the
two actions generate — is everything. -/
theorem doubleCentralizer_union_eq_univ (hG : IsICC G) :
    Set.centralizer (Set.centralizer
        (Set.range (leftRegularOperator G)
          ∪ Set.range (rightRegularOperator G)))
      = Set.univ := by
  rw [centralizer_union_eq_smul_one G hG]
  ext T
  simp only [Set.mem_univ, iff_true]
  rintro m ⟨c, rfl⟩
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-! ## Factoriality -/

/-- **`L(G)` is a factor** over an ICC group: a central element commutes with
both regular representations — with `λ(G)` because it lies in `L(G)`'s
commutant relation, with `ρ(G)` because all of `L(G)` does — hence is a
scalar. -/
theorem exists_smul_one_of_mem_center (hG : IsICC G)
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G)
    (hcentral : ∀ S ∈ groupVonNeumannAlgebra G, T * S = S * T) :
    ∃ c : ℂ, T = c • 1 := by
  apply exists_smul_one_of_mem_centralizer G hG
  rintro m (hm | hm)
  · obtain ⟨g, rfl⟩ := hm
    exact (hcentral _ (leftRegularOperator_mem G g)).symm
  · obtain ⟨g, rfl⟩ := hm
    exact commutes_rightRegularOperator G hT g

end

end GroupVonNeumann
end GroupApproximation
