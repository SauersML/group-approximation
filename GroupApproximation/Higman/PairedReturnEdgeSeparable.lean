import GroupApproximation.Higman.PairedReturnFirstRangeProfinitePromotion
import GroupApproximation.Sofic.ProfiniteFiniteIndexPromotion

/-!
# Profinite separability of the paired-return edge

The paired edge `M` is a retract after passing to one finite-index subgroup
of `F₃ × F₃`.  Namely, restrict the first coordinate to the even
`a`-parity subgroup.  Reading that coordinate recovers the two-copy word
which parametrizes `M`.  Finite-index promotion therefore makes `M`
profinitely closed in the full product.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnEdgeSeparable

open Conj
open PairedReturnEdgeGraph
open PairedReturnFirstRangeVirtualRetract
open PairedReturnFirstRangeProfinitePromotion

abbrev P : Type := PairedReturnGraphIntersection.P

/-- The parity action on the first coordinate of the product. -/
def evenBaseAct : P →* Equiv.Perm Bool :=
  stateAct.comp (MonoidHom.fst F₃ F₃)

/-- Restrict the first coordinate to even `a`-parity. -/
def EvenBase : Subgroup P := evenBaseAct.ker

instance evenBase_finiteIndex : EvenBase.FiniteIndex := by
  exact finiteIndex_comap_of_normal evenBaseAct (⊥ : Subgroup (Equiv.Perm Bool))

/-- The paired edge parametrization, with codomain restricted to `EvenBase`. -/
def muEven : Double →* EvenBase where
  toFun z := ⟨PairedReturnGraphIntersection.mu z, by
    rw [EvenBase, MonoidHom.mem_ker]
    change stateAct (PairedReturnGraphIntersection.mu z).1 = 1
    rw [mu_eq_graph]
    exact MonoidHom.mem_ker.mp (firstPath_mem_Even z)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

/-- First projection, remembering that its value has even parity. -/
def evenBaseFirst : EvenBase →* Even where
  toFun p := ⟨p.1.1, by
    change stateAct ((MonoidHom.fst F₃ F₃) (p : P)) = 1
    exact p.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- Read a paired word back from the even first coordinate. -/
def evenBaseRead : EvenBase →* Double := read.comp evenBaseFirst

theorem evenBaseRead_comp_muEven :
    evenBaseRead.comp muEven = MonoidHom.id Double := by
  apply DFunLike.ext
  intro z
  change evenBaseRead (muEven z) = z
  change PairedReturnFirstRangeVirtualRetract.read
    (evenBaseFirst (muEven z)) = z
  have hfirst : evenBaseFirst (muEven z) =
      ⟨firstPath z, firstPath_mem_Even z⟩ := by
    apply Subtype.ext
    change (PairedReturnGraphIntersection.mu z).1 = firstPath z
    rw [mu_eq_graph]
  rw [hfirst]
  exact read_firstPath z

/-- The paired edge is closed inside the finite-index even-base subgroup. -/
theorem profiniteClosure_muEven_range :
    profiniteClosure muEven.range = muEven.range := by
  exact profiniteClosure_range_eq_range_of_retraction
    muEven evenBaseRead evenBaseRead_comp_muEven

/-- Including the restricted parametrization into `P` recovers the original
paired edge exactly. -/
theorem map_muEven_range :
    muEven.range.map EvenBase.subtype = PairedReturnGraphIntersection.M := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨z, hz⟩ := hq
    refine ⟨z, ?_⟩
    change PairedReturnGraphIntersection.mu z = (q : P)
    exact congrArg Subtype.val hz
  · intro hp
    obtain ⟨z, hz⟩ := hp
    refine ⟨muEven z, ⟨z, rfl⟩, ?_⟩
    exact hz

/-- **The four-generator paired-return edge is profinitely closed in
`F₃ × F₃`.** -/
theorem profiniteClosure_edge :
    profiniteClosure PairedReturnGraphIntersection.M =
      PairedReturnGraphIntersection.M := by
  have h := profiniteClosure_map_subtype_eq_of_closed EvenBase muEven.range
    profiniteClosure_muEven_range
  rwa [map_muEven_range] at h

end PairedReturnEdgeSeparable
end Higman
end GroupApproximation
