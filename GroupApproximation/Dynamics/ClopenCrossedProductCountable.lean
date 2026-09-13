import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.List

/-!
# The clopen crossed product is countable

`non_mf_groups_exist.tex`, proof of `thm:core-mf-radical`, tex 1647–1649:

> Its countability hypothesis holds because $X$ has a countable clopen basis and each clopen
> subset is a finite union of basis sets.

* `exists_finite_subset_sUnion_eq_of_isClopen`: in a compact space every clopen set is a finite
  union of sets from any given basis (compactness of the clopen set).
* `exists_countable_clopen_basis`: a compact Hausdorff totally disconnected second countable space
  has a countable clopen basis.
* `countable_setOf_isClopen`: a compact second countable space has countably many clopen sets
  (finite subsets of a countable basis).
* `countable_locallyConstant`: with countable values, a locally constant function is determined by
  the finite set of its values paired with their clopen fibers.
* `ClopenCrossedProduct.countable`: `R_X` is countable for every compact second countable `X` and
  every countable coefficient ring, via the Laurent coefficients `ℤ →₀ LC(X, k)`.
* Closed endpoints at the printed generality: `printedCountableClopenBasis` and
  `printedClopenCrossedProductCountable` (compact metrizable totally disconnected `X`, finite field
  `k`).  The additive wrappers of the consumers' Props are in
  `Manuscript/ChainCore/ClopenCrossedProductCountableConsumers.lean`.
-/

namespace GroupApproximation

open TopologicalSpace

section Clopen

variable {X : Type*} [TopologicalSpace X]

/-- **"each clopen subset is a finite union of basis sets"** (tex 1648–1649), for any basis of a
compact space. -/
theorem exists_finite_subset_sUnion_eq_of_isClopen [CompactSpace X] {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {U : Set X} (hU : IsClopen U) :
    ∃ s ⊆ B, s.Finite ∧ U = ⋃₀ s := by
  classical
  let S : Set (Set X) := {V | V ∈ B ∧ V ⊆ U}
  have hcover : U ⊆ ⋃ V : S, (V : Set X) := by
    intro x hx
    obtain ⟨V, hVB, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx hU.isOpen
    exact Set.mem_iUnion.2 ⟨⟨V, hVB, hVU⟩, hxV⟩
  obtain ⟨t, ht⟩ := hU.isClosed.isCompact.elim_finite_subcover (fun V : S ↦ (V : Set X))
    (fun V ↦ hB.isOpen V.2.1) hcover
  refine ⟨Subtype.val '' (t : Set S), ?_, t.finite_toSet.image _, ?_⟩
  · rintro _ ⟨V, -, rfl⟩
    exact V.2.1
  · refine Set.Subset.antisymm (fun x hx ↦ ?_) ?_
    · obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact ⟨(V : Set X), ⟨V, hVt, rfl⟩, hxV⟩
    · rintro x ⟨_, ⟨V, -, rfl⟩, hxV⟩
      exact V.2.2 hxV

/-- **"`X` has a countable clopen basis"** (tex 1648). -/
theorem exists_countable_clopen_basis [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [SecondCountableTopology X] :
    ∃ B : Set (Set X), B.Countable ∧ (∀ U ∈ B, IsClopen U) ∧ IsTopologicalBasis B := by
  obtain ⟨B, hBsub, hBc, hB⟩ := isTopologicalBasis_isClopen.exists_countable (α := X)
  exact ⟨B, hBc, fun _ hU ↦ hBsub hU, hB⟩

/-- A compact second countable space has countably many clopen subsets. -/
theorem countable_setOf_isClopen [CompactSpace X] [SecondCountableTopology X] :
    {U : Set X | IsClopen U}.Countable := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis X
  refine ((Set.countable_setOf_finite_subset hBc).image Set.sUnion).mono ?_
  intro U hU
  obtain ⟨s, hsB, hs, rfl⟩ := exists_finite_subset_sUnion_eq_of_isClopen hB hU
  exact ⟨s, ⟨hs, hsB⟩, rfl⟩

/-- Locally constant functions with countably many values on a compact second countable space form
a countable set: such a function is determined by its finitely many values and their clopen
fibers. -/
theorem countable_locallyConstant [CompactSpace X] [SecondCountableTopology X] (k : Type*)
    [Countable k] : Countable (LocallyConstant X k) := by
  classical
  haveI : Countable {U : Set X // IsClopen U} := countable_setOf_isClopen.to_subtype
  let code : LocallyConstant X k → Finset (k × {U : Set X // IsClopen U}) := fun f ↦
    f.range_finite.toFinset.image fun a ↦
      (a, ⟨{x | f x = a}, f.isLocallyConstant.isClopen_fiber a⟩)
  refine Function.Injective.countable (f := code) fun f g hfg ↦ LocallyConstant.ext fun x ↦ ?_
  have hmem : (f x, (⟨{y | f y = f x}, f.isLocallyConstant.isClopen_fiber (f x)⟩ :
      {U : Set X // IsClopen U})) ∈ code f :=
    Finset.mem_image.2 ⟨f x, f.range_finite.mem_toFinset.2 ⟨x, rfl⟩, rfl⟩
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 ((Finset.ext_iff.1 hfg _).1 hmem)
  have h1 : a = f x := congrArg Prod.fst ha
  have h2 : {y | g y = a} = {y | f y = f x} := congrArg (fun p ↦ p.2.1) ha
  have hx : g x = a := by
    have hxf : x ∈ {y | f y = f x} := rfl
    rw [← h2] at hxf
    exact hxf
  exact (hx.trans h1).symm

end Clopen

/-- **`R_X` is countable** for a compact second countable `X` and a countable coefficient ring `k`:
the Laurent coefficients `x ↦ x.coeff : ℤ →₀ LC(X, k)` are injective. -/
theorem ClopenCrossedProduct.countable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] (T : X ≃ₜ X) (k : Type*) [Ring k] [Countable k] :
    Countable (ClopenCrossedProduct T k) := by
  haveI : Countable (ClopenCoeff T k) := countable_locallyConstant (X := X) k
  haveI : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  exact Function.Injective.countable
    (f := fun x : ClopenCrossedProduct T k ↦ SkewMonoidAlgebra.coeff x)
    fun x y (h : SkewMonoidAlgebra.coeff x = SkewMonoidAlgebra.coeff y) ↦
      congrArg SkewMonoidAlgebra.ofCoeff h

/-- **tex 1647–1649**, "$X$ has a countable clopen basis and each clopen subset is a finite union of
basis sets", for the compact metrizable zero-dimensional spaces of `sec:chain-core`. -/
def PrintedCountableClopenBasis : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X],
    ∃ B : Set (Set X), B.Countable ∧ (∀ U ∈ B, IsClopen U) ∧ IsTopologicalBasis B ∧
      ∀ U : Set X, IsClopen U → ∃ s ⊆ B, s.Finite ∧ U = ⋃₀ s

theorem printedCountableClopenBasis : PrintedCountableClopenBasis := by
  intro X _ _ _ _
  obtain ⟨B, hBc, hBclopen, hB⟩ := exists_countable_clopen_basis (X := X)
  exact ⟨B, hBc, hBclopen, hB, fun _ hU ↦ exists_finite_subset_sUnion_eq_of_isClopen hB hU⟩

/-- **tex 1647–1649**, "Its countability hypothesis holds": `R_X` is countable for every compact
metrizable totally disconnected `X`, homeomorphism `T` and finite field `k`. -/
def PrintedClopenCrossedProductCountable : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (k : Type) [Field k] [Finite k],
      Countable (ClopenCrossedProduct T k)

theorem printedClopenCrossedProductCountable : PrintedClopenCrossedProductCountable :=
  fun _ _ _ _ _ T k _ _ ↦ ClopenCrossedProduct.countable T k

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.printedCountableClopenBasis
#audit_closed_axioms GroupApproximation.printedClopenCrossedProductCountable
#audit_axioms GroupApproximation.ClopenCrossedProduct.countable
#audit_axioms GroupApproximation.countable_locallyConstant
