import Mathlib.GroupTheory.OrderOfElement
import GroupApproximation.Kazhdan.KMSGroupPresentation

/-!
# CCKW Theorem 3.1(ii) for `GHB(7)`, as a named statement

Caprace–Conder–Kaluba–Witzel (arXiv:2011.09276), Theorem 3.1(ii): in a nonpositively
curved triangle of finite groups, every finite subgroup of the fundamental group is
conjugate into one of the vertex groups.  For `GHB(7)` the vertex groups are
`⟨a,b⟩ ≅ U₃(7)`, `⟨c,b⟩ ≅ U₄(7)` and `⟨c,a⟩ ≅ U₄(7)`.

The torsion-freeness of the kernel of a quotient that is injective on the vertex
groups, and the infiniteness of `GHB(7)`, use only the cyclic case: every element of
finite order is conjugate into a vertex group.  That case is the named proposition
below.  It is an open leaf of the lattice route (`Kazhdan/GHBLatticeRoute.lean`),
consumed only as an explicit hypothesis of intermediate lemmas, never as a binder of
an endpoint.

Its proof is combinatorial nonpositive curvature on the coset complex of the triangle of
groups: the complex is simply connected, its vertex links have girth at least six, so a
finite cyclic group fixes a vertex (`GGT/Systolic*`).
-/

namespace GroupApproximation
namespace KMSGroup

/-- **CCKW Theorem 3.1(ii), cyclic case, for `GHB(7)`**: every element of finite order
is conjugate into one of the three vertex groups `⟨a,b⟩`, `⟨c,b⟩`, `⟨c,a⟩`. -/
def CCKWFiniteOrderConjugateIntoVertex : Prop :=
  ∀ g : GHB 7, IsOfFinOrder g → ∃ x : GHB 7,
    x⁻¹ * g * x ∈ Subgroup.closure {a 7, b 7} ∨
      x⁻¹ * g * x ∈ Subgroup.closure {c 7, b 7} ∨
        x⁻¹ * g * x ∈ Subgroup.closure {c 7, a 7}

end KMSGroup
end GroupApproximation
