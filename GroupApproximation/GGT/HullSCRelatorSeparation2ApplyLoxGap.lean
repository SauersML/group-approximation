import GroupApproximation.GGT.HullSCRelatorSeparation2Core

/-!
# Why the diagonal leaf's route is closed

The Ledger recorded the diagonal clause of the separation as discharged, by
`HullSC.noCommute_of_torsionFree` over `GGT/OsinTheorem54SepElementaryBall.lean`
--- "it holds for every loxodromic; nothing has to be chosen".  The lemma is
sound; its hypothesis cannot be met at this core.

It asks its element to be loxodromic in `Γ(G, X ⊔ ⨆H)`, the RELATIVE graph
whose relative ball the conclusion is about.  The relator's letters are powers
of `E.lox b`, and `HullSC.HypEmbeddedCore₂.lox_mem` puts `E.lox b` in `H b`,
which is part of the relative alphabet.  So `(E.lox b) ^ n` is a single letter
of that graph for every `n`, the orbit of the basepoint has diameter at most
one, and no positive linear lower bound is available.

That fact was already in the tree, at the file that defines the relative
generating set: `GGT.RelGenSet.not_isLoxodromic_of_mem_fam`.  All that is added
here is its instance at the core, so that the incompatibility is on record at
the place the composition needed it.  It does not say the diagonal clause is
false; it says this route to it is closed.

**What the clause would need.**  Not torsion-freeness by itself.  Both `x` and
the loxodromic lie in `H λ`, so if `H λ` is abelian --- and `E(g)` in a
torsion-free group is infinite cyclic --- then `x` commutes with every power and
the clause fails for every `x ≠ 1` of the ball.  What it needs is that
`relBall λ eps` meets the centralizer of `E.lox λ` trivially, which is a
condition on the core rather than on the group.

**And the chain no longer asks for it.**  Hull excludes the conjugacy identity
syntactically rather than by a clause about commutation, and what makes the
aligned case's connector trivial is (W4), `H₀ ∩ H₁ = {1}`, carried as the field
`HullSC.HypEmbeddedCore₂.disjoint` and spent by
`HullSC.trivialGap_of_two_connectors`.  So nothing downstream carries `hnc`;
this file records a closed route, not a standing debt.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section LoxGap

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The two elements of the relator's run are elliptic in the relative
graph.**  They lie in the family, and the family is part of the relative
alphabet, so `GGT.RelGenSet.not_isLoxodromic_of_mem_fam` applies. -/
theorem not_isLoxodromic_lox₂ (E : HypEmbeddedCore₂ A N) (b : Bool) :
    ¬ IsLoxodromic (E.lox b) (Cayley.base E.rel.alphabet) := by
  refine GGT.RelGenSet.not_isLoxodromic_of_mem_fam E.rel b ?_
  rw [E.fam_eq]
  exact E.lox_mem b

end LoxGap

end HullSC
end GroupApproximation
