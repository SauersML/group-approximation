import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblemPrimrec
import GroupApproximation.Meta.AxiomGuard

/-!
# The word problem of `Λ`

`simple_kazhdan_sofic_group.tex`, proof of `cor:lef`, second statement:

> An element $x\mapsto\delta x+c$ of $\Lambda$ is given by a word for $\delta$ and words for the lamps
> of $c$, so the word problem of $\Delta$ decides equality in $\Lambda$ and computes the values of $c$.

## Proof route

The generators of `Λ` are the lamp `lampAdd` and the translations `inr (t i)`. A word multiplies out
to `inl (ofAdd (lampSum t w)) * inr (wordValue t (deltaWord w))` (`wordValue_lampGen`), which is trivial
if and only if the `Δ`-word `deltaWord w` is trivial and every lamp position occurs an even number of
times. The positions are compared by finitely many `Δ` word-problem queries, which is a primitive
recursive truth-table reduction (`Lamplighter.hasSolvableWordProblem_lampAffine`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LamplighterWP

/-- **The word problem of `Δ` decides equality in `Λ`**: if `Δ` has solvable word problem, so has
the affine lamplighter group `Λ`. -/
theorem affineProof : Lamplighter.PrintedLamplighterAffineSolvableWordProblem :=
  Lamplighter.printedLamplighterAffineSolvableWordProblem

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.affineProof

end LamplighterWP
end SimpleKazhdanSofic
end GroupApproximation
