import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterRing

/-!
# The word problems of `Λ` and of `G_Δ`: statements

`simple_kazhdan_sofic_group.tex` at 696c4b602, section "LEF groups", proof of `cor:lef`, second
statement (l.445–455):

> An element $x\mapsto\delta x+c$ of $\Lambda$ is given by a word for $\delta$ and words for the lamps
> of $c$, so the word problem of $\Delta$ decides equality in $\Lambda$ and computes the values of $c$.
> A word in the generators of $G_\Delta$ multiplies out to a matrix with entries
> $\sum_\xi p_\xi u_\xi$, where each $p_\xi$ is a polynomial over $\F_2$ in finitely many coordinates
> $x(\delta)$, as $u_\xi e_Uu_\xi^{-1}$ is the indicator of $\{x:x(\delta)=1+c(\delta)\}$ for
> $\xi\colon x\mapsto\delta x+c$. After collecting equal $\xi$ and equal coordinates, the word is
> trivial if and only if every coefficient of its difference from $I_3$ vanishes at every assignment
> of its finitely many variables, as $\Omega$ is the full shift. So $G_\Delta$ has solvable word
> problem.

The spellings:

* `HasSolvableWordProblem` (sk-lef-assembly, over skf-degrees' `wordProblemOracle`): some finite
  generating family has a computable word problem.
* `Lamplighter.LampAffine Δ` (sk-lef-action): the affine lamplighter group `Λ` of maps `x ↦ δx + c`.
* `Lamplighter.LampRing Δ = LC(Ω, F_2) ⋊ Λ`, and `G_Δ = EL_3(R_Δ)`.

The named Props:

* `PrintedLamplighterAffineSolvableWordProblem`: the word problem of `Δ` decides equality in `Λ`.
* `PrintedLamplighterHostSolvableWordProblem`: `G_Δ` has solvable word problem.

sk-lef-assembly combines them with sk-lef-action's host theorem into
`LEFLamplighterSolvableWordProblemStatement`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter

/-- **The word problem of `Δ` decides equality in `Λ`** (tex l.445–447): if `Δ` has solvable word
problem, so has the affine lamplighter group `Λ` of maps `x ↦ δx + c`. -/
def PrintedLamplighterAffineSolvableWordProblem : Prop :=
  ∀ (Δ : Type) [Group Δ], HasSolvableWordProblem Δ → HasSolvableWordProblem (LampAffine Δ)

/-- **`G_Δ` has solvable word problem** (tex l.448–455): if `Δ` has solvable word problem, so has
`G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)`. -/
def PrintedLamplighterHostSolvableWordProblem : Prop :=
  ∀ (Δ : Type) [Group Δ], HasSolvableWordProblem Δ →
    HasSolvableWordProblem ↥(elementaryGroup (Fin 3) (LampRing Δ))

end Lamplighter
end SimpleKazhdanSofic
end GroupApproximation
