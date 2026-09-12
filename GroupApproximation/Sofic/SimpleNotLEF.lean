import GroupApproximation.Sofic.LEF
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# An infinite simple group is not residually finite

Two elementary facts that the torsion-free saturation route uses at its last
step, and that this development did not have.

The route builds a group whose nonsoficity is deduced from a simple subgroup
failing to be LEF.  That deduction has two halves, and only the first is
delicate:

* a finitely presented LEF group is residually finite — that is the
  Vershik--Gordon direction, and it is *not* proved here;
* an infinite simple group is not residually finite — that is immediate, and
  it is proved here.

The second is what makes the contradiction bite, so it is worth having outright
rather than as a step inside a longer argument.

## The proof

Let `S` be simple and infinite, and let `f : S → F` be a homomorphism to a
finite group.  Its kernel is normal, so by simplicity it is trivial or
everything.  Trivial is impossible: `S` would embed in a finite group and be
finite.  So every homomorphism to a finite group is trivial, and no family of
them separates any nonidentity element.

The statement is deliberately phrased against homomorphisms into arbitrary
finite groups rather than against a fixed residual-finiteness predicate, so it
composes with whichever formulation a caller has.

## Scope

Nothing here is about approximation.  In particular this file does **not**
prove the Vershik--Gordon direction, and says nothing about soficity: it is
pure group theory, and the analytic content of the route lives elsewhere.

-/

namespace GroupApproximation
namespace SimpleNotLEF

variable {S : Type*} [Group S]

/-! ## Homomorphisms to finite groups -/

/-- **A homomorphism from an infinite simple group to a finite group is
trivial.**  Its kernel is normal, hence trivial or everything; trivial would
embed an infinite group into a finite one. -/
theorem eq_one_of_finite_target [IsSimpleGroup S] [Infinite S]
    {F : Type*} [Group F] [Finite F] (f : S →* F) (x : S) :
    f x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance
    with hbot | htop
  · exfalso
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hbot
    exact (Finite.of_injective f hinj).false
  · have : x ∈ f.ker := htop ▸ Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp this

/-- **An infinite simple group is not separated by finite quotients.**  No
homomorphism to a finite group distinguishes a nonidentity element from the
identity. -/
theorem not_separated_by_finite [IsSimpleGroup S] [Infinite S]
    {x : S} (_hx : x ≠ 1) :
    ¬ ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : S →* F), f x ≠ 1 := by
  rintro ⟨F, _, _, f, hfx⟩
  exact hfx (eq_one_of_finite_target f x)

/-! ## What the saturation route consumes

The route reaches a finitely presented simple group `S` sitting inside a
quotient that would have to be LEF if the ambient group were sofic.  Combining
the Vershik--Gordon direction — a finitely presented LEF group is residually
finite, **not proved here** — with `eq_one_of_finite_target` gives the
contradiction, because residual finiteness of an infinite simple group would
require a nontrivial finite quotient and there is none.

Stating the second half separately is the point: it is unconditional, it is
short, and it is the half that a reader is most likely to assume without
checking. -/

end SimpleNotLEF
end GroupApproximation
