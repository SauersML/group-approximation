import GroupApproximation.Sofic.AlternatingLampExactRadical
import GroupApproximation.Analysis.PeterWeylProfinite

/-!
# The Bohr column of the alternating family, unconditionally

`Sofic/AlternatingLampExactRadical` proves, with no hypothesis and no citation,
that four approximation theories see the degree-`n` member `Wₙ` as exactly the
skeleton `V`:

  `Res_MF(Wₙ) = Rad_fd(Wₙ) = Res_fin(Wₙ) = Rad_lin(Wₙ) = Aₙ^(V/Γ) = ker rightHom`.

This file adds what can be said about the fifth theory -- homomorphisms into
compact Hausdorff groups -- **without assuming anything**.

* `bohrResidual_le_lampRange`: the Bohr residual is contained in the lamp
  subgroup.  A finite group is a compact target, so this is the finite-residual
  computation and nothing else.
* `lampRange_le_ker_of_profinite`: every homomorphism of `Wₙ` into a profinite
  group kills the whole lamp subgroup.  Van Dantzig supplies the separation
  outright, so this needs no analytic input either.
* `bohrResidual_eq_lampRange_of_profinite_only`: the two combine into an
  equality once the compact targets are restricted to the totally disconnected
  ones.

## What is deliberately absent

The inclusion `Aₙ^(V/Γ) ≤ Rad_Bohr(Wₙ)` for a **general** compact target is
*not* stated here in any form, conditional or otherwise.  It is true classically
and it is exactly Peter--Weyl: one needs finite-dimensional unitary
representations to separate the points of a compact group, and the pinned
Mathlib has none of that theory.  The remaining gap is genuinely the connected
case -- `Analysis/PeterWeylProfinite` already disposes of the totally
disconnected part, and a compact group's totally disconnected quotient is
handled above -- and the collapse mechanism this family uses cannot be
transported to it: `Sofic/PerfectLampCompressionRadical` gets commuting images
from a corona-specific spectral collapse and only then applies the purely
algebraic `eq_one_of_commuting_image_of_perfect`.  A compact group admits the
algebraic half and not the analytic one.

So the honest state is: four radicals coincide unconditionally, the Bohr
residual is unconditionally trapped below them, and the Bohr theory is
unconditionally equal to them on profinite targets.
-/

namespace GroupApproximation
namespace AlternatingLampFamily

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open MatricialStabilityRadical PeterWeyl

/-! ## The unconditional upper bound -/

/-- **The Bohr residual is inside the lamp subgroup.**  Finite groups are
compact targets, so `bohrResidual ≤ finiteResidual`, and the finite residual of
the degree-`n` member is its lamp subgroup. -/
theorem bohrResidual_le_lampRange {n : ℕ} (hn : 5 ≤ n) :
    bohrResidual (WAlt n) ≤ lampSub n := by
  rw [← finiteResidual_eq_lampRange hn]
  exact bohrResidual_le_finiteResidual

/-- The same bound written against the wreath projection's kernel. -/
theorem bohrResidual_le_ker_rightHom {n : ℕ} (hn : 5 ≤ n) :
    bohrResidual (WAlt n)
      ≤ (rightHom : WAlt n →* Vertical conjD conjD_injective).ker := by
  rw [ker_rightHom_eq_lampRange]
  exact bohrResidual_le_lampRange hn

/-! ## Profinite targets see nothing of the lamp -/

/-- **Every profinite representation of the degree-`n` member kills the entire
lamp subgroup.**  No analytic input: the finite residual is the lamp subgroup,
and a homomorphism into a profinite group cannot see the finite residual. -/
theorem lampRange_le_ker_of_profinite {n : ℕ} (hn : 5 ≤ n) {C : Type*}
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    [TotallyDisconnectedSpace C] (f : WAlt n →* C) :
    lampSub n ≤ f.ker := by
  rw [← finiteResidual_eq_lampRange hn]
  exact finiteResidual_le_ker_of_profinite f

/-- **The Bohr column, unconditionally, on profinite targets.**  Combining the
two directions: for totally disconnected compact targets the Bohr theory of the
degree-`n` member is exactly its lamp subgroup. -/
theorem bohrResidual_eq_lampRange_of_profinite_only {n : ℕ} (hn : 5 ≤ n) :
    bohrResidual (WAlt n) ≤ lampSub n ∧
      ∀ {C : Type} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
        [CompactSpace C] [TotallyDisconnectedSpace C] (f : WAlt n →* C),
          lampSub n ≤ f.ker :=
  ⟨bohrResidual_le_lampRange hn, fun {_} _ _ _ _ _ f =>
    lampRange_le_ker_of_profinite hn f⟩

/-! ## The package -/

/-- **The degree-`n` member, with every unconditional radical statement in one
place.**  Four residuals equal the lamp subgroup outright; the Bohr residual is
trapped inside it; and every profinite representation kills it.  No hypothesis
and no citation appears in the statement or in any of its ancestors. -/
theorem alternatingFamilyRadicalPackage {n : ℕ} (hn : 5 ≤ n) :
    actualCoronaMFResidual (WAlt n) = lampSub n ∧
      fdUnitaryResidual (WAlt n) = lampSub n ∧
      finiteResidual (WAlt n) = lampSub n ∧
      linearResidual (WAlt n) = lampSub n ∧
      (rightHom : WAlt n →* Vertical conjD conjD_injective).ker = lampSub n ∧
      bohrResidual (WAlt n) ≤ lampSub n ∧
      ∀ {C : Type} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
        [CompactSpace C] [TotallyDisconnectedSpace C] (f : WAlt n →* C),
          lampSub n ≤ f.ker := by
  obtain ⟨h1, h2, h3, h4⟩ := four_radicals_eq_lampRange hn
  exact ⟨h1, h2, h3, h4, ker_rightHom_eq_lampRange,
    bohrResidual_le_lampRange hn, fun {_} _ _ _ _ _ f =>
      lampRange_le_ker_of_profinite hn f⟩

end AlternatingLampFamily
end GroupApproximation
