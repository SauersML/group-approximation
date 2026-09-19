import GroupApproximation.Analysis.PeterWeylSeparation
import GroupApproximation.Sofic.FinitePerfectLampExactRadical

/-!
# Theorem C over the concrete datum, and the fifth column

Theorem C is proved for an abstract ascending-HNN datum in `PerfectLampExact`.
The form the paper displays fixes the *one* concrete affine doubling datum and
quantifies over the lamp group instead: for every nontrivial finite perfect `K`,

  `Res_MF(K^(V/Γ) ⋊ V) = K^(V/Γ)`,

with the member sofic, finitely generated and not MF, and with four radicals
coinciding.  `Aₙ` is one member of this family.

## The fifth column

The Peter--Weyl separation theorem is supplied by
`Analysis/PeterWeylSeparation`, which translates the vendored Tau Ceti density
theorem into the matrix-valued formulation used by the radical calculus.
Consequently the fifth radical is now included without an external hypothesis.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

open MatricialStabilityRadical FinitePerfectLamp

/-- **Theorem C, concrete-datum form.**  Every nontrivial finite perfect lamp
group over the concrete doubling datum gives a sofic, finitely generated,
non-MF group whose four radicals are exactly its lamp subgroup. -/
def FinitePerfectLampFamily : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [Nontrivial K], commutator K = ⊤ →
    IsSofic (WFin K) ∧ ¬ IsCDEOperatorMF (WFin K) ∧ Group.FG (WFin K) ∧
      actualCoronaMFResidual (WFin K) = lampSub K ∧
      fdUnitaryResidual (WFin K) = lampSub K ∧
      finiteResidual (WFin K) = lampSub K ∧
      linearResidual (WFin K) = lampSub K

theorem manuscriptFinitePerfectLampFamily : FinitePerfectLampFamily :=
  fun K _ _ _ hK => finitePerfectPackage K hK

/-- The five-radical conclusion, as a closed proposition. -/
def FinitePerfectLampFiveRadicals : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    actualCoronaMFResidual (WFin K) = lampSub K ∧
      fdUnitaryResidual (WFin K) = lampSub K ∧
        finiteResidual (WFin K) = lampSub K ∧
          linearResidual (WFin K) = lampSub K ∧
            PeterWeyl.bohrResidual (WFin K) = lampSub K

/-- **The fifth column, unconditionally.** -/
theorem manuscriptFinitePerfectLampFiveRadicals :
    FinitePerfectLampFiveRadicals :=
  fun K _ _ hK => five_radicals_eq_lampSub_of_separatesPoints K
    PeterWeyl.separatesPoints hK

end MFRadicals
end Manuscript
end GroupApproximation
