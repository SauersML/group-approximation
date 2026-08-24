import GroupApproximation.Sofic.FinitePerfectLampExactRadical

/-!
# Theorem C over the concrete datum, and the fifth column

Theorem C is proved for an abstract ascending-HNN datum in `PerfectLampExact`.
The form the paper displays fixes the *one* concrete affine doubling datum and
quantifies over the lamp group instead: for every nontrivial finite perfect `K`,

  `Res_MF(K^(V/Γ) ⋊ V) = K^(V/Γ)`,

with the member sofic, finitely generated and not MF, and with four radicals
coinciding.  `Aₙ` is one member of this family.

## The fifth column is the one conditional row

`manuscriptFinitePerfectLampFiveRadicals` takes `PeterWeyl.SeparatesPoints` as a
**leading hypothesis** rather than folding it into a named proposition.  That is
deliberate.  Folding it in would make the statement pass
`#audit_closed_axioms` — the gate does not unfold named propositions — and it
would then read exactly like the closed rows beside it.  Keeping the binder in
front means the gate rejects it, `Endpoint/MFRadicalPaperAudit` prints it with
the weaker macro, and the ledger records it as `conditional`.  It is the only
row of the package in that state, and nothing else depends on it.
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

/-- The five-radical conclusion, as a closed proposition.  It is *not* proved
unconditionally anywhere; see the theorem below. -/
def FinitePerfectLampFiveRadicals : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    actualCoronaMFResidual (WFin K) = lampSub K ∧
      fdUnitaryResidual (WFin K) = lampSub K ∧
        finiteResidual (WFin K) = lampSub K ∧
          linearResidual (WFin K) = lampSub K ∧
            PeterWeyl.bohrResidual (WFin K) = lampSub K

/-- **The fifth column, conditional on Peter--Weyl.**  The hypothesis is a
leading binder on purpose: this is the one statement of the package that is not
closed, and the audit's binder check is what says so. -/
theorem manuscriptFinitePerfectLampFiveRadicals
    (hPW : PeterWeyl.SeparatesPoints.{0}) : FinitePerfectLampFiveRadicals :=
  fun K _ _ hK => five_radicals_eq_lampSub_of_separatesPoints K hPW hK

end MFRadicals
end Manuscript
end GroupApproximation
