import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work: Bachner--Dogon--Lubotzky, the two notions

Census row `9e2046c330c8`, `non_mf_groups_exist.tex` lines 351--353
(Related work):

> Bachner--Dogon--Lubotzky showed that for groups of Deligne type,
> operator--Hilbert--Schmidt stability would imply that the group is not
> MF~\cite[Proposition~1.5]{BDL}.

`\bibitem[BDL]`: B. Bachner, A. Dogon, A. Lubotzky, *On `L¹`-approximation of
groups*, J. Algebra 702 (2026), arXiv:2508.17392.

This file defines the two notions in the sentence. The implication is proved
in `RelatedBDL/Proposition15.lean`.

## Deligne type

In [BDL], a group of *Deligne type* is a finitely generated group `Γ` with a
central element `J` of order `2` in the residually-finite kernel
`ker_RF(Γ) = ⋂ {N ◁ Γ : [Γ : N] < ∞}`. Deligne's central extension of
`Sp_{2g}(ℤ)` is the model case. `IsDeligneType` states this literally:

* `Group.FG Γ`;
* `orderOf J = 2`;
* `J` commutes with every element;
* `J` maps to `1` under every homomorphism to a finite group.

The last clause is exactly `J ∈ ker_RF(Γ)`. A finite-index normal subgroup
gives the finite quotient `Γ ⧸ N`. Conversely, the kernel of a map to a finite
group has finite index.

## Operator--Hilbert--Schmidt stability

An *operator-norm asymptotic homomorphism* is a sequence of maps
`φ_n : Γ → U(k_n)` whose multiplicative defects
`‖φ_n(gh) − φ_n(g) φ_n(h)‖_op` tend to `0` for all `g, h`. The group is
*operator--Hilbert--Schmidt stable* if every such sequence is close to genuine
homomorphisms `ψ_n : Γ → U(k_n)` in the normalized Hilbert--Schmidt norm:
`‖φ_n(g) − ψ_n(g)‖_HS → 0` for every `g`.

`IsOperatorHSStable` states this with these choices:

* `U(k)` is `Matrix.unitaryGroup (Fin k) ℂ`, written through the corpus finite
  model `naturalFiniteModel k`.
* `‖·‖` is the `L²`-operator norm (`Matrix.Norms.L2Operator`).
* `hsNorm Y A = √((1/|Y|) Σ |A_ij|²)` is the normalized Hilbert--Schmidt
  norm of the corpus.
* Dimensions are positive, and no normalization `φ_n(1) = 1` is imposed.
  Restricting the dimensions only weakens the stability hypothesis, which
  makes the implication proved from it stronger.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBDL

open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- **Deligne type** [BDL]: a finitely generated group with a central element
of order `2` that dies in every finite quotient, i.e. lies in `ker_RF`. -/
def IsDeligneType (Γ : Type) [Group Γ] : Prop :=
  Group.FG Γ ∧ ∃ J : Γ, orderOf J = 2 ∧ (∀ g : Γ, g * J = J * g) ∧
    ∀ (F : Type) [Group F] [Finite F] (f : Γ →* F), f J = 1

/-- **Operator--Hilbert--Schmidt stability** [BDL]: every operator-norm
asymptotic homomorphism into unitary groups of positive dimensions is
Hilbert--Schmidt close to a sequence of genuine unitary representations. -/
def IsOperatorHSStable (Γ : Type) [Group Γ] : Prop :=
  ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
    ∀ V : ∀ n, Γ → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ,
      (∀ g h : Γ, Tendsto (fun n ↦
        ‖(V n (g * h) : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) -
          (V n g : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) *
          (V n h : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ)‖) atTop (𝓝 0)) →
      ∃ ψ : ∀ n, Γ →* Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ,
        ∀ g : Γ, Tendsto (fun n ↦
          hsNorm (naturalFiniteModel (d n))
            ((V n g : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ) -
              (ψ n g : Matrix (naturalFiniteModel (d n))
                (naturalFiniteModel (d n)) ℂ))) atTop (𝓝 0)

end RelatedBDL
end NonMF
end Manuscript
end GroupApproximation
