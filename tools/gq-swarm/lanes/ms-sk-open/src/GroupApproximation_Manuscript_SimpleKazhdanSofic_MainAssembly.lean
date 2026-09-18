import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ElementaryGroupFacts
import GroupApproximation.Pestov91.Kazhdan
import GroupApproximation.Pestov91.LEFHyperlinear
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Separation.Profinite

/-!
# `thm:main` of `simple_kazhdan_sofic_group.tex`: statement and assembly

`simple_kazhdan_sofic_group.tex` at origin/main 9047d0d3c, Theorem `thm:main` (tex l.55–69):

> Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite alphabet, with shift $T$,
> and let $\LC(X,\F_2)$ be the ring of locally constant functions $X\to\F_2$. Then
> $G_X=\EL_3\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ is an infinite, finitely generated, simple group
> with Kazhdan's property (T). It is the limit, in the space of marked groups, of finite simple
> groups $\SL_{3N}(\F_2)$ whose Cayley graphs, with respect to the images of a fixed generating set,
> form a family of expanders. So $G_X$ is locally embeddable into finite groups (LEF), sofic and
> hyperlinear. The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ for every $n\ge3$, with
> $\SL_{nN}(\F_2)$ in place of $\SL_{3N}(\F_2)$.

The setting is `SimpleKazhdanSofic.Setting` (lane ms-intro-3): `Subshift A ℤ`, `IsMinimal`, the shift
`subshiftHomeo`, `R S = LC(X, F₂) ⋊_T ℤ`, and `G S = EL₃(R S)`.

## Definitions

* `IsMarkedLimit s σ`: generated groups `(H ℓ, σ ℓ)` converge to `(G, s)` in the space of marked
  groups.  Every word in the generators is, for all large `ℓ`, trivial in `H ℓ` exactly when it is
  trivial in `G`.
* `IsExpanderFamily σ`: the Cayley graphs of the finite groups `H ℓ` with respect to `σ ℓ` form a
  family of expanders.  The generating family is finite, the orders tend to infinity, and there is
  `ε > 0` such that every `S ⊆ H ℓ` with `2|S| ≤ |H ℓ|` has at least `ε|S|` edges `x → σ_i x`
  leaving `S`.
* `PrintedMarkedLimitExpanders S n`: `EL_n(R S)` is such a limit of finite simple groups
  `SL_{nN}(F₂)`, indexed by `Fin n × Fin N`, with expanding Cayley graphs.

## Pieces (named propositions, with the owning lanes)

* `PrintedSubshiftRingFGStatement`: `R` is a finitely generated ring (tex l.111–113; ct-involution);
* `PrintedSimplicityStatement`: `EL_n(R)` is simple for every `n ≥ 3` (section "Simplicity", tex
  l.188–253; skf-consequences and ct-bilateral-mf);
* `PrintedMarkedLimitExpandersStatement`: the marked limits and expanders (section "Finite models",
  tex l.162–185; ms-core-3 for the marked convergence, oa-expanders for the expanders);
* `PrintedMarkedLimitLEFStatement`: a marked limit of finite groups is LEF (tex l.177–180; closed in
  `SimpleKazhdanSofic.MarkedLimitLEF`).

Property (T) is Ershov–Jaikin-Zapirain, proved in this repository
(`Pestov91.elementary_hasKazhdanPropertyT`).  A Kazhdan group is finitely generated
(`KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`); the note instead reads finite generation off
the generating matrices (tex l.123–124, lane ms-compress-4).  `EL_n(R)` is infinite because
`e_{12}(LC(X, F₂))` is infinite (tex l.127–128; `infinite_locallyConstant_zmodTwo`, lane
ms-compress-4).  LEF groups are sofic and hyperlinear (tex l.185–187).

`printedSimpleKazhdanSoficMain_of_pieces` assembles the theorem from the four pieces.  Each clause
has its own lemma, so that elaboration stays small.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift Set Filter

/-! ## Marked limits and expanders -/

/-- **Convergence in the space of marked groups**: the generated groups `(H ℓ, σ ℓ)` converge to
`(G, s)`.  Every word in the generators is, for all large `ℓ`, trivial in `H ℓ` exactly when it is
trivial in `G`. -/
def IsMarkedLimit {ι G : Type*} [Group G] (s : ι → G) {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)]
    (σ : ∀ ℓ, ι → H ℓ) : Prop :=
  Subgroup.closure (Set.range s) = ⊤ ∧ (∀ ℓ, Subgroup.closure (Set.range (σ ℓ)) = ⊤) ∧
    ∀ w : FreeGroup ι, ∀ᶠ ℓ in atTop, (FreeGroup.lift (σ ℓ) w = 1 ↔ FreeGroup.lift s w = 1)

/-- **A family of expanders**: the Cayley graphs of the finite groups `H ℓ` with respect to the
finite generating families `σ ℓ` have orders tending to infinity and uniform edge expansion.  Every
`S ⊆ H ℓ` with `2|S| ≤ |H ℓ|` has at least `ε|S|` edges `x → σ_i x` leaving `S`. -/
def IsExpanderFamily {ι : Type*} {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)] (σ : ∀ ℓ, ι → H ℓ) : Prop :=
  Finite ι ∧ (∀ ℓ, Finite (H ℓ)) ∧ Tendsto (fun ℓ => Nat.card (H ℓ)) atTop atTop ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ℓ : ℕ) (S : Set (H ℓ)), 2 * S.ncard ≤ Nat.card (H ℓ) →
      ε * S.ncard ≤ ({p : H ℓ × ι | p.1 ∈ S ∧ σ ℓ p.2 * p.1 ∉ S} : Set (H ℓ × ι)).ncard

section Statement

variable {A : Type} [TopologicalSpace A]

/-- **The marked-limit clause of `thm:main`** (tex l.63–65, l.67–68): `EL_n(R S)` is the limit, in
the space of marked groups, of finite simple groups `SL_{nN}(F₂)` whose Cayley graphs, with respect
to the images of a fixed generating set, form a family of expanders. -/
def PrintedMarkedLimitExpanders (S : Subshift A ℤ) (n : ℕ) : Prop :=
  ∃ (ι : Type) (s : ι → ↥(elementaryGroup (Fin n) (R S))) (N : ℕ → ℕ)
    (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2)),
    (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2))) ∧
      IsMarkedLimit s σ ∧ IsExpanderFamily σ

end Statement

/-- **Theorem `thm:main` as printed** (tex l.55–69), for every `n ≥ 3`; `n = 3` is `G_X = G S`. -/
def PrintedSimpleKazhdanSoficMain : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ∀ n : ℕ, 3 ≤ n →
      Infinite ↥(elementaryGroup (Fin n) (R S)) ∧ Group.FG ↥(elementaryGroup (Fin n) (R S)) ∧
        IsSimpleGroup ↥(elementaryGroup (Fin n) (R S)) ∧
        HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin n) (R S)) ∧
        PrintedMarkedLimitExpanders S n ∧ IsLEF ↥(elementaryGroup (Fin n) (R S)) ∧
        IsSofic ↥(elementaryGroup (Fin n) (R S)) ∧ IsHyperlinear ↥(elementaryGroup (Fin n) (R S))

/-! ## Pieces -/

/-- **`R` is finitely generated** (tex l.111–113): it is generated by `u^{±1}` and the letter
indicators. -/
def PrintedSubshiftRingFGStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    IsFinitelyGeneratedRing (R S)

/-- **Simplicity** (section "Simplicity", tex l.188–253): for an infinite minimal subshift, `EL_n(R)`
is simple for every `n ≥ 3`. -/
def PrintedSimplicityStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ∀ n : ℕ, 3 ≤ n →
      IsSimpleGroup ↥(elementaryGroup (Fin n) (R S))

/-- **Marked limits and expanders** (section "Finite models", tex l.162–185). -/
def PrintedMarkedLimitExpandersStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ∀ n : ℕ, 3 ≤ n → PrintedMarkedLimitExpanders S n

/-- **A marked limit of finite groups is LEF** (tex l.177–180: "So these finite simple groups
converge to `G` in the space of marked groups, and `G` is LEF."). -/
def PrintedMarkedLimitLEFStatement : Prop :=
  ∀ (ι G : Type) [Group G] (s : ι → G) (H : ℕ → Type) [∀ ℓ, Group (H ℓ)] (σ : ∀ ℓ, ι → H ℓ),
    (∀ ℓ, Finite (H ℓ)) → IsMarkedLimit s σ → IsLEF G

/-! ## Clauses -/

section Clauses

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]

omit [DiscreteTopology A] in
/-- `X` is compact, as a closed subset of `A^ℤ`. -/
theorem compactSpace_carrier (S : Subshift A ℤ) : CompactSpace S.carrier :=
  isCompact_iff_compactSpace.mp S.isClosed.isCompact

/-- **`LC(X, F₂)` is infinite** for an infinite subshift: `X` is compact, Hausdorff and totally
disconnected, hence totally separated, and `infinite_locallyConstant_zmodTwo` applies. -/
theorem infinite_locallyConstant_carrier (S : Subshift A ℤ) (hinf : Infinite S.carrier) :
    Infinite (LocallyConstant S.carrier (ZMod 2)) := by
  haveI := compactSpace_carrier S
  haveI := hinf
  exact infinite_locallyConstant_zmodTwo S.carrier

/-- **`EL_n(R)` is infinite** (tex l.127–128): "It is infinite because `e_{12}(LC(X,F₂))` is
infinite."  The coefficient embedding `LC(X, F₂) → R` is injective, and `e_{12}` is injective on
`R`. -/
theorem infinite_elementaryGroup (S : Subshift A ℤ) (hinf : Infinite S.carrier) {n : ℕ}
    (hn : 3 ≤ n) : Infinite ↥(elementaryGroup (Fin n) (R S)) := by
  haveI := infinite_locallyConstant_carrier S hinf
  haveI : Infinite (R S) :=
    Infinite.of_injective (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2))
      (ClopenCrossedProduct.coeff_injective (subshiftHomeo S) (ZMod 2))
  exact elementaryGroup_infinite (ι := Fin n) (R := R S) ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff])

end Clauses

/-- **`thm:main` from the four pieces.** -/
theorem printedSimpleKazhdanSoficMain_of_pieces (hfg : PrintedSubshiftRingFGStatement)
    (hsimple : PrintedSimplicityStatement) (hmarked : PrintedMarkedLimitExpandersStatement)
    (hlef : PrintedMarkedLimitLEFStatement) : PrintedSimpleKazhdanSoficMain := by
  intro A _ _ _ S hinf hmin n hn
  have hT : HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin n) (R S)) :=
    Pestov91.elementary_hasKazhdanPropertyT (hfg A S) hn
  have hML : PrintedMarkedLimitExpanders S n := hmarked A S hinf hmin n hn
  obtain ⟨ι, s, N, σ, _, hlim, hexp⟩ := hML
  have hLEF : IsLEF ↥(elementaryGroup (Fin n) (R S)) :=
    hlef ι _ s (fun ℓ => Matrix.SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2)) σ hexp.2.1 hlim
  exact ⟨infinite_elementaryGroup S hinf hn,
    KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT _ hT, hsimple A S hinf hmin n hn, hT,
    hmarked A S hinf hmin n hn, hLEF, isSofic_of_isLEF hLEF, Pestov91.isHyperlinear_of_isLEF hLEF⟩

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.infinite_elementaryGroup
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain_of_pieces
