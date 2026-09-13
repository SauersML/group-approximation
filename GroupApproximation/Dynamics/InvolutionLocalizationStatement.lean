import GroupApproximation.Dynamics.TransientIdealExact
import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# `lem:involution-localization`: the printed statement and the pieces it consumes

`non_mf_groups_exist.tex`, tex 1658–1670:

> The matrix rank can be supplied by the dynamics itself.  The following localization makes the
> passage to a return section particularly simple.  Write $K_n(I)$ for the general linear
> restriction kernel, also when $n=1$, and use the same notation for corner ideals with their own
> identity.
>
> **Lemma** (localization by one involution).  Let $C$ be a full clopen section with bounded
> positive return times, put $p_C=1_C$ and $J=p_CIp_C$.  Over any finite field, for every finite
> $F\subset I$ there is $w\in R_X^\times$ with $w-1\in I$, $w^2=1$, and $wFw^{-1}\subset J$.  Over
> $\F_2$, every finite subset of $K_n(I)$ is simultaneously conjugate into the unitized $K_n(J)$ by
> $wI_n$; for $n\ge2$ this involution lies in $\EL_n(R_X)$.

Spelling, in the setting of sec:chain-core (`X` nonempty, compact, metrizable, zero-dimensional;
`T` a homeomorphism; `R_X = ClopenCrossedProduct T k`; `Y = Dynamics.chainRecurrentSet T`):

* `I`: `coreTransientIdeal T k`, the kernel of restriction `R_X → R_Y` (chain-matricial's
  `transientIdeal`; its elements are those whose Laurent coefficients vanish on `Y`,
  `mem_transientIdeal_iff_forall_coeff`);
* `J = p_C I p_C`: the elements `p_C a p_C` with `a ∈ I`;
* "full clopen section with bounded positive return times": `C` is clopen, meets every orbit, and
  each point of `C` returns to `C` after at most `H` positive steps;
* `K_n(I)`: the kernel of `coreRestrictMatrixUnits T k n : GL_n(R_X) → GL_n(R_Y)`, which is
  `ChainCore.DynamicRankBudget.glCoreRestrict` of ct-rank-budget by definition;
* the unitized `K_n(J)`: the images `(1 - p_C) I_n + h` of the corner kernel, i.e. the invertible
  matrices whose deviation `g - 1` has entries in `J` (both deviations of such a `g` are fixed by
  `p_C` on either side and restrict to zero);
* `w I_n`: `Units.map (Matrix.scalar (Fin n)).toMonoidHom w`; `EL_n` is `elementaryGroup`.

The printed lemma is `PrintedInvolutionLocalization`, the conjunction of the finite-field clause
`InvolutionLocalizationRingClause` and the `F₂` clause `InvolutionLocalizationMatrixClause`.

Pieces consumed by the proof, named until their owners land producers:

* `ChainCoreDefectCoverStatement` (lem:chain-core-models, chain-itinerary): `X ∖ Y` is covered by
  translates of the defects `P ∖ T(P)` of compressed clopen sets;
* `CoreKernelElementaryStatement` (the finite matrix argument of thm:core-mf-radical, chain-radical):
  over `F₂` and for `n ≥ 2`, `K_n(I) ⊆ EL_n(R_X)`.
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

section Spelling

variable {X : Type} [MetricSpace X] [CompactSpace X]

/-- The transient ideal `I` of `R_X`: the kernel of restriction to `Y = CR(T)`. -/
noncomputable abbrev coreTransientIdeal (T : X ≃ₜ X) (k : Type) [Ring k] :
    TwoSidedIdeal (ClopenCrossedProduct T k) :=
  transientIdeal T k (Dynamics.image_chainRecurrentSet T)

/-- General linear core restriction `GL_n(R_X) → GL_n(R_Y)`; its kernel is `K_n(I)`. -/
noncomputable abbrev coreRestrictMatrixUnits (T : X ≃ₜ X) (k : Type) [Ring k] (n : ℕ) :
    (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T k))ˣ →*
      (Matrix (Fin n) (Fin n)
        (ClopenCrossedProduct (restrictHomeo T (Dynamics.image_chainRecurrentSet T)) k))ˣ :=
  Units.map (RingHom.mapMatrix (restrict T k (Dynamics.image_chainRecurrentSet T))).toMonoidHom

end Spelling

/-- **lem:involution-localization, finite-field clause** (tex 1664–1667): for a full clopen section
`C` with bounded positive return times and a finite `F ⊆ I`, there is `w ∈ R_X^×` with `w - 1 ∈ I`,
`w² = 1` and `w F w⁻¹ ⊆ J = p_C I p_C`. -/
def InvolutionLocalizationRingClause : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (C : Set X) (hC : IsClopen C),
    (∀ x : X, ∃ j : ℤ, (T ^ j) x ∈ C) →
    (∃ H : ℕ, ∀ x ∈ C, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) →
    ∀ (k : Type) [Field k] [Finite k] (F : Finset (ClopenCrossedProduct T k)),
      (∀ x ∈ F, x ∈ coreTransientIdeal T k) →
      ∃ w : (ClopenCrossedProduct T k)ˣ,
        (w : ClopenCrossedProduct T k) - 1 ∈ coreTransientIdeal T k ∧
        (w : ClopenCrossedProduct T k) * w = 1 ∧
        ∀ x ∈ F, ∃ a ∈ coreTransientIdeal T k,
          (w : ClopenCrossedProduct T k) * x * ↑w⁻¹ =
            coeff T k (LocallyConstant.charFn k hC) * a * coeff T k (LocallyConstant.charFn k hC)

/-- **lem:involution-localization, `F₂` clause** (tex 1667–1669): every finite subset of `K_n(I)` is
simultaneously conjugate into the unitized `K_n(J)` by the scalar involution `w I_n`, with
`w - 1 ∈ I` and `w² = 1`, and `w I_n ∈ EL_n(R_X)` for `n ≥ 2`. -/
def InvolutionLocalizationMatrixClause : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (C : Set X) (hC : IsClopen C),
    (∀ x : X, ∃ j : ℤ, (T ^ j) x ∈ C) →
    (∃ H : ℕ, ∀ x ∈ C, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) →
    ∀ (n : ℕ) (F : Finset (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ),
      (∀ G ∈ F, G ∈ (coreRestrictMatrixUnits T (ZMod 2) n).ker) →
      ∃ w : (ClopenCrossedProduct T (ZMod 2))ˣ,
        (w : ClopenCrossedProduct T (ZMod 2)) - 1 ∈ coreTransientIdeal T (ZMod 2) ∧
        (w : ClopenCrossedProduct T (ZMod 2)) * w = 1 ∧
        (∀ G ∈ F, ∀ i j : Fin n, ∃ a ∈ coreTransientIdeal T (ZMod 2),
          ((Units.map (Matrix.scalar (Fin n)).toMonoidHom w * G *
              (Units.map (Matrix.scalar (Fin n)).toMonoidHom w)⁻¹ :
                (Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
              Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i j -
            (1 : Matrix (Fin n) (Fin n) (ClopenCrossedProduct T (ZMod 2))) i j =
            coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hC) * a *
              coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hC)) ∧
        (2 ≤ n → Units.map (Matrix.scalar (Fin n)).toMonoidHom w ∈
          elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2)))

/-- **lem:involution-localization** (tex 1663–1670), as printed. -/
def PrintedInvolutionLocalization : Prop :=
  InvolutionLocalizationRingClause ∧ InvolutionLocalizationMatrixClause

/-- The defect cover of lem:chain-core-models (tex 1373–1375): "The complement $X\setminus Y$ is
covered by translates of sets $P\setminus T(P)$, where $P$ is clopen and $T(P)\subseteq P$." -/
def ChainCoreDefectCoverStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (x : X), x ∉ Dynamics.chainRecurrentSet ⇑T →
      ∃ (P : Set X) (_ : IsClopen P) (j : ℤ), T '' P ⊆ P ∧ x ∈ ⇑(T ^ j) '' (P \ T '' P)

/-- The finite matrix argument of thm:core-mf-radical, as lem:involution-localization uses it
(tex 1691–1693): over `F₂` and for `n ≥ 2`, `K_n(I) ⊆ EL_n(R_X)`. -/
def CoreKernelElementaryStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (n : ℕ), 2 ≤ n →
      (coreRestrictMatrixUnits T (ZMod 2) n).ker ≤
        elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))

end ClopenCrossedProduct

end GroupApproximation
