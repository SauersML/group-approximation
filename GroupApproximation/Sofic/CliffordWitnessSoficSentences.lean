import GroupApproximation.Sofic.CliffordWitnessSoficPrinted
import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Printed proof sentences of `prop:clifford-locally-rf` and Theorem `thm:amenable-trace`

`non_mf_groups_exist.tex`'s printed proof of `prop:clifford-locally-rf`, and the one-sentence
proof of `thm:amenable-trace` that follows it, both have statement-level carriers
(`Sofic/CliffordWitnessSoficPrinted.lean`, `Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean`,
`Manuscript/OneSidedMFRadical/AmenableTraceTheorem.lean`) but no per-sentence carriers.  Following
the pattern of `Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean`, this module gives one
`manuscriptSentence_<slug>` lemma per printed sentence that asserts a checkable fact, each proved
from already-landed declarations --- no new mathematics.  A few printed sentences are pure
notation-setting (naming `Γ_n`, `Y`, `C_Y`) with no independent mathematical content beyond the
object they name; those are not given their own lemma, matching `NormalKazhdanPrintedRoute`'s own
treatment of its one purely-naming sentence.

The printed proof (`non_mf_groups_exist.tex`, current text) is a concrete combinatorial argument:
it names the commensurated subgroups `Γ_n`, builds a finite `Γ_n`-invariant lamp subgroup `C_Y`,
and shows `C_Y ⋊ Γ_n` residually finite via the kernel of the action on `C_Y`.  The repository's
landed proof of the *statement* goes through more abstract soficity/residual-finiteness permanence
theorems, but every one of the printed sentences' individual claims has its own direct carrier in
the repository:  the commensuration and finite-orbit geometry live in
`Sofic/MappingTelescopeFiniteOrbits.lean`, the finite invariant subgroup construction is
`CliffordLamp.exists_finite_invariant_clifford_subgroup`
(`Sofic/FiniteOrbitInvariantKernel.lean`), and the kernel-of-the-action residual-finiteness step is
`residuallyFinite_semidirectProduct_of_finite_range` (`Sofic/LEFSofic.lean`) --- the same general
lemma `CliffordWitnessLocallyRFByInt.isLocallyResiduallyFinite_semidirectProduct_of_invariant_finite`
already applies internally to close the landed statement-level theorem.
-/

namespace GroupApproximation
namespace AmenableTraceTheorem

open MarkedCompression MappingTelescope MappingTelescopeFiniteOrbits CliffordLamp
open CliffordWitnessLocallyRFByInt LocallyRFByIntAmenableTrace
open LiteralNonMFLinearWitness

noncomputable section

/-! ## `prop:clifford-locally-rf`, printed proof -/

/-- **Printed sentence.**

> Reassociating the semidirect products yields `W ≅ K ⋊ ℤ`, `K = Cl(X) ⋊ T_α`.

Projected from the closed statement-level theorem: this is its first conjunct. -/
theorem manuscriptSentence_reassociation {Γ : Type} [Group Γ] [Countable Γ]
    [Group.ResiduallyFinite Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    [α.range.FiniteIndex] {a : Γ} (ha : a ∉ Set.range α)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    Nonempty (Ambient α hα ≃*
      (ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ)) := by
  obtain ⟨hEquiv, -, -, -, -, -, -⟩ := manuscriptCliffordLocallyRF Γ α hα a ha hT
  exact hEquiv

/-- **Printed sentence** (definitional, no independent content beyond the object it names).

> For `n ≥ 0`, write `Γ_n = t^{-n} Γ t^n` for the image of the `n`th copy of `Γ` in `T_α`.

The Lean object is `(MappingTelescope.level α hα n).range : Subgroup (Telescope α hα)`. -/
example {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α) (n : ℕ) :
    Subgroup (Telescope α hα) :=
  (level α hα n).range

/-- **Printed sentence.**

> Since `[Γ:α(Γ)] < ∞`, each `Γ_n` has finite index in `Γ_{n+1}`; every element of `T_α` lies in
> some `Γ_m`, and conjugation by `t` maps `Γ_{m+1}` onto `Γ_m`, so `Γ` is commensurated by `V`.

The three clauses are `MappingTelescopeFiniteOrbits.level_relIndex_ne_zero`,
`exists_level_repr`, and `MappingTelescopeFiniteOrbits.vertical_le_commensurator` (the last of
these is literally the conclusion "`Γ` is commensurated by `V`", stated for the level-zero copy
against the whole vertical group). -/
theorem manuscriptSentence_commensuration {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex] (n : ℕ) :
    (level α hα n).range.relIndex (level α hα (n + 1)).range ≠ 0 ∧
      (∀ g : Telescope α hα, ∃ (m : ℕ) (x : Γ), level α hα m x = g) ∧
      (⊤ : Subgroup (Vertical α hα)) ≤
        Subgroup.Commensurable.commensurator (baseSubgroup α hα) :=
  ⟨level_relIndex_ne_zero α hα (Nat.le_succ n), exists_level_repr α hα,
    vertical_le_commensurator α hα⟩

/-- **Printed sentence.**

> Hence the stabilizer in `Γ_n` of every point of `X = V/Γ` has finite index, and every `Γ_n`-orbit
> in `X` is finite.

Orbit finiteness is `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit`; finite index of the
stabilizer follows from it by the orbit-stabilizer equivalence
(`MulAction.orbitEquivQuotientStabilizer`) and `Subgroup.finiteIndex_of_finite_quotient`. -/
theorem manuscriptSentence_stabilizerAndOrbitFinite {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex] (n : ℕ)
    (x : Cosets α hα) :
    (MulAction.stabilizer (verticalLevel α hα n) x).FiniteIndex ∧
      (MulAction.orbit (verticalLevel α hα n) x).Finite := by
  have horb : (MulAction.orbit (verticalLevel α hα n) x).Finite :=
    finite_verticalLevel_orbit α hα n x
  refine ⟨?_, horb⟩
  haveI : Finite ↥(MulAction.orbit (verticalLevel α hα n) x) := Set.finite_coe_iff.mpr horb
  haveI : Finite (verticalLevel α hα n ⧸ MulAction.stabilizer (verticalLevel α hα n) x) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer (verticalLevel α hα n) x)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **Printed sentence.**

> A finite subset of `K` involves only finitely many lamps `c_x`, and its `T_α`-coordinates lie in
> one `Γ_n`.

This is the finite-window setup already used inline in the landed proof of
`CliffordWitnessLocallyRFByInt.shiftKernelFor_isLocallyResiduallyFinite`: take `N` to be the
supremum, over the finite set, of the level of each element's `T_α`-coordinate. -/
theorem manuscriptSentence_finiteSubsetOneLevel {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α)
    (F : Finset (ShiftKernelFor α hα)) :
    ∃ N : ℕ, ∀ g ∈ F, g.right ∈ (level α hα N).range := by
  classical
  choose lvl elt hrepr using fun g : ShiftKernelFor α hα ↦
    exists_level_repr α hα g.right
  refine ⟨F.sup lvl, fun g hg ↦ ?_⟩
  have hle : lvl g ≤ F.sup lvl := Finset.le_sup (f := lvl) hg
  have hmem := level_mem_range_of_le α hα hle (elt g)
  rwa [hrepr g] at hmem

/-- **Printed sentences** (three sentences, one existence claim).

> Let `Y` be the union of the `Γ_n`-orbits of these finitely many `x`.  Then `Y` is finite and
> `Γ_n`-invariant, and the finite subset is contained in `C_Y ⋊ Γ_n`, where
> `C_Y = ⟨ε, c_y : y ∈ Y⟩` is finite by the normal form above.

`Y` and `C_Y` are not named separately in the landed development; the existence of a finite,
`H`-invariant subgroup of the Clifford lamp group containing a prescribed finite subset ---
exactly the printed content, with `C_Y` as the produced subgroup `K` --- is
`CliffordLamp.exists_finite_invariant_clifford_subgroup`, general in the acting subgroup `H` and
its permutation representation `ρ` on the site set `X`. -/
theorem manuscriptSentence_finiteInvariantSubgroup {X : Type} {H : Type} [Group H]
    (rho : H →* Equiv.Perm X) (hsite : ∀ x : X, (Set.range fun h : H ↦ rho h x).Finite)
    (F : Finset (CliffordLamp X)) :
    ∃ K : Subgroup (CliffordLamp X), Finite K ∧
      (∀ h : H, ∀ n ∈ K, CliffordLamp.actionHom rho h n ∈ K) ∧ ∀ n ∈ F, n ∈ K :=
  CliffordLamp.exists_finite_invariant_clifford_subgroup rho hsite F

/-- **Printed sentences** (four sentences, one residual-finiteness fact).

> This semidirect product is residually finite.  Indeed, an element with nontrivial
> `Γ_n`-component survives in a finite quotient of `Γ_n`.  For a nontrivial element of `C_Y`, let
> `J` be the kernel of the action `Γ_n → Aut(C_Y)`.  The quotient `Γ_n/J` is finite, and the
> element has nontrivial image in the finite group `C_Y ⋊ (Γ_n/J)`.

`J` is the kernel `φ.ker` of the acting homomorphism `φ : Γ_n → MulAut(C_Y)`; the quotient
`Γ_n/J ≅ φ.range` is finite because `C_Y` is finite (so `MulAut C_Y` is finite); and this is
exactly the general lemma `residuallyFinite_semidirectProduct_of_finite_range`, whose own proof
carries out the "element with nontrivial component survives" argument via the two projections
onto `M` and `φ.ker`. -/
theorem manuscriptSentence_semidirectResiduallyFinite
    {M Γ : Type*} [Group M] [Group Γ] (φ : Γ →* MulAut M)
    [Group.ResiduallyFinite M] [Group.ResiduallyFinite Γ] [Finite φ.range] :
    Group.ResiduallyFinite (M ⋊[φ] Γ) :=
  residuallyFinite_semidirectProduct_of_finite_range φ

/-- **Printed sentence** (already `formalized`, restated here for the sentence table).

> Therefore every finitely generated subgroup of `K` is residually finite.

This is exactly `IsLocallyResiduallyFinite (ShiftKernelFor α hα)`, whose definition
(`∀ H : Subgroup K, H.FG → Group.ResiduallyFinite H`) is this sentence verbatim; projected from
the closed statement-level theorem. -/
theorem manuscriptSentence_locallyResiduallyFinite {Γ : Type} [Group Γ] [Countable Γ]
    [Group.ResiduallyFinite Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    [α.range.FiniteIndex] {a : Γ} (ha : a ∉ Set.range α)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    IsLocallyResiduallyFinite (ShiftKernelFor α hα) := by
  obtain ⟨-, hKlocRF, -, -, -, -, -⟩ := manuscriptCliffordLocallyRF Γ α hα a ha hT
  exact hKlocRF

/-- **Printed sentence.**

> Each finitely generated subgroup of `K` is residually finite and hence sofic.

The generic residually-finite-implies-sofic route, applied pointwise to every finitely generated
subgroup (as a group in its own right). -/
theorem manuscriptSentence_fgSubgroupSofic {H : Type} [Group H] [Group.ResiduallyFinite H] :
    IsSofic H :=
  isSofic_of_isLEF isLEF_of_residuallyFinite

/-- **Printed sentence** (the amenability clause; "`K` is their directed union" is the structural
observation that any group is the directed union of its finitely generated subgroups, with no
further content to formalize).

> The group `K` is their directed union, and `W/K ≅ ℤ` is amenable.

`ℤ` amenable is `SoficByAmenablePermanence.isAmenable_int`, the repository's own Følner/invariant-
mean route (`Algebra/AmenableInt.lean`), not a literature input. -/
theorem manuscriptSentence_quotientAmenable :
    Amenability.IsAmenable (Multiplicative ℤ) :=
  SoficByAmenablePermanence.isAmenable_int

/-- **Printed sentence.**

> Soficity passes to directed unions and to extensions with amenable quotient
> [Elek--Szabó, Theorem 1], so `W` is sofic.

The mechanism: local residual finiteness gives soficity of `K` (`isSofic_of_locallyResiduallyFinite`,
the directed-union/LEF route), and soficity passes across a split extension by the (amenable) `ℤ`
factor (`SoficByAmenablePermanence.isSofic_int_semidirectProduct`, Elek--Szabó's Theorem 1 in the
form the repository proves it). -/
theorem manuscriptSentence_wSoficMechanism {K : Type} [Group K]
    (φ : Multiplicative ℤ →* MulAut K) (hK : IsLocallyResiduallyFinite K) :
    IsSofic (K ⋊[φ] Multiplicative ℤ) :=
  SoficByAmenablePermanence.isSofic_int_semidirectProduct φ
    (isSofic_of_locallyResiduallyFinite hK)

/-- **Printed sentence.**

> Proposition `prop:clifford-self-embedding` shows that it is not MF.

The cited proposition's own carrier. -/
theorem manuscriptSentence_notMF {Γ : Type} [Group Γ] [Countable Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) {a : Γ} (ha : a ∉ Set.range α)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    ¬ IsOperatorMF (Ambient α hα) :=
  CliffordWitnessDirectDefect.not_isOperatorMF α hα ha hT

/-- **Printed sentence.**

> By Proposition `prop:locally-rf-by-z-trace`, applied to the extension `1 → K → W → ℤ → 1`, the
> canonical trace of `C*_max(K)` is quasidiagonal and that of `C*_max(W)` is amenable; by Theorem
> `thm:factorization-nonmf-trace` the latter is not quasidiagonal.

Projected from the closed statement-level theorem: these are its last three conjuncts, produced
there from exactly the three cited ingredients (`ring-b-alg`'s
`AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal` for the first
half of `prop:locally-rf-by-z-trace`, `LocallyRFByIntFactorization`'s `ℤ`-specific carrier for the
second half, and `NinetyNineProblems.canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF`
for `thm:factorization-nonmf-trace`). -/
theorem manuscriptSentence_traceConclusions {Γ : Type} [Group Γ] [Countable Γ]
    [Group.ResiduallyFinite Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    [α.range.FiniteIndex] {a : Γ} (ha : a ∉ Set.range α)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar (ShiftKernelFor α hα) ↦
          canonicalMaximalTrace (ShiftKernelFor α hα) x) ∧
      Quasidiagonal.IsAmenableTrace
        (fun x : MaximalGroupCStar (Ambient α hα) ↦
          canonicalMaximalTrace (Ambient α hα) x) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar (Ambient α hα) ↦
          canonicalMaximalTrace (Ambient α hα) x) := by
  obtain ⟨-, -, -, -, hKQD, hAmen, hNotQD⟩ := manuscriptCliffordLocallyRF Γ α hα a ha hT
  exact ⟨hKQD, hAmen, hNotQD⟩

/-! ## Theorem `thm:amenable-trace`, printed proof -/

/-- **Printed sentence** (the theorem's entire proof).

> Apply Proposition `prop:clifford-locally-rf` to `Γ̄`, `α`, and `a`.

`Γ̄`, `α`, `a` are `gammaBar`, `alpha`, `v1G`; the application and its conclusions are
`AmenableTraceTheorem.manuscriptAffineCliffordConclusions`
(`Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean`). -/
theorem manuscriptSentence_theorem4Application :
    Nonempty (WitnessGroup ≃* (ShiftKernel ⋊[shiftAction] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite ShiftKernel ∧
      IsSofic WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar ShiftKernel ↦
          canonicalMaximalTrace ShiftKernel x) ∧
      Quasidiagonal.IsAmenableTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x) :=
  manuscriptAffineCliffordConclusions

end

end AmenableTraceTheorem
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceTheorem

#audit_closed_axioms manuscriptSentence_theorem4Application
