import GroupApproximation.Sofic.ConjugationDatumAnyUniverse
import GroupApproximation.Sofic.ManuscriptExactWrappers

/-!
# `thm:criterion` with the Kazhdan source in any universe

The printed statement is

> Let `H` be a countable group with a Kazhdan conjugation datum `(Λ, ι, t, c)`,
> and let `F ⊴ H` be a finite normal subgroup with `F ⊆ N_conj`.  Then every
> homomorphism `Θ : H → U(Q)` satisfies `Θ(f) = 1` for all `f ∈ F`.

with no universe named for `Λ`.  `ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion`
freed the ambient group and left the source at `Type 0`; that is ledger row
`FN.00`, and row `PA.14` cites the same declaration for the sentence of
`p:A-consequences`,

> Here `{1,w}` can be replaced by any finite normal subgroup of the normal
> closure of the commutators `[tct⁻¹, ι(γ)]` (Theorem~\ref{thm:criterion}) …

so both rows are about this one statement and both are closed by the wrapper
below.

The descent is the one of `Sofic.ConjugationDatumAnyUniverse`: the datum's
`kazhdan` field makes `Λ` countable, a countable group has a `Type 0` model,
`CompressionUniverseTransfer.mapCoreSource` carries the datum there, and
`mapCoreSource_defectNormal` says `N_conj` is *literally the same subgroup*
afterwards, so the finite normal subgroup and its containment hypothesis need no
translation at all.  Nothing analytic is redone, and the countability of `Λ`
that the print grants is derived rather than assumed — the wrapper carries one
hypothesis fewer than the `Type 0` form it replaces.
-/

namespace GroupApproximation
namespace ManuscriptExactWrappers

universe u v

/-- **`thm:criterion` with the Kazhdan source at an arbitrary universe**
(ledger rows `FN.00` and `PA.14`).

Exact natural-dimension form of the finite-normal obstruction criterion: every
homomorphism into the unitary group of the genuine norm-matrix C-star corona
maps the specified finite normal subgroup to the identity.

This is `manuscriptFiniteNormalObstructionCriterion` with `Γ` unpinned and with
its `Countable Γ` instance binder removed: the datum's property `(T)` supplies
it (`KazhdanCompressionCore.countable_source`), so no hypothesis the print does
not state is assumed and one the print does state is now derived.  `Countable H`
remains, as printed.

Every binder is after the colon, as the badged `Type 0` form does it: the
zero-input gate rejects a badged declaration with header binders. -/
theorem manuscriptFiniteNormalObstructionCriterion_anyUniverse :
    ∀ {Gamma : Type v} {H : Type u} [Group Gamma] [Group H]
      [Countable H]
      (C : KazhdanCompressionCore Gamma H)
      (F : Subgroup H) [Finite F] [F.Normal]
      (hF : F ≤ C.defectNormal)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ Theta.ker := by
  intro Gamma H _ _ _ C F _ _ hF d hd
  -- the source is countable because the datum says it has property `(T)`
  haveI : Countable Gamma := C.countable_source
  obtain ⟨Gamma₀, _groupGamma₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Gamma
  haveI : Countable Gamma₀ := Type0Transfer.countable_type0_model Gamma e
  -- `mapCoreSource` fixes `t` and `c` and reindexes `ι` along a bijection, so
  -- `N_conj` is unchanged and the containment hypothesis transports verbatim
  have hF₀ : F ≤ (CompressionUniverseTransfer.mapCoreSource C e).defectNormal := by
    rw [CompressionUniverseTransfer.mapCoreSource_defectNormal]
    exact hF
  exact manuscriptFiniteNormalObstructionCriterion
    (CompressionUniverseTransfer.mapCoreSource C e) F hF₀ d hd

end ManuscriptExactWrappers
end GroupApproximation
