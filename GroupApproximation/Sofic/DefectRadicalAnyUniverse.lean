import GroupApproximation.Sofic.ConjugationDatumAnyUniverse
import GroupApproximation.Sofic.ManuscriptKazhdanTransport

/-!
# `thm:compression-radical` with the Kazhdan source in any universe

The printed statement is

> Let `H` and `Γ` be countable groups, let `Γ` have property (T), let
> `ι : Γ → H` be a homomorphism, and put `L = ι(Γ)`.  If `F ⊴ H` is finite and
> `F ≤ 𝔇(H,L)`, then every homomorphism `H → U(Q)` maps every element of `F`
> to the identity.

`KazhdanAsymptoticCommutant.manuscriptCompressionRadical` freed the ambient
group and left `Γ` at `Type 0` — its own docstring says so: "The Kazhdan source
`Γ` is still fixed at `Type 0` by the spelling `HasKazhdanPropertyTComplex.{0,
w}`; the printed statement asks for it to be countable too, so that restriction
remains."  That reasoning is what the transport wrappers of 2026-08-17 overturn:
`Type 0` is not countability, and countability is not needed as a hypothesis
because property `(T)` already implies it.  This is ledger row `ID.09`.

The wrapper below states the theorem with `Γ` at an arbitrary universe.  The
countability of `Γ` that the print states is derived from its property `(T)`, so
the statement carries no binder for it; `Countable H` remains, as printed.  `L`
does not move when `ι` is reindexed onto the `Type 0` model of `Γ`
(`CompressionUniverseTransfer.range_comp_mulEquiv`), so `𝔇(H,L)` is the same
subgroup there and both the hypothesis and the conclusion are read verbatim.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

universe u v w

/-- **`thm:compression-radical` with the Kazhdan source at an arbitrary
universe** (ledger row `ID.09`).

For a countable ambient group, every finite normal subgroup of the intrinsic
compression--centralizer defect of a Kazhdan image lies in the literal
natural-dimension C-star-corona radical.  The second conjunct spells out the
equivalent kernel statement for every printed norm-matrix corona.

The spelling `HasKazhdanPropertyTComplex.{v, max v w}` is the textbook property
`(T)` for a group in `Type v`, by `hasKazhdanPropertyT_iff_textbook`; at `v = 0`
it is the `.{0, w}` of `manuscriptCompressionRadical`, unchanged.

Every binder is after the colon, as the badged `Type 0` form does it: the
zero-input gate rejects a badged declaration with header binders. -/
theorem manuscriptCompressionRadical_anyUniverse :
    ∀ {Γ : Type v} {H : Type u} [Group Γ] [Group H] [Countable H]
    (_hT : HasKazhdanPropertyTComplex.{v, max v w} Γ)
    (iota : Γ →* H)
    (F : Subgroup H) [Finite F] [F.Normal]
    (_hF : F ≤ compressionCentralizerDefect iota.range),
    F ≤ manuscriptCoronaMFResidual H ∧
      ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : H →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          F ≤ rho.ker := by
  intro Γ H _ _ _ hT iota F _ _ hF
  -- the printed countability of `Γ` is not assumed: property `(T)` gives it
  have hreal : HasKazhdanPropertyT.{v, v} Γ :=
    hasKazhdanPropertyT_iff_textbook.mpr hT
  haveI : Countable Γ := countable_of_hasKazhdanPropertyT hreal
  obtain ⟨Γ₀, _groupΓ₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hlift : HasKazhdanPropertyT.{v, 0} Γ :=
    HasKazhdanPropertyT.liftUniverse hreal
  have hreal₀ : HasKazhdanPropertyT.{0, 0} Γ₀ :=
    HasKazhdanPropertyT.of_mulEquiv e.symm hlift
  have hT₀ : HasKazhdanPropertyTComplex.{0, w} Γ₀ :=
    hasKazhdanPropertyT_iff_textbook.mp hreal₀
  -- `L = ι(Γ)` is unchanged by the reindexing, so `𝔇(H, L)` is too
  have hrange : (iota.comp e.symm.toMonoidHom).range = iota.range :=
    CompressionUniverseTransfer.range_comp_mulEquiv iota e.symm
  have hF₀ : F ≤
      compressionCentralizerDefect (iota.comp e.symm.toMonoidHom).range := by
    rw [hrange]
    exact hF
  exact manuscriptCompressionRadical hT₀ (iota.comp e.symm.toMonoidHom) F hF₀

end KazhdanAsymptoticCommutant
end GroupApproximation
