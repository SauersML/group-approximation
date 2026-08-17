import GroupApproximation.Sofic.ConjugationDatumAnyUniverse
import GroupApproximation.Sofic.KazhdanSignCriterion

/-!
# `thm:sign-criterion` with the Kazhdan source in any universe

The printed statement is

> Let `H` and `Γ` be countable groups, let `Γ` have property (T), let
> `ι : Γ → H` be a homomorphism, and suppose `tι(Γ)t⁻¹ ⊆ ι(Γ)`,
> `[c, ι(Γ)] = 1`.  Put `d = tct⁻¹` and `u = [d, ι(a)]` for some `a ∈ Γ`.  If
> `w := u²` is a nontrivial central involution of `H`, then every homomorphism
> `H → U(Q)` maps `w` to the identity, and `H` is not MF.

`KazhdanCompressionCore.ManuscriptCentralSignCriterion` freed the ambient group
and left `Γ` at `Type 0`; that is ledger row `CS.00`.

This module states the criterion with `Γ` at an arbitrary universe.  The printed
hypotheses are kept letter for letter — a homomorphism, a one-sided compressor,
a centralizing root, an element `a`, and the three conditions on `w = u²`
(nontrivial, involutive, central) — and the countability of `Γ` that the print
states is **derived** from its property `(T)` rather than assumed, so no
instance binder for it appears.  `Countable H` remains a hypothesis, as printed.

The spelling `HasKazhdanPropertyTComplex.{v, max v w}` is the textbook property
`(T)` for a group in `Type v`: `hasKazhdanPropertyT_iff_textbook` is exactly the
statement that the real form at the group's own universe is the complex-unitary
form at every representation universe at least as large.  At `v = 0` it is the
`.{0, w}` of the `Type 0` criterion, unchanged.

## Why the statement is not behind a closed-proposition `def`

`Sofic/KazhdanSignCriterion.lean` splits its `Type 0` form in two, a
`def ManuscriptCentralSignCriterion : Prop` and a theorem inhabiting it, and the
obvious way to write this file is to mirror that.  **Do not.**  A theorem whose
type is a bare universe-polymorphic constant has its universe parameters
*auto-bound* as fresh anonymous levels, so the `Γ` obtained by `intro` does not
live in the `v` of this file's `universe` command, and every `.{v, …}` written in
the proof then refers to a different level: the first attempt failed exactly
that way, with `Γ` rejected in `HasKazhdanPropertyT.{v, v} Γ`.  Writing the
binders after the colon, as the four sibling `AnyUniverse` modules do, binds
`u`, `v` and `w` by name in the statement itself and is what makes the universe
annotations inside the proof mean what they say.  The zero-input gate is
satisfied either way — what it requires is an empty declaration telescope, which
this has.
-/

namespace GroupApproximation
namespace KazhdanCompressionCore

open scoped commutatorElement

universe u v w

/-- **`thm:sign-criterion` with the Kazhdan source at an arbitrary universe**
(ledger row `CS.00`).

If the square of one compression defect is a nontrivial central involution, then
every homomorphism into every positive natural-dimensional genuine norm-matrix
C-star corona kills it, and the ambient countable group is not MF in the literal
CDE sense.  All groups, structure, and hypotheses are quantified inside the
sentence, leaving the declaration telescope empty; both groups range over every
universe, as the manuscript's "countable groups" do.

The proof descends the source to its `Type 0` model, which exists because
property `(T)` makes `Γ` countable, and which still has property `(T)` because
the isomorphism carries it.  The data is precomposed with the isomorphism and
the printed element `a` is read at `e a`; the conclusion mentions only `E`, `z`
and the corona, so nothing has to be translated back. -/
theorem manuscriptCentralSignCriterion_anyUniverse :
    ∀ {Γ : Type v} {E : Type u} [Group Γ] [Group E] [Countable E]
      (hT : HasKazhdanPropertyTComplex.{v, max v w} Γ)
      (iota : Γ →* E) (t c : E)
      (hcompresses : ∀ γ : Γ, ∃ δ : Γ,
        t * iota γ * t⁻¹ = iota δ)
      (hcomm : ∀ γ : Γ, Commute c (iota γ))
      (a : Γ) (z : E)
      (hz : z = ⁅t * c * t⁻¹, iota a⁆ ^ 2)
      (hz_ne : z ≠ 1) (hz_sq : z ^ 2 = 1)
      (hz_central : ∀ g : E, Commute z g),
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : E →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho z = 1) ∧
      ¬ IsCDEOperatorMF E := by
  intro Γ E _ _ _ hT iota t c hcompresses hcomm a z hz hz_ne hz_sq hz_central
  -- the printed countability of `Γ` is not assumed: property `(T)` gives it
  have hreal : HasKazhdanPropertyT.{v, v} Γ :=
    hasKazhdanPropertyT_iff_textbook.mpr hT
  haveI : Countable Γ := countable_of_hasKazhdanPropertyT hreal
  obtain ⟨Γ₀, _groupΓ₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  -- property `(T)` moves to the model in two steps: lower the representation
  -- universe to `0` so the model can see it, then carry it across
  have hlift : HasKazhdanPropertyT.{v, 0} Γ :=
    HasKazhdanPropertyT.liftUniverse hreal
  have hreal₀ : HasKazhdanPropertyT.{0, 0} Γ₀ :=
    HasKazhdanPropertyT.of_mulEquiv e.symm hlift
  have hT₀ : HasKazhdanPropertyTComplex.{0, w} Γ₀ :=
    hasKazhdanPropertyT_iff_textbook.mp hreal₀
  have hpull : ∀ γ₀ : Γ₀, (iota.comp e.symm.toMonoidHom) γ₀ = iota (e.symm γ₀) :=
    fun _ ↦ rfl
  have hcompresses₀ : ∀ γ₀ : Γ₀, ∃ δ₀ : Γ₀,
      t * (iota.comp e.symm.toMonoidHom) γ₀ * t⁻¹
        = (iota.comp e.symm.toMonoidHom) δ₀ := by
    intro γ₀
    obtain ⟨δ, hδ⟩ := hcompresses (e.symm γ₀)
    refine ⟨e δ, ?_⟩
    rw [hpull, hpull, e.symm_apply_apply]
    exact hδ
  have hcomm₀ : ∀ γ₀ : Γ₀, Commute c ((iota.comp e.symm.toMonoidHom) γ₀) :=
    fun γ₀ ↦ hcomm (e.symm γ₀)
  have hz₀ : z = ⁅t * c * t⁻¹,
      (iota.comp e.symm.toMonoidHom) (e a)⁆ ^ 2 := by
    rw [hpull, e.symm_apply_apply]
    exact hz
  exact manuscriptCentralSignCriterion (Γ := Γ₀) (E := E) hT₀
    (iota.comp e.symm.toMonoidHom) t c hcompresses₀ hcomm₀ (e a) z hz₀
    hz_ne hz_sq hz_central

end KazhdanCompressionCore
end GroupApproximation
