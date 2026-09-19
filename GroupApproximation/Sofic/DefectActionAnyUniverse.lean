import GroupApproximation.Sofic.ConjugationDatumAnyUniverse
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant
import GroupApproximation.Sofic.LiteralRouteTransport

/-!
# `cor:generaltransport` with the Kazhdan source in any universe

The printed corollary is

> Let `(r_n)` and `V_{g,n} ∈ U(r_n)` be an operator-norm asymptotic
> representation of `H`, let `Λ` have property (T), let `ι : Λ → H` be a
> homomorphism, and put `L = ι(Λ)`.  Suppose that `(x_n ∈ M_{r_n}(ℂ))` is
> uniformly bounded in operator norm and belongs to the asymptotic commutant in
> normalized Hilbert–Schmidt norm of `L`.  Then every `g ∈ G⁺(L)` acts in both
> directions on that asymptotic commutant.

`KazhdanAsymptoticCommutant.compressionGroup_transport_both` freed the ambient
group and left `Λ` at `Type 0`; that is ledger row `ID.04`.

## Why a second commutant predicate has to exist

The obstacle here is not the proof but the *statement*.
`KazhdanAsymptoticCommutant.IsAsymptoticCommutantOf` is declared under the
section variable `{Γ : Type}` of `Sofic/KazhdanAsymptoticCommutant.lean`, so it
has no universe parameter for the source group at all: the printed corollary
cannot even be written down with it once `Λ` leaves `Type 0`.  Its body,
however, mentions the source only through `ι(λ)`, and `HSSqVanishing` — the
normalized Hilbert–Schmidt convergence the display asks for — is already
universe-polymorphic.

So `IsAsymptoticCommutantOfAny` below is that body with the source binder freed,
and `isAsymptoticCommutantOfAny_type0` certifies, by `Iff.rfl`, that at `Type 0`
it *is* the original predicate.  No object is substituted: the two are the same
definition, one of which can be stated at the manuscript's quantification.

The proof is then the descent of `Sofic.ConjugationDatumAnyUniverse`: property
`(T)` makes `Λ` countable, `Λ` has a `Type 0` model, `L = ι(Λ)` does not move
when `ι` is reindexed along the isomorphism (`range_comp_mulEquiv`), so the
membership `g ∈ G⁺(L)` transports by a rewrite, and the conclusion is read back
along the isomorphism by `isAsymptoticCommutantOfAny_of_precomp`.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix
open scoped Matrix.Norms.L2Operator

universe u v v'

/-- **The asymptotic commutant of `ι(Λ)`, with `Λ` at an arbitrary universe.**
Literally the body of `IsAsymptoticCommutantOf`, whose source binder is pinned
to `Type 0` by a section variable: a matrix sequence asymptotically centralizes
the image of a homomorphism in normalized Hilbert--Schmidt norm. -/
def IsAsymptoticCommutantOfAny {Γ : Type v} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ γ : Γ, HSSqVanishing B (fun n ↦
    x n - (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
      x n * (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)

/-- At `Type 0` the universe-general predicate is the one the transport
machinery is written against, on the nose. -/
theorem isAsymptoticCommutantOfAny_type0 {Γ : Type} [Group Γ] {E : Type u}
    [Group E] (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    IsAsymptoticCommutantOfAny B iota x ↔ IsAsymptoticCommutantOf B iota x :=
  Iff.rfl

/-- Reading a precomposed commutant back along an isomorphism of the source.
Both statements quantify over their own source group, and `e` matches the
quantifiers: the condition at `γ` is the condition at `e γ`, because
`e⁻¹(e γ) = γ`. -/
theorem isAsymptoticCommutantOfAny_of_precomp {Γ₁ : Type v} [Group Γ₁]
    {Γ₂ : Type v'} [Group Γ₂] {E : Type u} [Group E]
    {B : OpAlmostRepresentation E} (iota : Γ₁ →* E) (e : Γ₁ ≃* Γ₂)
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (h : IsAsymptoticCommutantOfAny B (iota.comp e.symm.toMonoidHom) x) :
    IsAsymptoticCommutantOfAny B iota x := by
  intro γ
  have hpull : (iota.comp e.symm.toMonoidHom) (e γ) = iota γ := by
    show iota (e.symm (e γ)) = iota γ
    rw [e.symm_apply_apply]
  rw [← hpull]
  exact h (e γ)

/-- **`cor:generaltransport` with the Kazhdan source at an arbitrary universe**
(ledger row `ID.04`).

Pointwise form of the all-compressors transport theorem: every one-sided
conjugator of `L = ι(Λ)` acts in both directions on the bounded normalized
Hilbert--Schmidt asymptotic commutant of `L`.  Both groups are at arbitrary
universes, and no countability is assumed of either: the property `(T)` the
corollary already prints supplies it for `Λ`.

The `.{v, v}` spelling of property `(T)` is the real form at the source's own
representation universe, which at `v = 0` is the `.{0, 0}` of
`compressionGroup_transport_both`.

Every binder is after the colon, as the badged `Type 0` form does it: the
zero-input gate rejects a badged declaration with header binders. -/
theorem compressionGroup_transport_both_anyUniverse :
    ∀ {Γ : Type v} {E : Type u} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (_hkazhdan : HasKazhdanPropertyT.{v, v} Γ)
    {g : E} (_hg : g ∈ compressionGroup iota.range)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (_hbound : IsUniformlyBounded B x)
    (_hx : IsAsymptoticCommutantOfAny B iota x),
    IsAsymptoticCommutantOfAny B iota (adjointSequence B g x) ∧
      IsAsymptoticCommutantOfAny B iota (coadjointSequence B g x) := by
  intro Γ E _ _ B iota hkazhdan g hg x hbound hx
  haveI : Countable Γ := countable_of_hasKazhdanPropertyT hkazhdan
  obtain ⟨Γ₀, _groupΓ₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hlift : HasKazhdanPropertyT.{v, 0} Γ :=
    HasKazhdanPropertyT.liftUniverse hkazhdan
  have hkazhdan₀ : HasKazhdanPropertyT.{0, 0} Γ₀ :=
    HasKazhdanPropertyT.of_mulEquiv e.symm hlift
  -- `L = ι(Λ)` is unchanged by the reindexing, so `G⁺(L)` is too
  have hrange : (iota.comp e.symm.toMonoidHom).range = iota.range :=
    CompressionUniverseTransfer.range_comp_mulEquiv iota e.symm
  have hg₀ : g ∈ compressionGroup (iota.comp e.symm.toMonoidHom).range := by
    rw [hrange]
    exact hg
  have hx₀ : IsAsymptoticCommutantOf B (iota.comp e.symm.toMonoidHom) x := by
    intro γ₀
    exact hx (e.symm γ₀)
  -- `_literal`, not the finite-stage engine: `cor:generaltransport` prints
  -- "forward transport for a one-sided conjugator `s` is Theorem 3.1", so the
  -- corollary has to traverse the norm-ultraproduct proof of
  -- `\ref{thm:kazhdan-transport}`, which is what
  -- `compressionGroup_transport_both_literal` does.  That is ledger row
  -- `ID.05`; the universe generality below is `ID.04`, and the two are only
  -- closed together if one declaration carries both.
  obtain ⟨h1, h2⟩ := compressionGroup_transport_both_literal B
    (iota.comp e.symm.toMonoidHom) hkazhdan₀ hg₀ x hbound hx₀
  -- at `Type 0` the two commutant predicates are the same definition, so the
  -- retyping below is a defeq check and not a translation
  have h1' : IsAsymptoticCommutantOfAny B (iota.comp e.symm.toMonoidHom)
      (adjointSequence B g x) := h1
  have h2' : IsAsymptoticCommutantOfAny B (iota.comp e.symm.toMonoidHom)
      (coadjointSequence B g x) := h2
  exact ⟨isAsymptoticCommutantOfAny_of_precomp iota e h1',
    isAsymptoticCommutantOfAny_of_precomp iota e h2'⟩

end KazhdanAsymptoticCommutant
end GroupApproximation
