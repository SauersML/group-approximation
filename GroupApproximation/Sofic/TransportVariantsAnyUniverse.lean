import GroupApproximation.Sofic.CompressionUniverseTransfer
import GroupApproximation.Sofic.IntertwinerKazhdanTransport
import GroupApproximation.Sofic.KazhdanTransportAnyUniverse

/-!
# `thm:transport-variants` for groups in any universe

`thm:transport-variants` opens

> Let `Γ`, `H`, `ι`, and `s` be as in Theorem `thm:kazhdan-transport`

and `thm:kazhdan-transport` says only "let `Γ` and `H` be groups".  So the
printed statement grants **no countability and no universe restriction** on
either group, while the three formalized variants fix the Kazhdan source at
`Type 0`.  The proof ledger recorded that as `univ0`, correctly: a `Type 0`
statement is strictly narrower than the printed one.

This file closes it the way `Sofic.KazhdanTransportAnyUniverse` closed
`thm:kazhdan-transport`, and for the same reason: **property `(T)` implies
countability**, because it supplies a finite generating set.  So a Kazhdan
source in any universe has a `Type 0` model, the compression datum travels to
that model, and the `Type 0` theorem applies there.  No hypothesis the print
does not state is added; the countability is derived, not assumed.

## Why this is a wrapper and not a sweep

Generalizing the transport proofs themselves was measured twice and both
attempts were reverted.  The wall is not the group universe but the
representation universe: `KazhdanCompressorCorner.cornerProjection` and its
neighbours pin `IsKazhdanPair.{0, 0}`, so widening the source binder cascades
into the corner layer.  It does not need to be widened.  The three ingredients
of the descent are all in the tree already:

* `KazhdanCompressionCore.countable_source` — the datum's own `kazhdan` field
  forces its source to be countable;
* `Type0Transfer.exists_type0_model` — a countable group is isomorphic to one
  whose carrier is a `Type`;
* `CompressionUniverseTransfer.mapCoreSource` — the datum transports along an
  isomorphism of its source, property `(T)` included.

What this file adds is the two "undo the precomposition" lemmas the transport
back needs, and the three wrappers.  The datum handed to the `Type 0` theorem is
`mapCoreSource C e`, whose `iota` is `C.iota ∘ e.symm`; the conclusion therefore
speaks about `C.iota (e.symm γ₀)` and has to be read back as a statement about
`C.iota γ`.  Since `e` is a bijection, `γ₀ := e γ` does that, and the two lemmas
below are that single step for the two commutant predicates.  `mapCoreSource`
leaves `t` alone, so the compressed sequences are literally the same terms.
-/

namespace GroupApproximation

open Matrix IntertwinerKazhdanTransport ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

universe u v v'

namespace TransportVariantsAnyUniverse

/-! ## Reading a precomposed commutant back along the isomorphism

The `Type 0` theorem is applied to a datum whose homomorphism is `ι ∘ e⁻¹`.  Its
conclusion quantifies over the model group; the printed conclusion quantifies
over the original.  These two lemmas are the translation, and they are the only
place the isomorphism is used after the datum has been transported. -/

/-- A scaled asymptotic commutant for `ι ∘ e⁻¹` is one for `ι`.  Both statements
quantify over their own source group, and `e` matches the quantifiers: the
condition at `γ` is the condition at `e γ`, because `e⁻¹(e γ) = γ`. -/
theorem commutantOf_of_precomp {Γ₁ : Type v} {Γ₂ : Type v'} [Group Γ₁]
    [Group Γ₂] {E : Type u} [Group E] {B : OpAlmostRepresentation E} {w : ℕ → ℝ}
    (iota : Γ₁ →* E) (e : Γ₁ ≃* Γ₂)
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (h : IsScaledAsymptoticCommutantOf B w (iota.comp e.symm.toMonoidHom) x) :
    IsScaledAsymptoticCommutantOf B w iota x := by
  intro γ
  have hpull : (iota.comp e.symm.toMonoidHom) (e γ) = iota γ := by
    show iota (e.symm (e γ)) = iota γ
    rw [e.symm_apply_apply]
  rw [← hpull]
  exact h (e γ)

/-- The rectangular counterpart: a scaled asymptotic intertwiner for `ι ∘ e⁻¹`
is one for `ι`. -/
theorem intertwinerOf_of_precomp {Γ₁ : Type v} {Γ₂ : Type v'} [Group Γ₁]
    [Group Γ₂] {E : Type u} [Group E]
    {B₁ B₂ : OpAlmostRepresentation E} {w : ℕ → ℝ}
    (iota : Γ₁ →* E) (e : Γ₁ ≃* Γ₂)
    {x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ}
    (h : IsScaledAsymptoticIntertwinerOf B₁ B₂ w
      (iota.comp e.symm.toMonoidHom) x) :
    IsScaledAsymptoticIntertwinerOf B₁ B₂ w iota x := by
  intro γ
  have hpull : (iota.comp e.symm.toMonoidHom) (e γ) = iota γ := by
    show iota (e.symm (e γ)) = iota γ
    rw [e.symm_apply_apply]
  rw [← hpull]
  exact h (e γ)

/-! ## The three variants at any universe -/

/-- **`thm:transport-variants`(1) with the Kazhdan source at an arbitrary
universe.**  Transport of the `w`-scaled asymptotic commutant through the
compressor, in both directions, at every nonnegative weight — with no
countability and no universe hypothesis on the source, as printed.

`ScaledKazhdanTransport.scaled_transport_both` is this statement with the source
at `Type 0`.  The datum is carried to the `Type 0` model by `mapCoreSource`,
which fixes `t`, so the two compressed sequences in the conclusion are the same
terms there as here and only the homomorphism has to be read back.

Every binder is after the colon, as the badged `Type 0` form does it: the
zero-input gate rejects a badged declaration with header binders. -/
theorem scaled_transport_both_anyUniverse :
    ∀ {Γ : Type v} {E : Type u} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n)
      (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
      (_hx : IsScaledAsymptoticCommutant B w C x)
      (_hbound : IsScaledMassBounded B w x),
      IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
        IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  intro Γ E _ _ B w hw C x hx hbound
  haveI : Countable Γ := C.countable_source
  obtain ⟨Γ₀, _, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hx₀ : IsScaledAsymptoticCommutant B w
      (CompressionUniverseTransfer.mapCoreSource C e) x := by
    intro γ₀
    exact hx (e.symm γ₀)
  obtain ⟨h1, h2⟩ := scaled_transport_both B w hw
    (CompressionUniverseTransfer.mapCoreSource C e) x hx₀ hbound
  exact ⟨commutantOf_of_precomp C.iota e h1, commutantOf_of_precomp C.iota e h2⟩

/-- **The intertwiner transport variant with the Kazhdan source at an arbitrary
universe** (printed as `thm:transport-variants`(2) until the clause was cut on
2026-08-18).  Intertwiner transport at the `d¹ₙ + d²ₙ` normalization, with no
countability and no universe hypothesis on either group.

This is `IntertwinerKazhdanTransport.manuscriptIntertwinerTransport` composed
with the same descent `Sofic.KazhdanTransportAnyUniverse` performs for
`thm:kazhdan-transport`: property `(T)` gives countability, countability gives
the `Type 0` model, and the model still has property `(T)` because the
isomorphism carries it.  The two almost representations and the sequence are
untouched — they live over the ambient group, which was already polymorphic. -/
theorem manuscriptIntertwinerTransport_anyUniverse :
    ∀ {Γ : Type v} {H : Type u} [Group Γ] [Group H]
      (_hT : HasKazhdanPropertyTComplex.{v, max v v'} Γ)
      (iota : Γ →* H) (s : H)
      (_hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
      (d₁ d₂ : ℕ → ℕ) (_hd₁ : ∀ n, 0 < d₁ n) (_hd₂ : ∀ n, 0 < d₂ n)
      (U₁ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₁ n)) ℂ)
      (U₂ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₂ n)) ℂ)
      (_hU₁ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(U₁ n (g * h) : Matrix (naturalFiniteModel (d₁ n))
            (naturalFiniteModel (d₁ n)) ℂ) -
          (U₁ n g : Matrix (naturalFiniteModel (d₁ n))
            (naturalFiniteModel (d₁ n)) ℂ) * U₁ n h‖ ≤ ε)
      (_hU₂ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(U₂ n (g * h) : Matrix (naturalFiniteModel (d₂ n))
            (naturalFiniteModel (d₂ n)) ℂ) -
          (U₂ n g : Matrix (naturalFiniteModel (d₂ n))
            (naturalFiniteModel (d₂ n)) ℂ) * U₂ n h‖ ≤ ε)
      (x : ∀ n, Matrix (naturalFiniteModel (d₁ n))
        (naturalFiniteModel (d₂ n)) ℂ)
      (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
      (_hx : ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂ x (iota γ)),
      ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂
        (fun n ↦ (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
            (naturalFiniteModel (d₁ n)) ℂ) * x n *
          (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
            (naturalFiniteModel (d₂ n)) ℂ)ᴴ) (iota γ) := by
  intro Γ H _ _ hT iota s hs d₁ d₂ hd₁ hd₂ U₁ U₂ hU₁ hU₂ x hbound hx γ
  haveI : Countable Γ := countable_of_hasKazhdanPropertyTComplex.{v, v'} hT
  obtain ⟨Γ₀, _, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hT₀ : HasKazhdanPropertyTComplex.{0, max v v'} Γ₀ := hT.mulEquiv e
  have hpull : ∀ γ₀ : Γ₀, (iota.comp e.symm.toMonoidHom) γ₀ = iota (e.symm γ₀) :=
    fun _ ↦ rfl
  have hs₀ : ∀ γ₀ : Γ₀, ∃ δ₀ : Γ₀,
      s * (iota.comp e.symm.toMonoidHom) γ₀ * s⁻¹
        = (iota.comp e.symm.toMonoidHom) δ₀ := by
    intro γ₀
    obtain ⟨δ, hδ⟩ := hs (e.symm γ₀)
    refine ⟨e δ, ?_⟩
    rw [hpull, hpull, e.symm_apply_apply]
    exact hδ
  have hx₀ : ∀ γ₀ : Γ₀, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂ x
      ((iota.comp e.symm.toMonoidHom) γ₀) :=
    fun γ₀ ↦ by rw [hpull]; exact hx (e.symm γ₀)
  have hconc := manuscriptIntertwinerTransport hT₀
    (iota.comp e.symm.toMonoidHom) s hs₀ d₁ d₂ hd₁ hd₂ U₁ U₂ hU₁ hU₂ x hbound
    hx₀ (e γ)
  rw [hpull, e.symm_apply_apply] at hconc
  exact hconc

/-- **The intertwiner transport variant at every weight, with the Kazhdan source
at an arbitrary universe** (the clause left the print on 2026-08-18).  The
scaled form of the intertwiner variant, with no
countability and no universe hypothesis on the source.

Same descent as `scaled_transport_both_anyUniverse`, with the rectangular
predicate: `mapCoreSource` fixes `t`, so the compressed sequence is unchanged
and only the homomorphism is read back along `e`. -/
theorem scaled_intertwiner_transport_anyUniverse :
    ∀ {Γ : Type v} {E : Type u} [Group Γ] [Group E]
      (B₁ B₂ : OpAlmostRepresentation E)
      (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n) (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
      (_hx : IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota x)
      (_hbound : IsScaledRectMassBounded B₁ B₂ w x),
      IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota (fun n ↦
        (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  intro Γ E _ _ B₁ B₂ w hw C x hx hbound
  haveI : Countable Γ := C.countable_source
  obtain ⟨Γ₀, _, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hx₀ : IsScaledAsymptoticIntertwinerOf B₁ B₂ w
      (CompressionUniverseTransfer.mapCoreSource C e).iota x := by
    intro γ₀
    exact hx (e.symm γ₀)
  have h := scaled_intertwiner_transport B₁ B₂ w hw
    (CompressionUniverseTransfer.mapCoreSource C e) x hx₀ hbound
  exact intertwinerOf_of_precomp C.iota e h

end TransportVariantsAnyUniverse

end GroupApproximation
