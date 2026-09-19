import GroupApproximation.Sofic.CompressionUniverseTransfer
import GroupApproximation.Sofic.KazhdanTransportAnyUniverse

/-!
# `def:pattern` with the Kazhdan source in any universe

`non_mf_group_notes.tex` introduces the object all of `\section{Obstructions
from a one-sided conjugation datum}` (`\label{sec:conj}`) is stated about:

> Let `H` be a countable group.  A *Kazhdan conjugation datum* in `H` is a tuple
> `(Λ, ι, t, c)`, where `Λ` is a countable group with property (T),
> `ι : Λ → H` is a group homomorphism, not assumed injective, and `t, c ∈ H`,
> subject to
> (M1) `t ι(λ) t⁻¹ ∈ ι(Λ)` for every `λ ∈ Λ`;
> (M2) `c ι(λ) = ι(λ) c` for every `λ ∈ Λ`.

No universe is named for `Λ`, and the packaging that carried this claim,
`ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern`, pinned it at
`Type 0`.  That is ledger row `CD.01`, graded `MISMATCH` with the note
"univ0 on Gamma; H is polymorphic".

This module removes the pin, and supplies the three lemmas that the rest of the
universe-generalization cluster (`FN.00`, `NK.00`, `NK.16`, `NK.17`, `ID.04`,
`ID.09`, `PA.14`) consumes.  It follows the route established by
`Sofic.KazhdanTransportAnyUniverse` and `Sofic.TransportVariantsAnyUniverse`:
**property `(T)` implies countability**, so a Kazhdan source in any universe has
a `Type 0` model, the datum travels to that model by
`CompressionUniverseTransfer.mapCoreSource`, and the `Type 0` theorem applies
there.  Nothing the print does not state is assumed; the countability is
derived, and here it is even *certified* — `Countable Λ` is a conclusion of the
wrapper below rather than one of its hypotheses.

## What the descent needs, beyond `mapCoreSource`

`mapCoreSource C e` reindexes `ι` along `e⁻¹` and leaves `t` and `c` alone.  So

* its defect normal closure is *literally the same subgroup* — the generating
  set `{[d, ι(λ)] : λ ∈ Λ}` is a range, and precomposing a range with a
  bijection does not change it (`mapCoreSource_defectNormal`);
* the image `ι(Λ)`, which the intrinsic statements of `sec:conj` are about, is
  likewise unchanged (`range_comp_mulEquiv`).

Those two facts are what let a hypothesis stated upstairs be handed to the
`Type 0` theorem unmodified, and are the reason no conclusion has to be
translated back for the datum-based rows.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v v' w

/-! ## Property `(T)` forces countability, in the real form

`countable_of_hasKazhdanPropertyTComplex` of `Sofic.KazhdanTransportAnyUniverse`
is this statement for the complex-unitary form.  The rows whose printed
hypothesis is rendered by the real form need it at the group's own
representation universe; `Leavitt.GeneralCornerTheorem.countable_of_hasKazhdanPropertyT`
is the `Type 0` case. -/

/-- **A Kazhdan group is countable**, in the real form and at every universe.
Property `(T)` supplies a finite symmetric generating set, and a group generated
by a finite set is countable.  This is what makes the universe descents below
legitimate rather than a weakening: the printed statements grant countability of
the Kazhdan source, and none of the wrappers assume it — each derives it. -/
theorem countable_of_hasKazhdanPropertyT {G : Type v} [Group G]
    (h : HasKazhdanPropertyT.{v, v} G) : Countable G := by
  obtain ⟨S, -, -, hS⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset G h
  exact GeneralCornerTheorem.countable_of_closure_finset_eq_top hS

namespace CompressionUniverseTransfer

/-! ## Precomposition with an isomorphism of the source -/

/-- **Precomposing with an isomorphism does not change the image.**  The
manuscript writes `L = ι(Λ)` and states the intrinsic results of `sec:conj`
about `L`; the `Type 0` model of `Λ` is reached by precomposing `ι` with an
isomorphism, and this records that the object those results speak about is
untouched by that step. -/
theorem range_comp_mulEquiv {Γ₁ : Type v} [Group Γ₁] {Γ₂ : Type v'} [Group Γ₂]
    {E : Type u} [Group E] (iota : Γ₁ →* E) (e : Γ₂ ≃* Γ₁) :
    (iota.comp e.toMonoidHom).range = iota.range := by
  ext x
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨γ₂, hγ₂⟩
    exact ⟨e γ₂, hγ₂⟩
  · rintro ⟨γ₁, hγ₁⟩
    refine ⟨e.symm γ₁, ?_⟩
    show iota (e (e.symm γ₁)) = x
    rw [e.apply_symm_apply]
    exact hγ₁

/-- The pointwise compression defects of the transported datum are the pointwise
compression defects of the original.  `mapCoreSource` fixes `t` and `c`, hence
`d = tct⁻¹`, and reindexes `ι` along a bijection, so the displayed set
`{[d, ι(λ)] : λ ∈ Λ}` of `def:pattern` is the same set. -/
theorem mapCoreSource_defectSet {Γ₁ : Type v} [Group Γ₁] {Γ₂ : Type v'}
    [Group Γ₂] {E : Type u} [Group E]
    (C : KazhdanCompressionCore Γ₁ E) (e : Γ₁ ≃* Γ₂) :
    (mapCoreSource C e).defectSet = C.defectSet := by
  have hL : (mapCoreSource C e).defectSet
      = Set.range (fun γ₂ : Γ₂ ↦ ⁅C.transported, C.iota (e.symm γ₂)⁆) := rfl
  have hR : C.defectSet
      = Set.range (fun γ₁ : Γ₁ ↦ ⁅C.transported, C.iota γ₁⁆) := rfl
  rw [hL, hR]
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨γ₂, hγ₂⟩
    exact ⟨e.symm γ₂, hγ₂⟩
  · rintro ⟨γ₁, hγ₁⟩
    refine ⟨e γ₁, ?_⟩
    rw [e.symm_apply_apply]
    exact hγ₁

/-- **`N_conj` does not move when the Kazhdan source is replaced by an
isomorphic one.**  This is the fact that makes every datum-based descent in
`sec:conj` a one-liner: a subgroup assumed to lie inside `N_conj` upstairs lies
inside the `N_conj` of the transported datum with no translation at all. -/
theorem mapCoreSource_defectNormal {Γ₁ : Type v} [Group Γ₁] {Γ₂ : Type v'}
    [Group Γ₂] {E : Type u} [Group E]
    (C : KazhdanCompressionCore Γ₁ E) (e : Γ₁ ≃* Γ₂) :
    (mapCoreSource C e).defectNormal = C.defectNormal := by
  show Subgroup.normalClosure (mapCoreSource C e).defectSet
      = Subgroup.normalClosure C.defectSet
  rw [mapCoreSource_defectSet]

end CompressionUniverseTransfer

namespace ManuscriptExactWrappers

/-- **`def:pattern` with the Kazhdan source at an arbitrary universe** (ledger
row `CD.01`).

Exact data and defect subgroup of a Kazhdan conjugation datum: the source has
property `(T)` in both the real and the textbook complex-unitary form, `(M1)`
and `(M2)` hold as printed, and the datum determines `N_conj` as the normal
closure of the displayed commutators `[d, ι(λ)]`, normal in the ambient group.

Two things differ from `manuscriptMarkedKazhdanPattern`, which this replaces.

* The source is at an arbitrary universe.  The printed definition names none.
* `Countable Λ` moves from hypothesis to **conclusion**.  The print says
  "`Λ` is a countable group with property (T)", and the `Type 0` packaging
  carried that as an instance binder; here it is derived from the datum's own
  `kazhdan` field, so the wrapper certifies the printed clause instead of
  assuming it.  `Countable H` stays a hypothesis, as printed.

Every binder is after the colon: the zero-input gate rejects a badged
declaration with header binders. -/
theorem manuscriptMarkedKazhdanPattern_anyUniverse :
    ∀ {Gamma : Type v} {H : Type u} [Group Gamma] [Group H]
      [_countableH : Countable H]
      (C : KazhdanCompressionCore Gamma H),
    Countable Gamma ∧
      HasKazhdanPropertyT.{v, v} Gamma ∧
      HasKazhdanPropertyTComplex.{v, max v w} Gamma ∧
      (∀ gamma : Gamma, ∃ delta : Gamma,
        C.t * C.iota gamma * C.t⁻¹ = C.iota delta) ∧
      (∀ gamma : Gamma, Commute C.c (C.iota gamma)) ∧
      C.defectNormal = Subgroup.normalClosure
        (Set.range fun gamma : Gamma ↦
          ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) ∧
      C.defectNormal.Normal := by
  intro Gamma H _ _ _ C
  exact ⟨C.countable_source, C.kazhdan,
    hasKazhdanPropertyT_iff_textbook.mp C.kazhdan,
    C.compresses, C.comm_c, rfl, inferInstance⟩

end ManuscriptExactWrappers

end GroupApproximation
