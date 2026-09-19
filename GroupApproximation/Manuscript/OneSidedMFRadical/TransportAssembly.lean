import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport

/-!
# Assembling the one-sided transport theorem

`non_mf_groups_exist.tex`, Theorem `thm:transport`, is already carried by
`Manuscript/OneSidedMFRadical/KazhdanTransport.lean`
(`manuscriptOneSidedKazhdanTransport`), and its Corollary `cor:defect-hs` by
`Manuscript/OneSidedMFRadical/DefectHS.lean`
(`manuscriptCompressionDefectHSInvisible`).  **Nothing here restates either.**

This module imports that exact theorem and supplies the three further facts the
printed proof *uses* about transport and which the manuscript-facing layer did
not state.  All three are already proved in
`Sofic/PrintedReverseTransportRoute.lean`, on the printed
ultraproduct route -- the Kazhdan projection, one-sided order, stable
finiteness, and the printed reverse step `P = VPV^* ⟹ V^*PV = P`.  So no
analysis is redone below; each declaration is the printed route read at the
manuscript's own spelling `L ≤ G`.

## What is added, and why each is needed

* **The hypotheses survive transport.**  The printed theorem takes `(x_n)`
  uniformly bounded in operator norm and asymptotically `L`-central in
  normalized Hilbert--Schmidt norm, and returns two new sequences.  It does not
  say that those two sequences are again uniformly bounded, so as printed it
  cannot be applied to its own conclusion.  They are
  (`IsUniformlyBounded.adjointSequence` and its coadjoint twin: conjugating by
  a unitary is isometric for the operator norm), and
  `OneSidedKazhdanTransportPackage` records the whole input package as
  transported.  This is what makes the theorem iterable, and iterating it is
  exactly what the next item needs.
* **The compression *group*, not just one compressor.**  `printedDefect` is
  the normal closure of commutators over the *set* `Comp_G(L)`, while the
  development's `compressionCentralizerDefect` conjugates by
  `compressionGroup L`, the subgroup that set generates.
  `PrintedDefect.lean` records the containment between the two defects but
  states no transport for the larger index set.
  `CompressionGroupKazhdanTransport` is that transport at the printed
  spelling: every element of `compressionGroup L` -- every word in one-sided
  compressors and their inverses, whether or not it is itself one -- acts as a
  two-sided symmetry of the bounded asymptotic commutant.  It is the manuscript
  layer's carrier for the corollary that a one-sided conjugator preserves the
  commutant under conjugation *and* inverse conjugation, applied along a word.
* **The ambient group at an arbitrary universe.**  The printed theorem places
  no size hypothesis on `G`; `manuscriptOneSidedKazhdanTransport` fixes it at
  `Type 0`.  `OneSidedKazhdanTransportAnyAmbient` frees it.  The Kazhdan source
  stays at `Type 0`, because property `(T)` is spelled
  `HasKazhdanPropertyT.{0, 0}`, whose group argument that notation pins to the
  smallest universe; the subgroup is therefore presented as the range of a
  homomorphism from a `Type 0` group rather than as `L : Subgroup G`.  That is
  not a hypothesis the print does not grant -- property `(T)` forces
  countability, so a Kazhdan subgroup of any ambient group is the range of such
  a homomorphism, which is the content of
  `countable_of_hasKazhdanPropertyTComplex` and
  `Sofic/KazhdanTransportAnyUniverse.lean` -- but the descent itself is *not*
  performed here, so the statement below is the one with the homomorphism in
  it, not the one with `L : Subgroup G` in it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Matrix
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

universe u

/-! ## The printed hypotheses are closed under transport -/

/-- **The input package of `thm:transport` transports with the sequence.**

Both conclusions of the printed theorem are again uniformly bounded in
operator norm and again asymptotically central for `L`, so each of them
satisfies the theorem's own hypotheses on `(x_n)`.  The boundedness half is
isometry of unitary conjugation; the centrality half is the printed theorem. -/
def OneSidedKazhdanTransportPackage : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ (B : OpAlmostRepresentation G)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      IsAsymptoticCommutantOf B L.subtype x →
      IsUniformlyBounded B x →
      ∀ compressor ∈ compressionSet L,
        (IsUniformlyBounded B (adjointSequence B compressor x) ∧
            IsAsymptoticCommutantOf B L.subtype
              (adjointSequence B compressor x)) ∧
          (IsUniformlyBounded B (coadjointSequence B compressor x) ∧
            IsAsymptoticCommutantOf B L.subtype
              (coadjointSequence B compressor x))

/-- Closed proof that transport returns data of the same kind it consumes. -/
theorem manuscriptOneSidedKazhdanTransportPackage :
    OneSidedKazhdanTransportPackage := by
  intro G _ L hT B x hx hbound compressor hcompressor
  have hset : compressor ∈ compressionSet L.subtype.range := by
    rwa [L.range_subtype]
  have hcompressor' : compressor ∈ compressionGroup L.subtype.range :=
    Subgroup.subset_closure hset
  obtain ⟨hadjoint, hcoadjoint⟩ :=
    KazhdanAsymptoticCommutant.compressionGroup_transport_both_printed
      B L.subtype hT hcompressor' x hbound hx
  exact ⟨⟨hbound.adjointSequence, hadjoint⟩,
    ⟨hbound.coadjointSequence, hcoadjoint⟩⟩

/-! ## Every word in one-sided compressors transports -/

/-- **Transport along the compression group.**

The printed theorem is stated for a single `u` with `uLu⁻¹ ≤ L`.  Since the
transported data again satisfies the theorem's hypotheses, the elements that
transport the bounded asymptotic commutant in both directions form a subgroup,
so every element of `compressionGroup L` transports -- including the elements
of that subgroup which are not themselves one-sided compressors.  This is the
index set of `compressionCentralizerDefect`, the defect
`printedDefect_le_compressionCentralizerDefect` compares the printed defect
against. -/
def CompressionGroupKazhdanTransport : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ (B : OpAlmostRepresentation G)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      IsAsymptoticCommutantOf B L.subtype x →
      IsUniformlyBounded B x →
      ∀ g ∈ compressionGroup L,
        IsAsymptoticCommutantOf B L.subtype (adjointSequence B g x) ∧
          IsAsymptoticCommutantOf B L.subtype (coadjointSequence B g x)

/-- Closed proof of transport along the whole compression group. -/
theorem manuscriptCompressionGroupKazhdanTransport :
    CompressionGroupKazhdanTransport := by
  intro G _ L hT B x hx hbound g hg
  have hg' : g ∈ compressionGroup L.subtype.range := by
    rwa [L.range_subtype]
  exact KazhdanAsymptoticCommutant.compressionGroup_transport_both_printed
    B L.subtype hT hg' x hbound hx

/-! ## The ambient group at an arbitrary universe -/

/-- **`thm:transport` with no size hypothesis on the ambient group.**

The printed statement quantifies over an arbitrary group `G`; the `Type 0`
endpoint is strictly narrower.  Here `G` lives in an arbitrary universe and the
property-`(T)` subgroup is presented as `ι(Γ)` for a homomorphism `ι` from a
`Type 0` group, which is where `HasKazhdanPropertyT.{0, 0}` puts its argument.
The compressor is quantified over the group generated by the one-sided
compressors of that image, so this is simultaneously the any-universe form of
`CompressionGroupKazhdanTransport`; taking `ι = L.subtype` and `u ∈ Comp_G(L)`
returns the printed statement. -/
def OneSidedKazhdanTransportAnyAmbient : Prop :=
  ∀ (G : Type u) [Group G] (Gamma : Type) [Group Gamma] (iota : Gamma →* G),
    HasKazhdanPropertyT.{0, 0} Gamma →
    ∀ (B : OpAlmostRepresentation G)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      IsAsymptoticCommutantOf B iota x →
      IsUniformlyBounded B x →
      ∀ g ∈ compressionGroup iota.range,
        IsAsymptoticCommutantOf B iota (adjointSequence B g x) ∧
          IsAsymptoticCommutantOf B iota (coadjointSequence B g x)

/-- Closed proof of the printed transport theorem with the ambient group in an
arbitrary universe. -/
theorem manuscriptOneSidedKazhdanTransportAnyAmbient :
    OneSidedKazhdanTransportAnyAmbient := by
  intro G _ Gamma _ iota hT B x hx hbound g hg
  exact KazhdanAsymptoticCommutant.compressionGroup_transport_both_printed
    B iota hT hg x hbound hx

end OneSidedMFRadical
end Manuscript
end GroupApproximation
