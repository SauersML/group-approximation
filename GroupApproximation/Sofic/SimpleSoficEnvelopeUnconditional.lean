import GroupApproximation.Algebra.InvolutionBlockAssembly
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Sofic.SoficEnvelopeWitness

/-!
# The simple sofic envelope, with no premise

`Sofic/SoficEnvelopeSimplicity.lean` carries the one external input of the
Elek--Szabó envelope theorem (proof-ledger row `SO.17`) as the spelled-out
premise `hBNG`, **bounded normal generation of finite alternating groups**, on
exactly three declarations.  This file proves that premise and restates those
three conclusions without it.

## The premise, proved

`boundedNormalGeneration` is `hBNG` verbatim.  Its proof is the elementary
route, assembled from the two halves built in `Algebra/`:

* *production* — one commutator with `s` doubles any permutation supported off
  its own image, so every doubled cycle type whose half fits in a third of
  `supp s` is a product of **two** conjugates of `s^{±1}`
  (`AlternatingDoubledTransport.isBoundedConjProduct_two_of_cycleType_doubled`);
* *consumption* — an even permutation is a product of two involutions, each of
  which cuts into blocks of bounded size whose cycle types are doublings, with
  a parity repair through one spare transposition
  (`InvolutionBlocks.isBoundedConjProduct_of_sign_eq_one`).

The constants: with `F = ⌈12/δ⌉` the block capacity is `c = |supp s| / 6`, the
count is `K = 4F + 4`, and the threshold is `M = 12F + 12`.  `K` depends on `δ`
alone, which is the whole content of the premise — a bound varying with the
index is exactly what the metric ultraproduct cannot absorb, as the module
docstring of `Sofic/SoficEnvelopeSimplicity.lean` records.

Neither the evenness of `s` nor the threshold `M` is used by the production
half; they are consumed only through the arithmetic that turns the density
hypothesis into the fuel.

## What this changes

The three declarations that carried `hBNG` —
`SoficEnvelopeSimplicity.isSimpleGroup_universalSofic`,
`SoficEnvelopeSimplicity.exists_countable_simple_sofic_envelope` and
`SoficEnvelopeWitness.manuscript_simpleSoficEnvelope` — are restated here with
the premise discharged.  The manuscript's paragraph *A simple sofic envelope*
prints a citation to Elek--Szabó for the sentence itself; what changes is that
the repository no longer takes anything on trust for it.
-/

namespace GroupApproximation
namespace SimpleSoficEnvelopeUnconditional

open SoficEnvelopeSimplicity InvolutionBlocks

/-! ## Bounded normal generation -/

/-- **Bounded normal generation of finite alternating groups.**  For every
`δ > 0` there are `K` and `M` such that in a model of at least `M` points, an
even permutation whose support is at least a `δ`-fraction of the model has
every even permutation as a product of at most `K` conjugates of it and its
inverse.

This is the premise `hBNG` of `Sofic/SoficEnvelopeSimplicity.lean`, verbatim. -/
theorem boundedNormalGeneration (δ : ℝ) (hδ : 0 < δ) :
    ∃ K M : ℕ,
      ∀ (Y : FiniteModel) (s a : Equiv.Perm Y), M ≤ Fintype.card Y →
        Equiv.Perm.sign s = 1 →
        δ * (Fintype.card Y : ℝ) ≤ ((s.support.card : ℝ)) →
        Equiv.Perm.sign a = 1 → IsBoundedConjProduct s K a := by
  classical
  refine ⟨4 * ⌈12 / δ⌉₊ + 4, 12 * ⌈12 / δ⌉₊ + 12, ?_⟩
  intro Y s a hM _hs hdens ha
  -- the ceiling clears `12/δ`
  have hFδ : (12 : ℝ) ≤ δ * (⌈12 / δ⌉₊ : ℝ) := by
    have h1 : (12 / δ : ℝ) ≤ (⌈12 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : δ * (12 / δ) = 12 := by field_simp
    nlinarith [h1, hδ.le]
  have hF1 : 0 < ⌈12 / δ⌉₊ := Nat.ceil_pos.mpr (div_pos (by norm_num) hδ)
  -- the density hypothesis, cleared of `δ`
  have hn0 : (0 : ℝ) ≤ ((Fintype.card Y : ℕ) : ℝ) := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ ((⌈12 / δ⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hreal : (12 : ℝ) * ((Fintype.card Y : ℕ) : ℝ)
      ≤ ((⌈12 / δ⌉₊ : ℕ) : ℝ) * ((s.support.card : ℕ) : ℝ) := by
    calc (12 : ℝ) * ((Fintype.card Y : ℕ) : ℝ)
        ≤ (δ * ((⌈12 / δ⌉₊ : ℕ) : ℝ)) * ((Fintype.card Y : ℕ) : ℝ) := by
          nlinarith
      _ = ((⌈12 / δ⌉₊ : ℕ) : ℝ) * (δ * ((Fintype.card Y : ℕ) : ℝ)) := by ring
      _ ≤ ((⌈12 / δ⌉₊ : ℕ) : ℝ) * ((s.support.card : ℕ) : ℝ) := by nlinarith
  have hnat : 12 * Fintype.card Y ≤ ⌈12 / δ⌉₊ * s.support.card := by
    exact_mod_cast hreal
  -- the support of `s` is large, so the block capacity is positive
  have hmul : ⌈12 / δ⌉₊ * 144 ≤ ⌈12 / δ⌉₊ * s.support.card := by omega
  have hm144 : 144 ≤ s.support.card := Nat.le_of_mul_le_mul_left hmul hF1
  -- there is fuel enough for any involution
  have hFm : ⌈12 / δ⌉₊ * s.support.card
      ≤ ⌈12 / δ⌉₊ * (6 * (s.support.card / 6) + 5) :=
    Nat.mul_le_mul le_rfl (by omega)
  have hexp : ⌈12 / δ⌉₊ * (6 * (s.support.card / 6) + 5)
      = 6 * (⌈12 / δ⌉₊ * (s.support.card / 6)) + 5 * ⌈12 / δ⌉₊ := by ring
  exact isBoundedConjProduct_of_sign_eq_one (c := s.support.card / 6)
    (fuel := ⌈12 / δ⌉₊) (by omega) (by omega) (by omega) (by omega) ha

/-! ## The three conclusions, restated without the premise -/

/-- **Simplicity of the universal sofic group**, unconditionally. -/
theorem isSimpleGroup_universalSofic {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i)) :
    IsSimpleGroup (UniversalSofic 𝒰 X) :=
  SoficEnvelopeSimplicity.isSimpleGroup_universalSofic 𝒰 X hdiv
    boundedNormalGeneration

/-- **The Elek--Szabó envelope theorem**, unconditionally: every countable
sofic group embeds in a countable simple sofic group. -/
theorem exists_countable_simple_sofic_envelope {G : Type*} [Group G]
    [Countable G] (hG : IsSofic G) :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E ∧
        ∃ f : G →* ↥E, Function.Injective f :=
  SoficEnvelopeSimplicity.exists_countable_simple_sofic_envelope
    boundedNormalGeneration hG

/-- **The manuscript's displayed statement**, unconditionally: there is a
countable simple sofic group equal to its own MF radical. -/
theorem manuscript_simpleSoficEnvelope :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E ∧
        coronaMFResidual ↥E = ⊤ ∧ normMFResidual ↥E = ⊤ ∧
        (∀ (H : Type) [Group H], IsOperatorMF H →
          ∀ (φ : ↥E →* H) (s : ↥E), φ s = 1) ∧
        ¬ IsOperatorMF ↥E :=
  SoficEnvelopeWitness.manuscript_simpleSoficEnvelope boundedNormalGeneration

/-! ## The torsion-free-quotient no-go

The envelope above contains the concrete witness injectively.  In particular
it contains the witness's nontrivial Clifford sign, an involution.  Since the
envelope is simple, killing that one element kills the whole envelope.  Every
map to a torsion-free group therefore is trivial; passing to the universal
torsion-free quotient cannot turn this unconditional non-MF group into a
torsion-free non-MF example. -/

/-- A simple envelope receiving the concrete witness injectively has no
nontrivial torsion-free image. -/
theorem hom_eq_one_to_isPowerTorsionFree_of_witnessEmbedding
    {E : Type*} [Group E] [IsSimpleGroup E]
    (f : LiteralNonMFLinearWitness.WitnessGroup →* E)
    (hf : Function.Injective f) {T : Type*} [Group T]
    (hT : IsPowerTorsionFree T) (phi : E →* T) : phi = 1 := by
  let z : LiteralNonMFLinearWitness.WitnessGroup :=
    MarkedCompression.signAmbient LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective
  have hz_ne : f z ≠ 1 := by
    apply SimpleSoficEnvelope.map_ne_one_of_injective f hf
    exact MarkedCompression.signAmbient_ne_one LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective
  have hz_sq : z ^ 2 = 1 :=
    MarkedCompression.signAmbient_sq LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective
  have hkill : phi (f z) = 1 := by
    apply hT (phi (f z)) 2 (by decide)
    rw [← map_pow, ← map_pow, hz_sq, map_one, map_one]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal phi.ker inferInstance with
    hbot | htop
  · exfalso
    apply hz_ne
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact MonoidHom.mem_ker.mpr hkill
  · apply MonoidHom.ext
    intro x
    apply MonoidHom.mem_ker.mp
    rw [htop]
    exact Subgroup.mem_top x

/-- **Premise-free torsion-free no-go for the manuscript envelope.**  There
is an unconditional countable simple sofic full-MF-radical envelope for which
every map to every torsion-free group is trivial; consequently that envelope
itself is not torsion-free. -/
theorem manuscript_simpleSoficEnvelope_no_torsionFree_image :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↑E ∧ IsSimpleGroup ↑E ∧ IsSofic ↑E ∧
        coronaMFResidual ↑E = ⊤ ∧ normMFResidual ↑E = ⊤ ∧
        (∀ (T : Type) [Group T], IsPowerTorsionFree T →
          ∀ phi : ↑E →* T, phi = 1) ∧
        ¬ IsPowerTorsionFree ↑E := by
  obtain ⟨𝒰, X, E, hEc, hEs, hEsofic, f, hf⟩ :=
    exists_countable_simple_sofic_envelope
      LiteralWitnessConsequences.witnessGroup_isSofic
  letI : Countable ↑E := hEc
  letI : IsSimpleGroup ↑E := hEs
  obtain ⟨hcorona, hnorm, -, -⟩ :=
    SimpleSoficEnvelope.simpleEnvelope_of_witnessEmbedding f hf
  have hmaps : ∀ (T : Type) [Group T], IsPowerTorsionFree T →
      ∀ phi : ↑E →* T, phi = 1 := by
    intro T _ hT phi
    exact hom_eq_one_to_isPowerTorsionFree_of_witnessEmbedding f hf hT phi
  refine ⟨𝒰, X, E, hEc, hEs, hEsofic, hcorona, hnorm, hmaps, ?_⟩
  intro htf
  have hid : MonoidHom.id ↑E = 1 := hmaps ↑E htf (MonoidHom.id ↑E)
  let z : LiteralNonMFLinearWitness.WitnessGroup :=
    MarkedCompression.signAmbient LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective
  have hz_ne : f z ≠ 1 := by
    apply SimpleSoficEnvelope.map_ne_one_of_injective f hf
    exact MarkedCompression.signAmbient_ne_one LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective
  apply hz_ne
  simpa using DFunLike.congr_fun hid (f z)

end SimpleSoficEnvelopeUnconditional
end GroupApproximation
