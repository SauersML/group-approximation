import GroupApproximation.Sofic.NormMFResidualFunctorial
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.LiteralWitnessConsequences
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The simple sofic envelope: everything downstream of the embedding

The manuscript's paragraph *A simple sofic envelope* reads as follows.  The
file is under concurrent edit, so it is located only by its stable anchors: the
heading `\paragraph{A simple sofic envelope.}` and the citation key
`ElekSzaboHyper`
(which also distinguishes it from the Elek--Szabó *amenable-extension*
theorem, cited elsewhere in the same section under the key `ElekSzabo`).

> There is a countable simple sofic group `S_simp` with
> `Res_MF(S_simp) = S_simp`.  Equivalently, every homomorphism from `S_simp`
> to an MF group is trivial.
>
> *Proof.* By Elek--Szabó, every countable sofic group embeds in a countable
> simple sofic group.  Embed `W` in such a group.  Functoriality of the MF
> radical sends `ζ` to a nontrivial element of the MF radical of the simple
> group.  That radical is normal, so it is the whole group.  Every
> homomorphism to an MF group kills the MF radical.

The printed argument has four steps:

1. **(existence)** every countable sofic group embeds in a countable simple
   sofic group — the Elek--Szabó input;
2. **(transport)** functoriality of the MF radical carries the witness mark
   `ζ` to a nontrivial element of the radical of the simple group;
3. **(normality)** the radical is normal, so in a simple group a single
   nontrivial member forces it to be everything;
4. **(triviality)** homomorphisms into MF groups kill the radical.

This file certifies steps 2, 3 and 4 for the manuscript's actual witness `W`
(`LiteralNonMFLinearWitness.WitnessGroup`) and its actual mark `ζ`
(`MarkedCompression.signAmbient`), and in addition proves the "Equivalently"
of the displayed statement as a genuine equivalence — the manuscript only ever
uses the forward direction, but the word *equivalently* asserts both.

Step 1 is **not** proved here and is not assumed here either: no declaration
in this file has a hypothesis asserting that such an envelope exists.  What is
proved is the implication *from a concrete envelope*, i.e. from a countable
simple group receiving the witness injectively.  The existence half is
developed, as far as it currently goes, in
`GroupApproximation.Sofic.SoficEnvelopeExistence`, whose module docstring
states precisely what remains open.

The radical used is the manuscript's own one: `coronaMFResidual`, the
intersection of the kernels of all homomorphisms into unitary groups of
standard cofinite norm-matrix coronas.  For countable groups it coincides with
the ultraproduct residual `normMFResidual`
(`coronaMFResidual_eq_normMFResidual`), and both forms are recorded.
-/

namespace GroupApproximation
namespace SimpleSoficEnvelope

universe u v

/-! ## Step 2: transport of the mark along an embedding -/

/-- An injective homomorphism does not kill a nontrivial element.  This is the
only property of the Elek--Szabó embedding that the manuscript's argument
uses. -/
theorem map_ne_one_of_injective {G : Type u} [Group G] {S : Type v} [Group S]
    (f : G →* S) (hf : Function.Injective f) {x : G} (hx : x ≠ 1) : f x ≠ 1 := by
  intro h
  exact hx (hf (h.trans (map_one f).symm))

/-- **Steps 2 and 3.**  Functoriality of the MF radical carries a nontrivial
invisible element through an embedding, and normality of the radical inside a
simple target promotes it to the whole target. -/
theorem normMFResidual_eq_top_of_simple_of_embedding
    {G : Type u} [Group G] {S : Type v} [Group S] [IsSimpleGroup S]
    (f : G →* S) (hf : Function.Injective f) {x : G}
    (hx : NormMFInvisible x) (hne : x ≠ 1) :
    normMFResidual S = ⊤ :=
  normMFResidual_eq_top_of_simple (hx.map f) (map_ne_one_of_injective f hf hne)

/-- The same conclusion in the manuscript's own radical: `Res_MF(S) = S`. -/
theorem coronaMFResidual_eq_top_of_simple_of_embedding
    {G : Type u} [Group G] {S : Type v} [Group S] [Countable S] [IsSimpleGroup S]
    (f : G →* S) (hf : Function.Injective f) {x : G}
    (hx : NormMFInvisible x) (hne : x ≠ 1) :
    coronaMFResidual S = ⊤ := by
  rw [coronaMFResidual_eq_normMFResidual]
  exact normMFResidual_eq_top_of_simple_of_embedding f hf hx hne

/-! ## Step 4 and its converse: the "equivalently" of the displayed statement -/

/-- **Step 4.**  A full MF radical kills every homomorphism into an MF group.
No countability is needed on the target: the homomorphism factors through its
range, and operator MF passes to subgroups. -/
theorem map_eq_one_of_coronaMFResidual_eq_top
    {S : Type} [Group S] [Countable S] (htop : coronaMFResidual S = ⊤)
    {H : Type*} [Group H] (hH : IsOperatorMF H) (φ : S →* H) (s : S) : φ s = 1 := by
  have hnorm : normMFResidual S = ⊤ := by
    rw [← coronaMFResidual_eq_normMFResidual]
    exact htop
  exact map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF hnorm hH φ s

/-- The converse direction of the manuscript's *equivalently*: if every
homomorphism into an MF group is trivial then the MF radical is everything.
The target realizing the test is the range of a corona representation, which
is operator MF by construction. -/
theorem coronaMFResidual_eq_top_of_forall_map_eq_one
    {S : Type} [Group S]
    (h : ∀ (H : Type) [Group H], IsOperatorMF H → ∀ (φ : S →* H) (s : S), φ s = 1) :
    coronaMFResidual S = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  show CoronaMFInvisible x
  intro X hX rho
  have hMF : IsOperatorMF rho.range :=
    ⟨X, hX, rho.range.subtype, Subtype.val_injective⟩
  have hone : rho.rangeRestrict x = 1 := h rho.range hMF rho.rangeRestrict x
  simpa using congrArg Subtype.val hone

/-- **The displayed equivalence of the manuscript paragraph.**  For a countable
group, `Res_MF(S) = S` holds exactly when every homomorphism from `S` to an MF
group is trivial. -/
theorem coronaMFResidual_eq_top_iff_forall_map_eq_one {S : Type} [Group S] [Countable S] :
    coronaMFResidual S = ⊤ ↔
      ∀ (H : Type) [Group H], IsOperatorMF H → ∀ (φ : S →* H) (s : S), φ s = 1 := by
  constructor
  · intro htop H _ hH φ s
    exact map_eq_one_of_coronaMFResidual_eq_top htop hH φ s
  · exact coronaMFResidual_eq_top_of_forall_map_eq_one

/-- A group with full MF radical is itself not MF, provided it is nontrivial.
This is the sanity check that the envelope statement is not vacuous. -/
theorem not_isOperatorMF_of_coronaMFResidual_eq_top
    {S : Type} [Group S] [Countable S] [Nontrivial S]
    (htop : coronaMFResidual S = ⊤) : ¬ IsOperatorMF S := by
  intro hMF
  rw [isOperatorMF_iff_coronaMFResidual_eq_bot] at hMF
  have hbot : (⊤ : Subgroup S) = ⊥ := htop.symm.trans hMF
  obtain ⟨x, hx⟩ := exists_ne (1 : S)
  have hmem : x ∈ (⊥ : Subgroup S) := by
    rw [← hbot]
    exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hmem)

/-! ## The manuscript's witness and its mark

The manuscript embeds its concrete witness `W`, and transports its concrete
mark `ζ`.  Both are already in the library: `W` is
`LiteralNonMFLinearWitness.WitnessGroup`, and `ζ` is the surviving Clifford
sign `MarkedCompression.signAmbient`. -/

/-- The manuscript's `ζ`: the surviving Clifford sign of the concrete witness
is nontrivial and invisible to every operator-norm matrix ultraproduct. -/
theorem witness_mark_ne_one_and_normMFInvisible :
    MarkedCompression.signAmbient LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective ≠ 1 ∧
      NormMFInvisible (MarkedCompression.signAmbient LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective) :=
  ⟨MarkedCompression.signAmbient_ne_one LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective,
    LiteralWitnessConsequences.witness_sign_normMFInvisible⟩

/-- **The manuscript paragraph, downstream of its Elek--Szabó input.**  Let `S`
be any countable simple group receiving the concrete witness `W` injectively.
Then

* `Res_MF(S) = S` in the manuscript's cofinite-corona radical,
* the same in the ultraproduct residual,
* every homomorphism from `S` into an MF group is trivial, and
* `S` is itself not MF.

The hypothesis is a property of the *given* group `S`, not an assumption that
such an `S` exists; producing one is the content of
`GroupApproximation.Sofic.SoficEnvelopeExistence` and is not complete. -/
theorem simpleEnvelope_of_witnessEmbedding
    {S : Type} [Group S] [Countable S] [IsSimpleGroup S]
    (f : LiteralNonMFLinearWitness.WitnessGroup →* S) (hf : Function.Injective f) :
    coronaMFResidual S = ⊤ ∧ normMFResidual S = ⊤ ∧
      (∀ (H : Type) [Group H], IsOperatorMF H → ∀ (φ : S →* H) (s : S), φ s = 1) ∧
      ¬ IsOperatorMF S := by
  obtain ⟨hne, hinv⟩ := witness_mark_ne_one_and_normMFInvisible
  have hnorm : normMFResidual S = ⊤ :=
    normMFResidual_eq_top_of_simple_of_embedding f hf hinv hne
  have hcor : coronaMFResidual S = ⊤ := by
    rw [coronaMFResidual_eq_normMFResidual]
    exact hnorm
  refine ⟨hcor, hnorm, ?_, not_isOperatorMF_of_coronaMFResidual_eq_top hcor⟩
  intro H _ hH φ s
  exact map_eq_one_of_coronaMFResidual_eq_top hcor hH φ s

end SimpleSoficEnvelope
end GroupApproximation
