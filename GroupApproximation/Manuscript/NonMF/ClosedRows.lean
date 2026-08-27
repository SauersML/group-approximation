import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.SimpleSoficEnvelope
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# Manuscript-facing restatements for three regraded ledger rows

`notes/NON_MF_PROOF_LEDGER.md` grades printed sentences against Lean
declarations.  Three of its rows were regraded on 2026-08-17 from `MISSING` to
`EXACT` because the tree turned out to prove what they recorded as absent, and
in each case the internal declaration is stated in the shape its own module
needed rather than in the shape the manuscript prints.  This file restates the
three printed sentences directly, so that a reader can see the printed
quantification without reconstructing it from a `variable` block.

Nothing here is new mathematics and nothing here is a proof.  Each theorem is
the printed sentence, proved by handing the hypotheses to the internal
declaration the ledger row names:

* `manuscriptLEFImpliesMF` -- `INT.10`, "LEF groups are MF".  The manuscript's
  standing convention is that all groups are discrete and countable, so
  `[Countable G]` is the convention rather than an added hypothesis, and the
  printed sentence is a statement about groups rather than about a `variable`.
* `manuscriptSoficByAmenableExtension` -- `SO.15`, "soficity is preserved by
  every extension with amenable quotient".  The row had recorded that only the
  `ℤ` case was formalized; `Sofic.SoficByAmenablePermanence` proves the general
  case with no countability premise and no splitting hypothesis.
* `manuscriptSimpleEnvelopeFromLiteralEmbedding` -- `SO.18`.  This one is not
  only a restatement.  The printed proof of *A simple sofic envelope* used to
  embed the witness group `W` and now embeds `E`, which is sofic by
  `thm:Esofic`; `Sofic.SimpleSoficEnvelope` supplies the argument at `W`
  (`simpleEnvelope_of_witnessEmbedding`) and the general lemmas it is built
  from, but no declaration instantiated them at the literal `E`.  That is what
  this one does, from `LiteralNonMFEndpoint.cliffordSign_blackHole`.

This module is in the root import closure and MSI-validated green as of
`ce9ea2ff`.  The ledger rows it restates are nevertheless graded against the
*internal* declarations rather than against these, deliberately: a restatement
proved by handing hypotheses to an internal theorem is evidence about the
restatement, not about the theorem, and a row that cited only the façade would
certify the printed shape while saying nothing about what proves it.  What these
are for is reading — the printed quantification without reconstructing it from a
`variable` block.

`manuscriptSimpleEnvelopeFromLiteralEmbedding` is the exception and is genuinely
new: no declaration instantiated the generic residual lemmas at the literal `E`,
which is the group the printed proof now embeds.
-/

namespace GroupApproximation
namespace ManuscriptNonMF

/-! ## `INT.10`: LEF groups are MF -/

/-- **The introduction's "LEF groups are MF", with the printed quantification.**
Every countable group locally embeddable into finite groups is operator-MF.
`Sofic.LocallyFiniteMF` proves this with the group in a `variable` block; the
manuscript states it about groups, and the two are the same assertion. -/
theorem manuscriptLEFImpliesMF :
    ∀ (G : Type) [Group G] [Countable G], IsLEF G → IsOperatorMF G := by
  intro G _ _ hG
  exact isOperatorMF_of_isLEF hG

/-! ## `SO.15`: soficity passes to extensions with amenable quotient -/

/-- **"Soficity is preserved by every extension with amenable quotient."**  The
manuscript cites Elek--Szabó for this and uses it at the `ℤ`-extension
`W → ℤ`; the general statement is proved in
`Sofic.SoficByAmenablePermanence` by the Følner argument, with no countability
premise, no splitting hypothesis and no literature input. -/
theorem manuscriptSoficByAmenableExtension :
    ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal],
      IsSofic N → Amenability.IsAmenable (G ⧸ N) → IsSofic G := by
  intro G _ N _ hN hQ
  exact SoficByAmenablePermanence.isSofic_of_isSofic_of_isAmenable_quotient N hN hQ

/-! ## `SO.18`: the envelope paragraph, at the group the proof now embeds -/

/-- **The paragraph *A simple sofic envelope*, downstream of its Elek--Szabó
input, at the literal `E`.**  Let `S` be any countable simple group receiving
the manuscript's eight-generator group `E` injectively.  Then the MF residual of
`S` is all of `S` in both of the manuscript's presentations of it, every
homomorphism from `S` into an MF group is trivial, and `S` is not itself MF.

The hypothesis is a property of the *given* `S`, not an assumption that such an
`S` exists: producing one is the Elek--Szabó input the manuscript cites, graded
separately at `SO.17`, and nothing in this statement asserts it.

`Sofic.SimpleSoficEnvelope.simpleEnvelope_of_witnessEmbedding` is the same
conclusion from an embedding of the witness group `W`, which is what the
manuscript's proof used to embed.  The lemmas underneath are generic in the
source group, so moving to `E` costs only its two inputs, and both are in
`LiteralNonMFEndpoint.cliffordSign_blackHole`: the distinguished word is
invisible to every operator-norm matrix ultraproduct, and it is not the
identity. -/
theorem manuscriptSimpleEnvelopeFromLiteralEmbedding
    {S : Type} [Group S] [Countable S] [IsSimpleGroup S]
    (f : LiteralNonMFPresentation.MarkedGroup →* S) (hf : Function.Injective f) :
    coronaMFResidual S = ⊤ ∧ normMFResidual S = ⊤ ∧
      (∀ (H : Type) [Group H], IsOperatorMF H → ∀ (φ : S →* H) (s : S), φ s = 1) ∧
      ¬ IsOperatorMF S := by
  obtain ⟨hinv, hne⟩ := LiteralNonMFEndpoint.cliffordSign_blackHole
  have hnorm : normMFResidual S = ⊤ :=
    SimpleSoficEnvelope.normMFResidual_eq_top_of_simple_of_embedding f hf hinv hne
  have hcor : coronaMFResidual S = ⊤ := by
    rw [coronaMFResidual_eq_normMFResidual]
    exact hnorm
  refine ⟨hcor, hnorm, ?_,
    SimpleSoficEnvelope.not_isOperatorMF_of_coronaMFResidual_eq_top hcor⟩
  intro H _ hH φ s
  exact SimpleSoficEnvelope.map_eq_one_of_coronaMFResidual_eq_top hcor hH φ s

end ManuscriptNonMF
end GroupApproximation
