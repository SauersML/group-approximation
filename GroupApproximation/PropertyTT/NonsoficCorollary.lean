import GroupApproximation.Endpoint.MainResults
import GroupApproximation.PropertyTT.PaperStatements

/-!
# A nonsofic group with property `(TT)/T`

This file intentionally sits outside the dependency closure of the rigidity
theorems.  It combines the `(TT)/T` endpoint proved in this development with the
nonsoficity theorem for the same elementary group.  The conjunction below is
only a corollary.

The nonsoficity input is `Endpoint.MainResults.universalLeavittEL4_not_isSofic`,
and the credit for its mechanism is threefold: the expander decomposition of a
sofic approximation of a property-`(T)` group is Kun (arXiv:1606.04471, 2016);
the expander-centralizer theorem that turns a *single* expanding component into
an LEF conclusion is Kun--Thom (arXiv:1901.03963, 2019); and the step between
them --- selecting one component from Kun's union, which is what the
compression setup is for --- is the contribution of the prior OpenAI work.
Both external theorems are *proved* in this development
(`Kun/KunDecomposition`, `KunThom/KunThomTheorem`) rather than assumed, so none
of the three is a literature input here; the attribution is about who the
mathematics belongs to, not about what is trusted.
-/

namespace GroupApproximation
namespace PropertyTTPaper

universe v

/-- For every `n ≥ 2`, the elementary group over the binary Leavitt algebra
over `F₂` has property `(TT)/T` and is nonsofic.

The `(TT)/T` assertion is the rigidity result of this development.  The
nonsoficity assertion is imported from the prior nonsofic-group theorem and is
not claimed here as a new proof or mechanism. -/
theorem binaryLeavitt_elementaryGroup_hasTTmodT_and_not_isSofic
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, v}
        (elementaryGroup (Fin n) BinaryL) ∧
      ¬ IsSofic (elementaryGroup (Fin n) BinaryL) := by
  refine ⟨binaryLeavitt_elementaryGroup_hasTTmodT n hn, ?_⟩
  intro hsofic
  exact binaryLeavittUnits_not_isSofic (ZMod 2)
    ((isSofic_mulEquiv_iff
      (binaryLeavitt_elementaryEquivUnits n hn)).mp hsofic)

end PropertyTTPaper
end GroupApproximation
