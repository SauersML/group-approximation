import GroupApproximation.Analysis.McDuffTensorHyperfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# McDuff model faithfulness: the Pauli model `𝓡` absorbs itself

Lane `sk-rows-09` (faithfulness audit of `McDuff.IsMcDuffFactor`, `Analysis/McDuffFactor.lean:38`) for
`simple_kazhdan_sofic_group.tex`, tex 350–355 (census row `5b15f5d8faae`):

> "Then $G$ lies in the unitary group of the McDuff factor $L(G)\mathbin{\bar\otimes}\mathcal R$
> \cite{McDuff}, which embeds in $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq
> (\mathcal R\mathbin{\bar\otimes}\mathcal R)^\omega\cong\mathcal R^\omega$, as in Brown's question."

The corpus definition `IsMcDuffFactor M` asks for a II₁ factor `M` with `M ≅ M ⊗̄ 𝓡`, where `𝓡` is the
Pauli model `Hyperfinite.hyperfiniteFactor = L_β(Γ)` (`Γ` the Pauli group, `β` its sign cocycle) and
`M ⊗̄ 𝓡 = McDuff.tensorHyperfinite M`.  A faithful model of the hyperfinite II₁ factor must itself be
McDuff, and in particular satisfy the ingredient `𝓡 ⊗̄ 𝓡 ≅ 𝓡` used at tex 354.  This module proves it.

## Route

* II₁: `Hyperfinite.isIIOneFactor_hyperfiniteFactor` (already in the corpus).
* `𝓡 ⊗̄ 𝓡 = twistedTensor (L_β(Γ)) β`.  The curry unitary carries it onto `L_{β⊕β}(Γ × Γ)`
  (`TwistedProduct.curryConj_image_twistedTensor`).
* The interleaving `Hyperfinite.pauliInterleave : Γ × Γ ≃* Γ` (even and odd sites, the bijection
  `ℕ ⊕ ℕ ≃ ℕ` of the lane note) carries `β ⊕ β` to `β` (`pauliCocycle_pauliInterleave`, from
  `Hyperfinite.pauliCocycle_interleave`), so reindexing carries `L_{β⊕β}(Γ × Γ)` onto `L_β(Γ)`
  (`SpatialIso.conj_image_twistedVonNeumannAlgebra_of_mulEquiv`).
* Both links are spatial, so they restrict to ⋆-algebra isomorphisms (`SpatialIso.restrictConj`).

Endpoints: `manuscriptSentence_hyperfiniteAbsorbsHyperfinite` (`𝓡 ≅ 𝓡 ⊗̄ 𝓡`) and
`manuscriptSentence_hyperfiniteIsMcDuff` (`IsMcDuffFactor 𝓡`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity

open TwistedGroupVonNeumann TwistedTensor TwistedProduct SpatialIso

noncomputable section

/-- **The interleaving carries the product cocycle `β ⊕ β` to `β`**, in the form required by
`conj_image_twistedVonNeumannAlgebra_of_mulEquiv`. -/
theorem pauliCocycle_pauliInterleave (x y : Hyperfinite.PauliGroup × Hyperfinite.PauliGroup) :
    Hyperfinite.pauliCocycle (Hyperfinite.pauliInterleave x) (Hyperfinite.pauliInterleave y) =
      prodCocycle Hyperfinite.pauliCocycle Hyperfinite.pauliCocycle x y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  exact Hyperfinite.pauliCocycle_interleave a b c d

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity.pauliCocycle_pauliInterleave

/-- **`𝓡 ≅ 𝓡 ⊗̄ 𝓡`** for the Pauli model `𝓡 = L_β(Γ)`, as a composite of two spatial isomorphisms:
`L_β(Γ) ≅ L_{β⊕β}(Γ × Γ)` by interleaving and `L_{β⊕β}(Γ × Γ) ≅ L_β(Γ) ⊗̄ L_β(Γ)` by currying. -/
def pauliSelfAbsorbs :
    ↥(twistedVonNeumannAlgebra Hyperfinite.pauliCocycle).toStarSubalgebra ≃⋆ₐ[ℂ]
      ↥(twistedTensor (twistedVonNeumannAlgebra Hyperfinite.pauliCocycle)
        Hyperfinite.pauliCocycle).toStarSubalgebra := by
  have h3 := curryConj_image_twistedTensor Hyperfinite.pauliCocycle Hyperfinite.pauliCocycle
    Hyperfinite.pauliCocycle_isSignCocycle Hyperfinite.pauliCocycle_isSignCocycle
  have h4 := conj_image_twistedVonNeumannAlgebra_of_mulEquiv Hyperfinite.pauliInterleave
    (prodCocycle Hyperfinite.pauliCocycle Hyperfinite.pauliCocycle) Hyperfinite.pauliCocycle
    pauliCocycle_pauliInterleave
  exact (restrictConj _ h4).symm.trans (restrictConj curryLp h3).symm

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity.pauliSelfAbsorbs

/-- **`𝓡 ⊗̄ 𝓡 ≅ 𝓡`** (tex 354 ingredient): the Pauli model of the hyperfinite II₁ factor is
isomorphic, as a unital ⋆-algebra, to its own tensor product with `𝓡` in the sense of
`McDuff.tensorHyperfinite`. -/
theorem manuscriptSentence_hyperfiniteAbsorbsHyperfinite :
    Nonempty (↥Hyperfinite.hyperfiniteFactor.toStarSubalgebra ≃⋆ₐ[ℂ]
      ↥(McDuff.tensorHyperfinite Hyperfinite.hyperfiniteFactor).toStarSubalgebra) := by
  show Nonempty (↥(twistedVonNeumannAlgebra Hyperfinite.pauliCocycle).toStarSubalgebra ≃⋆ₐ[ℂ]
      ↥(twistedTensor (twistedVonNeumannAlgebra Hyperfinite.pauliCocycle)
        Hyperfinite.pauliCocycle).toStarSubalgebra)
  exact ⟨pauliSelfAbsorbs⟩

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity.manuscriptSentence_hyperfiniteAbsorbsHyperfinite

/-- **The Pauli model `𝓡` is a McDuff factor** in the corpus sense `McDuff.IsMcDuffFactor`: a II₁ factor
with `𝓡 ≅ 𝓡 ⊗̄ 𝓡`.  So `IsMcDuffFactor` is satisfied by the hyperfinite II₁ factor itself, as McDuff's
notion requires. -/
theorem manuscriptSentence_hyperfiniteIsMcDuff :
    McDuff.IsMcDuffFactor Hyperfinite.hyperfiniteFactor :=
  ⟨Hyperfinite.isIIOneFactor_hyperfiniteFactor, manuscriptSentence_hyperfiniteAbsorbsHyperfinite⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity.manuscriptSentence_hyperfiniteIsMcDuff

end

end GroupApproximation.SimpleKazhdanSofic.SkRows.McDuffSanity
