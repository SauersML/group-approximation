import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# LEF faithfulness: the corpus `IsLEF` is Vershik–Gordon local embeddability

`simple_kazhdan_sofic_group.tex`, section `sec:intro` (tex l.102–104):

> A group is LEF~\cite{VershikGordon} if each finite subset $\Phi$ maps
> injectively into a finite group by a map that preserves every product $gh$
> with $g,h,gh\in\Phi$.

The corpus predicate `GroupApproximation.IsLEF` (`Sofic/LEF.lean`) asks for a globally defined
map into a symmetric group `Perm (Fin n)`, normalized at `1` and multiplicative on *all* pairs
of the test set.  This module checks that it is exactly the printed definition, with an
arbitrary finite group `Q : Type` as target and multiplicativity required only when the product
stays in the test set.

## Route

* `isTextbookLEF_iff_isLocallyEmbeddable`: the corpus textbook form `IsTextbookLEF` bundles the
  finite target as a `FiniteGroupModel` (carrier, group, `Fintype`, `DecidableEq`).  Unbundle it
  to `(Q : Type) (_ : Group Q) (_ : Finite Q)`; conversely `Fintype.ofFinite` and
  `Classical.decEq` rebuild the model.
* `isLEF_iff_localEmbedding`: compose with the corpus equivalence `isLEF_iff_textbook`
  (Cayley embedding of the finite target, after enlarging the test set by `1` and the pairwise
  products).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.LEFFaithful

open GroupApproximation

universe u

/-- **Vershik–Gordon local embeddability, as printed** (tex l.102–104): every finite subset `F`
maps injectively into a finite group by a map preserving every product `g h` with
`g, h, g h ∈ F`. -/
def IsLocallyEmbeddable (G : Type u) [Group G] : Prop :=
  ∀ F : Finset G, ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (φ : G → Q),
    Set.InjOn φ (F : Set G) ∧ ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → φ (g * h) = φ g * φ h

/-- The bundled textbook form `IsTextbookLEF` is the unbundled printed form. -/
theorem isTextbookLEF_iff_isLocallyEmbeddable (G : Type u) [Group G] :
    IsTextbookLEF G ↔ IsLocallyEmbeddable G := by
  constructor
  · intro h F
    obtain ⟨M, φ, hinj, hmul⟩ := h F
    exact ⟨M.groupCarrier, M.group, @Finite.of_fintype M.groupCarrier M.fintype, φ, hinj, hmul⟩
  · intro h F
    obtain ⟨Q, hQ, hfin, φ, hinj, hmul⟩ := h F
    let M : FiniteGroupModel :=
      { groupCarrier := Q
        group := hQ
        fintype := @Fintype.ofFinite Q hfin
        decidableEq := Classical.decEq Q }
    exact ⟨M, φ, hinj, hmul⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LEFFaithful.isTextbookLEF_iff_isLocallyEmbeddable

/-- **LEF faithfulness** (tex l.102–104): the corpus `IsLEF` (permutation targets, global maps,
multiplicative on all pairs) is Vershik–Gordon local embeddability into finite groups. -/
theorem isLEF_iff_localEmbedding (G : Type u) [Group G] :
    IsLEF G ↔ ∀ F : Finset G, ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (φ : G → Q),
      Set.InjOn φ (F : Set G) ∧ ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → φ (g * h) = φ g * φ h :=
  (isLEF_iff_textbook G).trans (isTextbookLEF_iff_isLocallyEmbeddable G)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LEFFaithful.isLEF_iff_localEmbedding

/-- **Endpoint** (tex l.102–104): the repository definition of LEF is the printed one. -/
theorem manuscriptSentence_lefDefinitionVershikGordon (G : Type u) [Group G] :
    IsLEF G ↔ IsLocallyEmbeddable G :=
  isLEF_iff_localEmbedding G

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LEFFaithful.manuscriptSentence_lefDefinitionVershikGordon

end GroupApproximation.SimpleKazhdanSofic.SkRows.LEFFaithful
