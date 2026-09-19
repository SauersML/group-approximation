import GroupApproximation.Sofic.CentralizerNormalizationRefuted
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.KunThomShulmanDoubleConstruction
import GroupApproximation.Sofic.SymmetricDoubleCovering

/-!
# Nothing in the double-construction interface can be removed

`KunThomShulmanDoubleData` has six fields.  Four of them are proved here from
`¬ Γ.Normal` alone (`Sofic/InfranormalCompressionPair`, and `ofNotNormal`), and
`not_normal_of_data` proves the converse, so those four are *exactly*
non-normality and carry nothing extra.  This file settles the other two, and the
answer for both is the same: **they are not lemmas.  They are false.**

* `centralizerNormalization` is refuted in `Sofic/CentralizerNormalizationRefuted`
  by the reflection subgroup of the dihedral group of order six.
* `operatorMF` is refuted here.  Over `Γ = ⊤` the double collapses,
  `G *_⊤ G ≅ G`, so the double of a non-MF group is a non-MF double — and this
  repository's own headline theorem produces a finitely presented non-MF group.

Consequently there is no assumption left to delete.  Every hypothesis of the
construction is either *proved* or *provably necessary*, and the construction
also carries an endpoint with no hypothesis at all beyond the two
group-theoretic words of the Kun--Thom pair
(`DoubleFdRigidity.symmetricDouble_no_faithful_fdRep`).

## The boundary, stated precisely

Refuting a statement about *arbitrary* pairs is not the same as refuting it
about the pairs the construction is run on, and this file does not confuse the
two.

* the centralizer counterexample has a *finite* peripheral subgroup, and
  `isInfranormal_iff_normal_of_finite` shows no finite peripheral subgroup can
  belong to a compression pair;
* the MF counterexample has `Γ = ⊤`, and `IsCompressionPair.ne_top` shows no
  compression pair has `Γ = ⊤`.

So neither refutation touches the Kun--Thom/Shulman hypotheses.  What each shows
is that the corresponding field of the interface quantifies over pairs where it
fails, hence cannot be replaced by a proof.  Inside the residually finite class
the MF field is exactly Shulman's amalgamation theorem, a C\*-algebra statement
about `A *_C A`; that is where the mathematics lives, not in this interface.
-/

namespace GroupApproximation

namespace KunThomShulmanDouble

/-! ## The double over the whole group -/

/-- Over the whole group as peripheral subgroup the double collapses: there is
nothing to amalgamate. -/
def symmetricDoubleTopEquiv (G : Type) [Group G] :
    SymmetricDouble G (⊤ : Subgroup G) ≃* G :=
  (symmetricDoubleEquivIteratedBool G (⊤ : Subgroup G)).trans
    (iteratedTopEquiv G Bool false)

theorem not_isOperatorMF_symmetricDouble_top {G : Type} [Group G]
    (h : ¬ IsOperatorMF G) :
    ¬ IsOperatorMF (SymmetricDouble G (⊤ : Subgroup G)) :=
  fun hd ↦ h (CommensurabilityInvariance.isOperatorMF_of_mulEquiv
    (symmetricDoubleTopEquiv G) hd)

/-! ## The MF field is not dischargeable -/

/-- **There is a pair whose symmetric double is not operator-MF.**  So the
`operatorMF` field of the datum is a genuine hypothesis about the pair, not a
theorem awaiting a proof. -/
theorem exists_not_isOperatorMF_symmetricDouble :
    ∃ (G : Type) (_ : Group G) (Γ : Subgroup G),
      ¬ IsOperatorMF (SymmetricDouble G Γ) := by
  obtain ⟨E, groupE, _hfp, hE⟩ :=
    ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF
  exact ⟨E, groupE, ⊤, @not_isOperatorMF_symmetricDouble_top E groupE hE⟩

theorem not_forall_isOperatorMF_symmetricDouble :
    ¬ (∀ (G : Type) [Group G] (Γ : Subgroup G),
      IsOperatorMF (SymmetricDouble G Γ)) := by
  intro hall
  obtain ⟨G, groupG, Γ, hΓ⟩ := exists_not_isOperatorMF_symmetricDouble
  exact hΓ (@hall G groupG Γ)

/-! ## Minimality of the interface -/

/-- **The interface is minimal: nothing in it can be deleted.**

1. The four combinatorial fields are *exactly* `¬ Γ.Normal`: they exist for a
   pair if and only if the peripheral subgroup fails to be normal, so they add
   nothing and lose nothing.
2. The centralizer field is false for some pair, so it cannot be replaced by a
   proof.
3. The MF field is false for some pair, so it cannot be replaced by a proof
   either.

Together with `DoubleFdRigidity.symmetricDouble_no_faithful_fdRep` — an endpoint
of the same construction that assumes neither field — this is the complete
account of what the double construction does and does not need. -/
theorem doubleData_interface_minimal :
    (∀ (G : Type) [Group G] (Γ : Subgroup G),
        Nonempty (EscapeWitness Γ) ↔ ¬ Γ.Normal) ∧
      (∃ (G : Type) (_ : Group G) (Γ : Subgroup G),
        ¬ HasSoficCentralizerNormalization Γ) ∧
      (∃ (G : Type) (_ : Group G) (Γ : Subgroup G),
        ¬ IsOperatorMF (SymmetricDouble G Γ)) :=
  ⟨fun _ _ _ ↦ nonempty_escapeWitness_iff,
    exists_not_hasSoficCentralizerNormalization,
    exists_not_isOperatorMF_symmetricDouble⟩

/-- The refuting pair for the MF field is not a compression pair either: its
peripheral subgroup is the whole group. -/
theorem top_not_isCompressionPair (G : Type) [Group G] :
    ¬ IsCompressionPair (⊤ : Subgroup G) :=
  fun h ↦ h.ne_top rfl

end KunThomShulmanDouble

end GroupApproximation
