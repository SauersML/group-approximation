import GroupApproximation.Criterion.ClosedEnvelopeCompressionCore
import GroupApproximation.Algebra.ZariskiEnvelopeEndpoint

/-!
# Compression cannot shrink a chain-condition envelope

`rem:chaincondition` of `non_mf_groups_exist.tex` prints two things, and the
badge on this module has to carry both.

1. **The abstract principle.**  "A conjugation-equivariant monotone invariant
   whose values satisfy the ascending or descending chain condition takes the
   same value on `Γ` as on `tΓt⁻¹`, because an order isomorphism of such a
   poset fixes every point it moves weakly upward."  That is
   `ClosedEnvelopeCompressionCore.envelope_conj_eq`, and it needs nothing about
   algebraic geometry.
2. **The third of the three named instances.**  "The Zariski closures of
   `σ(Γ)` and `σ(tΓt⁻¹)` coincide, the descending chain condition for
   Zariski-closed subgroups of `GL(V)` coming from the Hilbert basis theorem."
   That is a statement about a *particular* closedness predicate, and the
   manuscript prints it with no hypothesis.

Until now the badged declaration stated only (1), with the geometry entering as
the quantified premises `(Closed : Subgroup G → Prop)` and
`[WellFoundedLT {H // Closed H}]`.  Those premises are what
`scripts/check_non_mf_unconditional.py` reported: a reader of the badge alone
could not tell that the corpus proves the chain condition rather than assuming
it.  It does prove it --- `Algebra/ZariskiDescendingChain` builds the Zariski
topology on `GL n k` over an arbitrary field and derives
`wellFoundedLT_isZClosedSubgroup` from the Hilbert basis theorem, and
`Algebra/ZariskiEnvelopeEndpoint` exhibits the entire premise package at it ---
so the repair is to say so in the badged statement.

`manuscriptEnvelopeCompressionBlind` below therefore has three conjuncts: the
abstract principle, the *inhabitation* of its premises by Zariski closedness
(which is the direct answer to "the corpus exhibits no `Closed` for which the
instance holds"), and the displayed identity
`closure of σ(tΓt⁻¹) = closure of σ(Γ)` for an arbitrary finite-dimensional
representation of an arbitrary group.  Nothing is quoted anywhere in the chain.

The abstract half now lives one module up, in
`Criterion/ClosedEnvelopeCompressionCore`, under the same namespace, because
`Algebra/ZariskiDescendingChain` consumes it and this file consumes
`Algebra/ZariskiEnvelopeEndpoint`.  Callers of `envelope_conj_eq`,
`conj_eq_of_conj_le` and `conjClosedIso` are unaffected: the names did not
change, only the file they are declared in.
-/

namespace GroupApproximation
namespace ClosedEnvelopeCompression

open Matrix ZariskiClosedSubgroup

/-- **The manuscript's envelope remark, in the form it is printed.**

The conjuncts follow the printed sentences:

* the abstract principle --- a conjugation-equivariant monotone envelope
  landing in a class of subgroups with the descending chain condition is blind
  to one-sided compression;
* that class of subgroups exists, for `GL(V)` over an arbitrary field, and the
  envelope it exists with is the Zariski closure: the premises of the first
  conjunct are inhabited, not assumed;
* hence the displayed identity
  `\overline{\sigma(t\Gamma t^{-1})}^{Z} = \overline{\sigma(\Gamma)}^{Z}`
  for an arbitrary representation `σ` of an arbitrary group, with no
  hypothesis.

The second conjunct is what makes the third unconditional, and it is what a
reader of the first conjunct alone cannot see.  Its own proof rests on the
Hilbert basis theorem, exactly as the manuscript says. -/
theorem manuscriptEnvelopeCompressionBlind :
    (∀ {G : Type} [Group G] (Closed : Subgroup G → Prop),
      (∀ (g : G) (H : Subgroup G), Closed H →
          Closed (H.map (MulAut.conj g).toMonoidHom)) →
        ∀ [WellFoundedLT {H : Subgroup G // Closed H}]
          (envelope : Subgroup G → Subgroup G),
          (∀ H, Closed (envelope H)) → Monotone envelope →
          (∀ (g : G) (H : Subgroup G),
            envelope (H.map (MulAut.conj g).toMonoidHom) =
              (envelope H).map (MulAut.conj g).toMonoidHom) →
          ∀ (Γ : Subgroup G) (t : G),
            Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
            envelope (Γ.map (MulAut.conj t).toMonoidHom) = envelope Γ) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k],
      ∃ (Closed : Subgroup (GeneralLinearGroup n k) → Prop)
        (envelope : Subgroup (GeneralLinearGroup n k) →
          Subgroup (GeneralLinearGroup n k)),
        (∀ (g : GeneralLinearGroup n k) (H : Subgroup (GeneralLinearGroup n k)),
            Closed H → Closed (H.map (MulAut.conj g).toMonoidHom)) ∧
          WellFoundedLT {H : Subgroup (GeneralLinearGroup n k) // Closed H} ∧
          (∀ H, Closed (envelope H)) ∧
          Monotone envelope ∧
          (∀ (g : GeneralLinearGroup n k) (H : Subgroup (GeneralLinearGroup n k)),
            envelope (H.map (MulAut.conj g).toMonoidHom)
              = (envelope H).map (MulAut.conj g).toMonoidHom) ∧
          ∀ H : Subgroup (GeneralLinearGroup n k),
            (envelope H : Set (GeneralLinearGroup n k))
              = zClosure (H : Set (GeneralLinearGroup n k))) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      {H : Type} [Group H] (σ : H →* GeneralLinearGroup n k) (Γ : Subgroup H)
      (t : H),
      Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
      zClosure ((((Γ.map (MulAut.conj t).toMonoidHom).map σ) :
          Subgroup (GeneralLinearGroup n k)) : Set (GeneralLinearGroup n k))
        = zClosure ((Γ.map σ : Subgroup (GeneralLinearGroup n k)) :
          Set (GeneralLinearGroup n k))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact abstractEnvelopeCompressionBlind
  · intro n _ _ k _
    exact ZariskiEnvelopeEndpoint.manuscriptZariskiEnvelopeData
  · intro n _ _ k _ H _ σ Γ t ht
    exact ZariskiEnvelopeEndpoint.manuscriptZariskiRepresentationEnvelope σ Γ t ht

end ClosedEnvelopeCompression
end GroupApproximation
