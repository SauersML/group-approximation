import GroupApproximation.Algebra.ZariskiDescendingChain

/-!
# The Zariski envelope endpoint, with nothing to the left of the colon

`Criterion/ClosedEnvelopeCompressionCore.abstractEnvelopeCompressionBlind` is
the abstract half of `rem:chaincondition` in `non_mf_groups_exist.tex`: an order
isomorphism of a well-founded poset that moves a point weakly downward fixes it,
so a conjugation-equivariant monotone envelope with chain-condition values is
compression-blind.  It carries two premises that stand in for the geometry --- a
predicate `Closed` on subgroups, and `WellFoundedLT` on the closed subgroups ---
and the manuscript prints the conclusion for the Zariski closure without them.

`Algebra/ZariskiClosedSubgroup` and `Algebra/ZariskiDescendingChain` supply the
geometry: Zariski closedness for subgroups of `GL n k`, conjugation stability of
it, and the descending chain condition, all proved from the Hilbert basis
theorem and the ideal--variety pair.  What is missing between those two files and
the badge surface is a *statement in the shape the gate reads*.  This file adds
exactly that, and nothing else.

## What is here

Five closed-header endpoints, in increasing distance from the abstract theorem.

* `manuscriptZariskiChainCondition` --- the classical input itself, as a
  sentence about descending chains of Zariski closed subgroups of `GL n k`.
  This is the input `rem:chaincondition` names; it is a theorem, not a premise.
* `manuscriptZariskiEnvelopeData` --- the premises of the abstract theorem are
  *inhabited*, and this is the conjunct
  `ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind` cites to make
  the badged statement unconditional: there is a predicate
  `Closed`, conjugation stable and well founded, together with a monotone
  conjugation-equivariant `envelope` landing in it, whose value on a subgroup is
  the Zariski closure of that subgroup.  A single existential statement,
  discharging the whole conditional package at once.
* `manuscriptZariskiEnvelopeCompression` and
  `manuscriptZariskiClosureCompression` --- the abstract theorem *applied*: the
  envelope, respectively the Zariski closure, of a one-sided compression
  `tΓt⁻¹ ≤ Γ` agrees with that of `Γ`.
* `manuscriptZariskiRepresentationEnvelope` --- the displayed identity
  `closure of σ(tΓt⁻¹) = closure of σ(Γ)` at the level at which the manuscript
  prints it, for an arbitrary finite-dimensional representation `σ` of an
  arbitrary group.  This is the sentence a badge on `rem:chaincondition` should
  cite.

`manuscriptZariskiNoDescendingChain` is the negative form of the first, and is
the fifth.

Every one of them is stated with no declaration inputs: all quantifiers,
including the typeclass ones, occur inside the proposition, which is what
`scripts/check_non_mf_zero_input.py` inspects and what the rest of the badge
surface already does.

## What is not here

No new mathematics.  Each proof is one application of a theorem in
`Algebra/ZariskiDescendingChain` or in
`Criterion/ClosedEnvelopeCompressionCore`, after `intro`.  The content of this
file is the shape of the statements.

The dimension is presented as a `Fintype`-indexed matrix group, `GL n k` for
`k` a field; `ZariskiDescendingChain.wellFoundedLT_isZClosedSubgroupOfBasis`
transports the chain condition to `GL(V)` for an arbitrary `V` with a basis
indexed by `n`, so nothing is lost by working in coordinates.
-/

namespace GroupApproximation
namespace ZariskiEnvelopeEndpoint

open Matrix ZariskiClosedSubgroup

/-! ## The classical input, as a theorem -/

/-- **The descending chain condition for Zariski closed subgroups of `GL(V)`.**
This is the sentence `rem:chaincondition` calls classical: a descending chain of
Zariski closed subgroups of the general linear group over a field stabilises.

The proof is `Algebra/ZariskiDescendingChain.zariski_dcc_closedSubgroups`, which
reads the chain through the ideal of polynomial relations satisfied by the matrix
entries: that map is strictly order reversing on closed subgroups, and the ideals
of `k[X_{ij}]` satisfy the ascending chain condition by the Hilbert basis
theorem. -/
theorem manuscriptZariskiChainCondition :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      (C : ℕ → Subgroup (GeneralLinearGroup n k)),
      (∀ m, IsZClosedSubgroup (C m)) →
      (∀ m, C (m + 1) ≤ C m) →
      ∃ m, C (m + 1) = C m := by
  intro n _ _ k _ C hC hanti
  exact exists_succ_eq_of_antitone IsZClosedSubgroup C hC hanti

/-- **No infinite strictly descending chain of Zariski closed subgroups.**  The
negative form of the same statement, which is how a chain condition is usually
quoted. -/
theorem manuscriptZariskiNoDescendingChain :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      (C : ℕ → Subgroup (GeneralLinearGroup n k)),
      (∀ m, IsZClosedSubgroup (C m)) →
      ¬ ∀ m, C (m + 1) < C m := by
  intro n _ _ k _ C hC
  exact zariski_no_strict_descending_chain C hC

/-! ## The conditional package, inhabited -/

/-- **The premises of `manuscriptEnvelopeCompressionBlind` are satisfied.**
The abstract envelope theorem quantifies over a closedness predicate that is
conjugation stable and whose closed subgroups are well founded under `⊇`,
together with a monotone conjugation-equivariant envelope landing in it.  For
`GL n k` over a field, all of that exists, and the envelope it exists with is
the Zariski closure --- the invariant the manuscript names.

Reading the conjuncts in order: conjugation stability of closedness, the
descending chain condition, the envelope is closed, monotone, conjugation
equivariant, and equal to the Zariski closure on underlying sets. -/
theorem manuscriptZariskiEnvelopeData :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k],
      ∃ (Closed : Subgroup (GeneralLinearGroup n k) → Prop)
        (envelope : Subgroup (GeneralLinearGroup n k) → Subgroup (GeneralLinearGroup n k)),
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
              = zClosure (H : Set (GeneralLinearGroup n k)) := by
  intro n _ _ k _
  refine ⟨IsZClosedSubgroup, zEnvelope, fun g _ hH => isZClosedSubgroup_map_conj hH g,
    inferInstance, isZClosedSubgroup_zEnvelope, fun _ _ h => zEnvelope_mono h,
    zEnvelope_map_conj, zEnvelope_eq_zClosure⟩

/-! ## The abstract theorem, applied -/

/-- **Compression does not move the algebraic envelope.**  The abstract theorem
`ClosedEnvelopeCompression.abstractEnvelopeCompressionBlind`, applied to the
Zariski notion of closedness with its two premises discharged.

This is the first sentence of the envelope paragraph of `rem:chaincondition`,
with no literature input left: the descending chain condition it quotes is
`manuscriptZariskiChainCondition` above. -/
theorem manuscriptZariskiEnvelopeCompression :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      (Γ : Subgroup (GeneralLinearGroup n k)) (t : GeneralLinearGroup n k),
      Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
      zEnvelope (Γ.map (MulAut.conj t).toMonoidHom) = zEnvelope Γ := by
  intro n _ _ k _ Γ t ht
  exact ClosedEnvelopeCompression.abstractEnvelopeCompressionBlind
    IsZClosedSubgroup (fun g _ hH => isZClosedSubgroup_map_conj hH g)
    zEnvelope isZClosedSubgroup_zEnvelope (fun _ _ h => zEnvelope_mono h)
    zEnvelope_map_conj Γ t ht

/-- The same conclusion written on the Zariski closures themselves rather than
on the lattice-theoretic envelope.  `zEnvelope_eq_zClosure` identifies the two,
which is why the manuscript may say "closure" and the Lean statement may say
"envelope" without a gap between them. -/
theorem manuscriptZariskiClosureCompression :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      (Γ : Subgroup (GeneralLinearGroup n k)) (t : GeneralLinearGroup n k),
      Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
      zClosure ((Γ.map (MulAut.conj t).toMonoidHom : Subgroup (GeneralLinearGroup n k)) :
          Set (GeneralLinearGroup n k))
        = zClosure (Γ : Set (GeneralLinearGroup n k)) := by
  intro n _ _ k _ Γ t ht
  exact manuscriptZariskiClosureCompressionBlind ht

/-- **The manuscript's displayed identity.**  For a finite-dimensional
representation `σ` of an arbitrary group `H` over an arbitrary field, a subgroup
`Γ ≤ H` and a compressor `t` with `tΓt⁻¹ ≤ Γ`, the Zariski closures of
`σ(tΓt⁻¹)` and of `σ(Γ)` coincide.

This is
`\overline{\sigma(t\Gamma t^{-1})}^{\,Z}=\overline{\sigma(\Gamma)}^{\,Z}`
of `rem:chaincondition`, unconditionally. -/
theorem manuscriptZariskiRepresentationEnvelope :
    ∀ {n : Type} [Fintype n] [DecidableEq n] {k : Type} [Field k]
      {H : Type} [Group H] (σ : H →* GeneralLinearGroup n k) (Γ : Subgroup H) (t : H),
      Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
      zClosure ((((Γ.map (MulAut.conj t).toMonoidHom).map σ) :
          Subgroup (GeneralLinearGroup n k)) : Set (GeneralLinearGroup n k))
        = zClosure ((Γ.map σ : Subgroup (GeneralLinearGroup n k)) :
          Set (GeneralLinearGroup n k)) := by
  intro n _ _ k _ H _ σ Γ t ht
  exact ZariskiClosedSubgroup.manuscriptZariskiClosureOfRepresentation σ Γ t ht

end ZariskiEnvelopeEndpoint
end GroupApproximation
