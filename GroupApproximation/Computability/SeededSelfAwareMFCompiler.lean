import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.OperatorMFFreeProductConsequences

/-!
# A seeded self-aware compiler for operator-MF

The proof-theoretic reverse-Kleene interface asks for a machine-indexed marked
presentation whose mark survives on halting inputs and belongs to the MF
radical on nonhalting inputs.  Once a single nontrivial MF-radical element is
known, those semantic clauses have a completely elementary seeded
realization.

For a marked group `(G, w)`, add one free infinite-cyclic generator `z`.  A
machine-indexed recursively enumerable presentation may enumerate the single
extra relation `z = 1` if the machine halts.  Thus the two endpoint groups are
`G` (halting) and `G * Z` (nonhalting).  The mark survives in both endpoints;
in the free-product endpoint its MF-invisibility is transported by the
canonical factor map.

This file formalizes exactly the group-theoretic endpoint package.  The
computability/Kleene argument is recorded in Cairn because the repository does
not yet bundle machine-indexed recursively enumerable marked presentations as
a Lean structure.

The construction is intentionally labelled *seeded*: it does not supply an
independent proof of the existence of non-MF groups.  It proves instead that
the bare reverse-Kleene compiler interface, unless it explicitly forbids an
existing MF-radical seed, is already satisfiable.
-/

namespace GroupApproximation
namespace SeededSelfAwareMFCompiler

open scoped Monoid.Coprod
open LiteralNonMFPresentation
open LiteralNonMFEndpoint
open LiteralNonMFLinearWitness

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Transport a marked MF-radical seed into the left factor of a free product.
The two conclusions are the only group-theoretic facts needed by the
nonhalting branch of the seeded toggle compiler. -/
theorem freeProduct_seed_transport {w : G}
    (hne : w ≠ 1) (hinvisible : NormMFInvisible w) :
    Monoid.Coprod.inl w ≠ (1 : G ∗ H) ∧
      NormMFInvisible (Monoid.Coprod.inl w : G ∗ H) := by
  constructor
  · intro h
    apply hne
    apply Monoid.Coprod.inl_injective
    simpa using h
  · exact hinvisible.map Monoid.Coprod.inl

/-- The nonhalting endpoint of the explicit seeded compiler. -/
abbrev NonhaltGroup : Type := MarkedGroup ∗ Multiplicative ℤ

/-- The original literal mark, carried into the nonhalting free-product
endpoint. -/
def nonhaltMark : NonhaltGroup := Monoid.Coprod.inl mark

/-- The nonhalting mark remains both nontrivial and MF-invisible. -/
theorem nonhaltMark_blackHole :
    nonhaltMark ≠ 1 ∧ NormMFInvisible nonhaltMark := by
  simpa [nonhaltMark] using
    freeProduct_seed_transport
      LiteralNonMFLinearWitness.literal_mark_ne_one
      literal_mark_normMFInvisible

/-- The nonhalting endpoint is itself finitely presented and non-MF.  This is
stronger than what the threshold-free reverse-Kleene/Higman wrapper needs. -/
theorem nonhaltGroup_finitelyPresented_not_isOperatorMF :
    Group.IsFinitelyPresented NonhaltGroup ∧
      ¬ IsOperatorMF NonhaltGroup := by
  exact ⟨inferInstance,
    not_isOperatorMF_coprod_left literal_not_isOperatorMF⟩

/-- Semantic endpoint package for the machine toggle: the halting endpoint is
`E`, while the nonhalting endpoint is `E * Z`.  The proposition `P e` may be
any machine-halting predicate.  No property of `P` is needed at this layer. -/
theorem literal_toggle_semantics (P : ℕ → Prop) :
    (∀ e, P e → mark ≠ 1) ∧
      (∀ e, ¬ P e →
        nonhaltMark ≠ 1 ∧ NormMFInvisible nonhaltMark) := by
  constructor
  · intro e he
    exact LiteralNonMFLinearWitness.literal_mark_ne_one
  · intro e he
    exact nonhaltMark_blackHole

/-- A constant-carrier version of the compiler semantics.  This records the
logical collapse even more starkly: the two HALT/NONHALT implications alone
are already satisfied by ignoring the machine index and returning one marked
MF-radical seed. -/
def HasConstantCarrierMFCompiler (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Group K) (w : ℕ → K),
    (∀ e, P e → w e ≠ 1) ∧
      (∀ e, ¬ P e → NormMFInvisible (w e))

/-- Every nontrivial MF-radical seed gives constant-carrier compiler semantics
for every predicate on machine indices. -/
theorem hasConstantCarrierMFCompiler_of_seed
    {K : Type u} [Group K] {w : K}
    (hne : w ≠ 1) (hinvisible : NormMFInvisible w)
    (P : ℕ → Prop) : HasConstantCarrierMFCompiler P := by
  refine ⟨K, inferInstance, fun _ ↦ w, ?_, ?_⟩
  · intro e he
    exact hne
  · intro e he
    exact hinvisible

/-- The explicit literal non-MF mark therefore supplies the abstract compiler
semantics for every machine predicate, unconditionally. -/
theorem literal_hasConstantCarrierMFCompiler (P : ℕ → Prop) :
    HasConstantCarrierMFCompiler P :=
  hasConstantCarrierMFCompiler_of_seed
    LiteralNonMFLinearWitness.literal_mark_ne_one
    literal_mark_normMFInvisible P

end SeededSelfAwareMFCompiler
end GroupApproximation
