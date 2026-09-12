import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.OperatorMFFreeProductConsequences
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

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
computability/Kleene implementation remains recorded in Cairn because the
repository does not yet bundle machine-indexed recursively enumerable marked
presentations as a Lean structure.  The fixed-point contradiction itself, the
seed/compiler logical equivalence, prime-coded carriers, and the monotone
same-mark quotient obstruction are formalized below.

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
    exact Monoid.Coprod.inl_injective (N := H) (by simpa using h)
  · exact hinvisible.map (Monoid.Coprod.inl : G →* G ∗ H)

/-- The nonhalting endpoint of the explicit seeded compiler. -/
abbrev NonhaltGroup : Type := MarkedGroup ∗ Multiplicative ℤ

/-- The original literal mark, carried into the nonhalting free-product
endpoint. -/
noncomputable def nonhaltMark : NonhaltGroup := Monoid.Coprod.inl mark

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
    {K : Type} [Group K] {w : K}
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

/-! ## Literal self-reference and the seed/compiler equivalence -/

/-- The proposition-level core of the reverse-Kleene argument.  `halts ↔
trivial` is the self-aware proof-search program: it halts exactly when it finds
a proof that its marked word is trivial.  The HALT survival clause rules that
out, and the NONHALT clause then supplies invisibility. -/
theorem reverseKleene_fixedPoint_logic
    {halts trivial invisible : Prop}
    (hself : halts ↔ trivial)
    (hhalt : halts → ¬ trivial)
    (hnonhalt : ¬ halts → invisible) :
    ¬ halts ∧ ¬ trivial ∧ invisible := by
  have hnh : ¬ halts := by
    intro hh
    exact hhalt hh (hself.mp hh)
  exact ⟨hnh, fun ht ↦ hnh (hself.mpr ht), hnonhalt hnh⟩

/-- A marked MF-radical seed, with no computability structure attached. -/
def HasMarkedMFSeed : Prop :=
  ∃ (K : Type) (_ : Group K) (w : K),
    w ≠ 1 ∧ NormMFInvisible w

/-- The logical endpoint of a self-aware marked compiler.  The computable
compiler and recursion-theorem machinery produce exactly such a fixed point;
this structure deliberately records only the semantic data checked here. -/
def HasLogicalSelfAwareMFCompiler : Prop :=
  ∃ (K : Type) (_ : Group K) (w : K) (halts : Prop),
    (halts ↔ w = 1) ∧
      (halts → w ≠ 1) ∧
      (¬ halts → NormMFInvisible w)

/-- One marked MF-radical seed gives a self-aware compiler endpoint: choose a
fixed point which never halts. -/
theorem hasLogicalSelfAwareMFCompiler_of_seed :
    HasMarkedMFSeed → HasLogicalSelfAwareMFCompiler := by
  rintro ⟨K, hK, w, hne, hinvisible⟩
  letI : Group K := hK
  refine ⟨K, inferInstance, w, False, ?_, ?_, ?_⟩
  · simp [hne]
  · simp
  · intro _
    exact hinvisible

/-- Reverse Kleene extracts a nontrivial invisible word from the logical
self-aware endpoint. -/
theorem seed_of_hasLogicalSelfAwareMFCompiler :
    HasLogicalSelfAwareMFCompiler → HasMarkedMFSeed := by
  rintro ⟨K, hK, w, halts, hself, hhalt, hnonhalt⟩
  letI : Group K := hK
  obtain ⟨_, hne, hinvisible⟩ :=
    reverseKleene_fixedPoint_logic hself hhalt hnonhalt
  exact ⟨K, inferInstance, w, hne, hinvisible⟩

/-- The bare self-aware MF compiler endpoint is logically equivalent to
already possessing one marked MF-radical seed. -/
theorem logicalSelfAwareMFCompiler_iff_seed :
    HasLogicalSelfAwareMFCompiler ↔ HasMarkedMFSeed :=
  ⟨seed_of_hasLogicalSelfAwareMFCompiler,
    hasLogicalSelfAwareMFCompiler_of_seed⟩

/-- The literal eight-generator group supplies a closed marked MF-radical
seed.  Unlike `hasLogicalSelfAwareMFCompiler_of_seed`, this declaration has
no caller-supplied construction datum: both survival and invisibility are
theorems about the literal presentation. -/
theorem literal_hasMarkedMFSeed : HasMarkedMFSeed :=
  ⟨MarkedGroup, inferInstance, mark,
    LiteralNonMFLinearWitness.literal_mark_ne_one,
    literal_mark_normMFInvisible⟩

/-- Closed semantic self-awareness endpoint obtained from the literal seed.

This is deliberately the *logical* endpoint.  It does not claim that Lean has
internalized Turing-machine codes, r.e. presentation enumerators, or Kleene's
recursion theorem. -/
theorem literal_hasLogicalSelfAwareMFCompiler :
    HasLogicalSelfAwareMFCompiler :=
  hasLogicalSelfAwareMFCompiler_of_seed literal_hasMarkedMFSeed

/-! ## Prime-coded finite presentations -/

/-- A carrier which records the compiler index in the order of a finite
cyclic free factor.  The external computability layer instantiates
`primeCode e` with the `(e+1)`-st prime; the group-theoretic transport below
works for every code function. -/
abbrev PrimeCodedGroup (K : Type u) [Group K]
    (primeCode : ℕ → ℕ) (e : ℕ) : Type u :=
  K ∗ Multiplicative (ZMod (primeCode e))

/-- The seed mark in the prime-coded carrier. -/
def primeCodedMark (K : Type u) [Group K]
    (primeCode : ℕ → ℕ) (e : ℕ) (w : K) :
    PrimeCodedGroup K primeCode e := Monoid.Coprod.inl w

/-- Prime coding does not change survival or MF-invisibility of the seed. -/
theorem primeCodedMark_blackHole {K : Type u} [Group K] {w : K}
    (hne : w ≠ 1) (hinvisible : NormMFInvisible w)
    (primeCode : ℕ → ℕ) (e : ℕ) :
    primeCodedMark K primeCode e w ≠ 1 ∧
      NormMFInvisible (primeCodedMark K primeCode e w) := by
  simpa [primeCodedMark] using
    (freeProduct_seed_transport (H := Multiplicative (ZMod (primeCode e)))
      hne hinvisible)

/-- The prime-coded carrier is finitely presented whenever the seed carrier
is. -/
theorem primeCodedGroup_finitelyPresented {K : Type u} [Group K]
    [Group.IsFinitelyPresented K] (primeCode : ℕ → ℕ) (e : ℕ)
    (hprime : Nat.Prime (primeCode e)) :
    Group.IsFinitelyPresented (PrimeCodedGroup K primeCode e) := by
  letI : NeZero (primeCode e) := ⟨hprime.ne_zero⟩
  infer_instance

/-! ## The monotone same-mark obstruction -/

/-- If an MF-invisible mark survives a quotient, the quotient is not
operator-MF.  This is the formal same-mark no-go for compilers whose HALT
branch is obtained only by appending relators. -/
theorem quotient_not_isOperatorMF_of_invisible_mark_survives
    {K : Type u} {L : Type v} [Group K] [Group L] [Countable L]
    {w : K} (hinvisible : NormMFInvisible w) (q : K →* L)
    (hsurvives : q w ≠ 1) :
    ¬ IsOperatorMF L := by
  intro hMF
  have hmem : q w ∈ normMFResidual L := hinvisible.map q
  rw [normMFResidual_eq_bot_of_isOperatorMF hMF] at hmem
  exact hsurvives (Subgroup.mem_bot.mp hmem)

end SeededSelfAwareMFCompiler
end GroupApproximation
