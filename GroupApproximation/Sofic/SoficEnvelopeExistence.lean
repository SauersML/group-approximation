import GroupApproximation.Sofic.SoficUltraproduct
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Covers.TableCover
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Set.Countable

/-!
# Towards Elek--Szabó: countable simple sofic envelopes

The manuscript's paragraph *A simple sofic envelope* cites Elek--Szabó for

> every countable sofic group embeds in a countable simple sofic group

In `non_mf_groups_exist.tex` the paragraph is located by its stable anchors --
the file is under concurrent edit and no offset survives: the
heading `\paragraph{A simple sofic envelope.}` and the citation key
`ElekSzaboHyper`, Theorem 1.  That key is *not* the one on the Elek--Szabó
amenable-extension theorem used elsewhere in the same section, which is
`ElekSzabo` and is a different result.

Everything after the citation is proved in
`GroupApproximation.Sofic.SimpleSoficEnvelope`.  This file develops the cited
existence statement itself.

## The classical proof and what is done here

The standard argument has three moves.

1. **Ambient group.**  A countable sofic group embeds into a metric
   ultraproduct `∏_𝒰 Sym(X_i) / (null)` of finite symmetric groups, and
   conversely every subgroup of such an ultraproduct is sofic.  This is the
   `UniversalSofic` development of `Sofic.SoficUltraproduct`.  Both directions
   are assembled below, with the extra bookkeeping the second one needs: the
   models must all be nonempty, which a shift of the approximation index
   arranges (`shiftApproximation`, `exists_positive_soficApproximation`).
   The ambient group is itself sofic (`isSofic_universalSofic`).

2. **Simplicity of the ambient group.**  When the model cardinalities diverge
   along `𝒰`, the metric ultraproduct is a simple group.  This is the
   combinatorial heart of Elek--Szabó.  It is **not proved here**; it is
   developed in `GroupApproximation.Sofic.SoficEnvelopeSimplicity`, down to one
   finite statement about symmetric groups which that module carries as an
   explicit premise.  See the section *What is missing* below.

3. **Descent to a countable subgroup.**  Inside a simple group, a countable
   subset can be enlarged to a countable *simple* subgroup, by closing up
   under conjugators realizing normal generation, countably many times.
   `exists_countable_simple_subgroup` proves this in full, for an arbitrary
   group in which every nontrivial element normally generates; and
   `exists_countable_simple_sofic_subgroup` records the version that also
   carries soficity down, for an arbitrary simple sofic ambient group.  No
   hypothesis in either statement refers to ultraproducts: they are ordinary
   group theory.

Move 3 is the "downward Löwenheim--Skolem" half of the citation, and is the
only half that is delicate to state: the enlargement has to be performed
`ω` many times, because each round introduces new pairs of elements that must
themselves be joined by conjugators.

## What is missing — the closure record

This section is the standing record of what the Elek--Szabó citation still
costs.  It is meant to be readable without any accompanying report.

Move 2 is carried out in `GroupApproximation.Sofic.SoficEnvelopeSimplicity`,
which also composes moves 1--3 into the cited theorem.  **Everything in move 2
is proved there** from divergence of the model cardinalities alone -- that every
class has an *even* representative, that the ultraproduct is nontrivial, that
the density criterion below survives divergence, and that a normal subgroup
containing the class of `σ` contains the class of any sequence whose coordinates
are products of a *uniformly* bounded number of conjugates of `(σ i)^{±1}` --
**except for exactly one statement**, the bounded normal generation of finite
alternating groups:

> for every `δ > 0` there are `K` and `M` such that whenever `Ω` is a finite set
> with `|Ω| ≥ M` and `s` is an **even** permutation of `Ω` with
> `|supp s| ≥ δ|Ω|`, every even permutation of `Ω` is a product of at most `K`
> conjugates of `s` and `s⁻¹`.

That statement is a theorem of the literature -- it is what the Liebeck--Shalev
covering bounds for `Aₙ` supply, and it is the input Elek--Szabó use -- and this
repository does not prove it.  It is not tagged, aliased, or packaged: it is
written out in full as an explicit premise `hBNG` on exactly the three
declarations that consume it, and on nothing else anywhere in the corpus:

* `GroupApproximation.SoficEnvelopeSimplicity.isSimpleGroup_universalSofic`
* `GroupApproximation.SoficEnvelopeSimplicity.exists_countable_simple_sofic_envelope`
* `GroupApproximation.SoficEnvelopeWitness.manuscript_simpleSoficEnvelope`

**Print and Lean agree in strength.**  The manuscript paragraph *A simple sofic
envelope* does not claim this as its own; it prints
`\cite[Theorem~1]{ElekSzaboHyper}` for precisely the sentence "every countable
sofic group embeds in a countable simple sofic group".  The paragraph carries no
`\leanverified` badge, and none of the three declarations above may ever be
given one.

Two things about that premise are worth keeping on the record.  First, the
bound `K` must depend only on `δ` and not on `Ω` or on the index, which is what
makes the statement hard and what makes it the real content of the citation: an
unbounded product of conjugates has no image in the metric ultraproduct, and the
approximate form of the statement therefore does *not* suffice -- see the
"What cannot be weakened" section of `SoficEnvelopeSimplicity`, which records
why the natural iteration argument fails.  Second, the threshold `M` is not
cosmetic: on four points a product of two disjoint transpositions has full
support and normally generates only the Klein four-group.  Divergence of the
model cardinalities makes a threshold free.

None of that is assumed anywhere in *this* file: there is no declaration here
whose hypotheses include the simplicity of a universal sofic group, and no
predicate standing in for it.  Divergence of the model cardinalities is
genuinely needed for move 2: for a principal ultrafilter over a constant model
of size `n` the null subgroup is trivial and the ultraproduct is `Sym n`, which
for `n ≥ 3` is not simple.  Divergence is available from any sofic
approximation (`card_eventually_ge`).

The density half of the reduction of move 2 is recorded here: a class in
`UniversalSofic 𝒰 X` is nontrivial exactly when the supports of its
representatives occupy a positive fraction of the model on a `𝒰`-large set
(`exists_pos_support_density_of_mk_ne_one`).
-/

namespace GroupApproximation
namespace SoficEnvelopeExistence

open Filter

/-! ## Countability of generated subgroups

The enlargement in move 3 adds countably many generators at a time, so it has
to know that the subgroup generated by a countable set is countable.  The
proof is the standard surjection from the free group on the generating set. -/

/-- The subgroup generated by a countable set is countable. -/
theorem countable_closure_of_countable {Γ : Type*} [Group Γ] {S : Set Γ}
    (hS : S.Countable) : Countable ↥(Subgroup.closure S) := by
  haveI : Countable ↥S := hS.to_subtype
  haveI : Countable (FreeGroup ↥S) := by
    have hmk : Function.Surjective (FreeGroup.mk (α := ↥S)) := by
      rintro ⟨L⟩
      exact ⟨L, FreeGroup.quot_mk_eq_mk.symm⟩
    exact hmk.countable
  rw [FreeGroup.closure_eq_range]
  exact (MonoidHom.rangeRestrict_surjective _).countable

/-! ## Finitely many conjugators suffice

Membership in a normal closure is witnessed by a finite product of conjugates,
hence by a finite set of conjugating elements.  This is what makes each round
of the enlargement add only countably many new generators. -/

variable {Γ : Type*} [Group Γ]

/-- If `y` lies in the normal closure of `x`, then it lies in the subgroup
generated by the conjugates of `x` by a *finite* set of elements. -/
theorem exists_finset_conjugators {x y : Γ}
    (hy : y ∈ Subgroup.normalClosure ({x} : Set Γ)) :
    ∃ T : Finset Γ, y ∈ Subgroup.closure {w : Γ | ∃ g ∈ T, w = g * x * g⁻¹} := by
  classical
  have hy' : y ∈ Subgroup.closure (Group.conjugatesOfSet ({x} : Set Γ)) := hy
  clear hy
  induction hy' using Subgroup.closure_induction with
  | mem z hz =>
      rw [Group.mem_conjugatesOfSet_iff] at hz
      obtain ⟨a, ha, hconj⟩ := hz
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      exact ⟨{g}, Subgroup.subset_closure ⟨g, Finset.mem_singleton_self g, hg.symm⟩⟩
  | one => exact ⟨∅, one_mem _⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨T₁, h₁⟩ := iha
      obtain ⟨T₂, h₂⟩ := ihb
      refine ⟨T₁ ∪ T₂, mul_mem ?_ ?_⟩
      · refine Subgroup.closure_mono ?_ h₁
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨g, Finset.mem_union_left _ hg, rfl⟩
      · refine Subgroup.closure_mono ?_ h₂
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨g, Finset.mem_union_right _ hg, rfl⟩
  | inv a _ ih =>
      obtain ⟨T, h⟩ := ih
      exact ⟨T, inv_mem h⟩

/-- A total choice of conjugator sets: for every pair it returns a finite set
which works whenever `y` is in the normal closure of `x` at all. -/
theorem exists_conjugatorFinset (x y : Γ) :
    ∃ T : Finset Γ, y ∈ Subgroup.normalClosure ({x} : Set Γ) →
      y ∈ Subgroup.closure {w : Γ | ∃ g ∈ T, w = g * x * g⁻¹} := by
  classical
  by_cases hy : y ∈ Subgroup.normalClosure ({x} : Set Γ)
  · obtain ⟨T, hT⟩ := exists_finset_conjugators hy
    exact ⟨T, fun _ => hT⟩
  · exact ⟨∅, fun h => absurd h hy⟩

/-- The chosen finite set of conjugators for the pair `(x, y)`. -/
noncomputable def conjugatorFinset (x y : Γ) : Finset Γ :=
  (exists_conjugatorFinset x y).choose

/-- The defining property of `conjugatorFinset`. -/
theorem conjugatorFinset_spec {x y : Γ}
    (h : y ∈ Subgroup.normalClosure ({x} : Set Γ)) :
    y ∈ Subgroup.closure {w : Γ | ∃ g ∈ conjugatorFinset x y, w = g * x * g⁻¹} :=
  (exists_conjugatorFinset x y).choose_spec h

/-! ## The `ω`-step enlargement

`envelopeSeed s n` is the generating set after `n` rounds: each round throws in
the conjugators for every ordered pair of elements of the subgroup generated so
far.  `envelope s` is the union of the subgroups they generate. -/

/-- The generating set after `n` rounds of closing up under conjugators. -/
noncomputable def envelopeSeed (s : Set Γ) (n : ℕ) : Set Γ :=
  @Nat.rec (fun _ => Set Γ) s
    (fun _ A => A ∪ ⋃ p : ↥(Subgroup.closure A) × ↥(Subgroup.closure A),
      (↑(conjugatorFinset (p.1 : Γ) (p.2 : Γ)) : Set Γ)) n

@[simp] theorem envelopeSeed_zero (s : Set Γ) : envelopeSeed s 0 = s := rfl

@[simp] theorem envelopeSeed_succ (s : Set Γ) (n : ℕ) :
    envelopeSeed s (n + 1) =
      envelopeSeed s n ∪
        ⋃ p : ↥(Subgroup.closure (envelopeSeed s n)) ×
              ↥(Subgroup.closure (envelopeSeed s n)),
          (↑(conjugatorFinset (p.1 : Γ) (p.2 : Γ)) : Set Γ) := rfl

/-- The subgroup generated after `n` rounds. -/
noncomputable def envelopeStage (s : Set Γ) (n : ℕ) : Subgroup Γ :=
  Subgroup.closure (envelopeSeed s n)

theorem envelopeSeed_subset_succ (s : Set Γ) (n : ℕ) :
    envelopeSeed s n ⊆ envelopeSeed s (n + 1) := by
  rw [envelopeSeed_succ]
  exact Set.subset_union_left

theorem envelopeStage_le_succ (s : Set Γ) (n : ℕ) :
    envelopeStage s n ≤ envelopeStage s (n + 1) :=
  Subgroup.closure_mono (envelopeSeed_subset_succ s n)

theorem envelopeStage_mono (s : Set Γ) : Monotone (envelopeStage s) :=
  monotone_nat_of_le_succ (envelopeStage_le_succ s)

theorem envelopeSeed_countable {s : Set Γ} (hs : s.Countable) (n : ℕ) :
    (envelopeSeed s n).Countable := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [envelopeSeed_succ]
      refine ih.union ?_
      haveI : Countable ↥(Subgroup.closure (envelopeSeed s n)) :=
        countable_closure_of_countable ih
      exact Set.countable_iUnion fun _ => Finset.countable_toSet _

/-- The union of the stages, as a subgroup: the stages form a chain, so the
union is closed under the group operations. -/
noncomputable def envelope (s : Set Γ) : Subgroup Γ where
  carrier := {x : Γ | ∃ n, x ∈ envelopeStage s n}
  one_mem' := ⟨0, one_mem _⟩
  mul_mem' := by
    rintro a b ⟨n, ha⟩ ⟨m, hb⟩
    exact ⟨max n m, mul_mem (envelopeStage_mono s (le_max_left n m) ha)
      (envelopeStage_mono s (le_max_right n m) hb)⟩
  inv_mem' := by
    rintro a ⟨n, ha⟩
    exact ⟨n, inv_mem ha⟩

theorem mem_envelope {s : Set Γ} {x : Γ} :
    x ∈ envelope s ↔ ∃ n, x ∈ envelopeStage s n := Iff.rfl

theorem envelopeStage_le_envelope (s : Set Γ) (n : ℕ) :
    envelopeStage s n ≤ envelope s := by
  intro x hx
  exact mem_envelope.mpr ⟨n, hx⟩

theorem mem_envelope_of_mem (s : Set Γ) {x : Γ} (hx : x ∈ s) : x ∈ envelope s := by
  refine mem_envelope.mpr ⟨0, ?_⟩
  show x ∈ Subgroup.closure s
  exact Subgroup.subset_closure hx

theorem subset_envelope (s : Set Γ) : s ⊆ (envelope s : Set Γ) := by
  intro x hx
  exact mem_envelope_of_mem s hx

/-- The envelope is generated by the union of the seeds; this is how its
countability is read off. -/
theorem envelope_eq_closure (s : Set Γ) :
    envelope s = Subgroup.closure (⋃ n, envelopeSeed s n) := by
  apply le_antisymm
  · rintro x ⟨n, hx⟩
    exact Subgroup.closure_mono (Set.subset_iUnion (envelopeSeed s) n) hx
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact envelopeStage_le_envelope s n (Subgroup.subset_closure hn)

theorem envelope_countable {s : Set Γ} (hs : s.Countable) : Countable ↥(envelope s) := by
  rw [envelope_eq_closure]
  exact countable_closure_of_countable
    (Set.countable_iUnion fun n => envelopeSeed_countable hs n)

/-- Conjugators for a pair of elements of one stage are generators of the next
stage, hence members of the envelope. -/
theorem conjugator_mem_envelope (s : Set Γ) (n : ℕ) {x y : Γ}
    (hx : x ∈ envelopeStage s n) (hy : y ∈ envelopeStage s n)
    {g : Γ} (hg : g ∈ conjugatorFinset x y) : g ∈ envelope s := by
  have hseed : g ∈ envelopeSeed s (n + 1) := by
    rw [envelopeSeed_succ]
    refine Set.mem_union_right _ ?_
    rw [Set.mem_iUnion]
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Finset.mem_coe.mpr hg⟩
  exact ⟨n + 1, Subgroup.subset_closure hseed⟩

/-! ## Move 3: countable simple subgroups of a simple group -/

/-- In a simple group every nontrivial element normally generates. -/
theorem normalClosure_singleton_eq_top [IsSimpleGroup Γ] {γ : Γ} (hγ : γ ≠ 1) :
    Subgroup.normalClosure ({γ} : Set Γ) = ⊤ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (Subgroup.normalClosure_normal (s := ({γ} : Set Γ))) with h | h
  · exfalso
    rw [Subgroup.normalClosure_eq_bot_iff] at h
    exact hγ (Set.mem_singleton_iff.mp (h (Set.mem_singleton_iff.mpr rfl)))
  · exact h

/-- **The envelope is simple.**  If every nontrivial element of `Γ` normally
generates `Γ`, then the same holds inside the envelope, because the conjugators
realizing normal generation for a pair of its elements were themselves put into
the envelope one round later. -/
theorem envelope_isSimpleGroup
    (hΓ : ∀ γ : Γ, γ ≠ 1 → Subgroup.normalClosure ({γ} : Set Γ) = ⊤)
    {s : Set Γ} {z : Γ} (hz : z ∈ s) (hz1 : z ≠ 1) :
    IsSimpleGroup ↥(envelope s) where
  exists_pair_ne := by
    refine ⟨⟨z, mem_envelope_of_mem s hz⟩, 1, ?_⟩
    intro h
    exact hz1 (congrArg Subtype.val h)
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    rcases eq_or_ne N ⊥ with hbot | hbot
    · exact Or.inl hbot
    refine Or.inr ?_
    obtain ⟨⟨u, huN⟩, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hu1 : u ≠ 1 := fun h => hune (Subtype.ext h)
    have ha1 : (u : Γ) ≠ 1 := fun h => hu1 (Subtype.ext h)
    rw [Subgroup.eq_top_iff']
    rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := mem_envelope.mp u.2
    obtain ⟨m, hm⟩ := mem_envelope.mp hb
    have hak : (u : Γ) ∈ envelopeStage s (max n m) :=
      envelopeStage_mono s (le_max_left n m) hn
    have hbk : b ∈ envelopeStage s (max n m) :=
      envelopeStage_mono s (le_max_right n m) hm
    have hbmem : b ∈ Subgroup.normalClosure ({(u : Γ)} : Set Γ) := by
      rw [hΓ (u : Γ) ha1]
      exact Subgroup.mem_top b
    have hclos := conjugatorFinset_spec hbmem
    have hsub : {w : Γ | ∃ g ∈ conjugatorFinset (u : Γ) b, w = g * (u : Γ) * g⁻¹} ⊆
        ((N.map (envelope s).subtype : Subgroup Γ) : Set Γ) := by
      rintro _ ⟨g, hg, rfl⟩
      have hgE : g ∈ envelope s := conjugator_mem_envelope s (max n m) hak hbk hg
      show g * (u : Γ) * g⁻¹ ∈ N.map (envelope s).subtype
      exact Subgroup.mem_map.mpr
        ⟨(⟨g, hgE⟩ : ↥(envelope s)) * u * (⟨g, hgE⟩ : ↥(envelope s))⁻¹,
          hN.conj_mem u huN ⟨g, hgE⟩, rfl⟩
    have hle : Subgroup.closure
        {w : Γ | ∃ g ∈ conjugatorFinset (u : Γ) b, w = g * (u : Γ) * g⁻¹} ≤
          N.map (envelope s).subtype := (Subgroup.closure_le _).mpr hsub
    have hbM : b ∈ N.map (envelope s).subtype := hle hclos
    obtain ⟨w, hw, hwb⟩ := Subgroup.mem_map.mp hbM
    have hweq : (⟨b, hb⟩ : ↥(envelope s)) = w := Subtype.ext hwb.symm
    rw [hweq]
    exact hw

/-- **Downward Löwenheim--Skolem for simplicity.**  In a group in which every
nontrivial element normally generates, every countable subset containing a
nontrivial element is contained in a countable simple subgroup. -/
theorem exists_countable_simple_subgroup
    (hΓ : ∀ γ : Γ, γ ≠ 1 → Subgroup.normalClosure ({γ} : Set Γ) = ⊤)
    {s : Set Γ} (hs : s.Countable) {z : Γ} (hz : z ∈ s) (hz1 : z ≠ 1) :
    ∃ E : Subgroup Γ, s ⊆ (E : Set Γ) ∧ Countable ↥E ∧ IsSimpleGroup ↥E :=
  ⟨envelope s, subset_envelope s, envelope_countable hs,
    envelope_isSimpleGroup hΓ hz hz1⟩

/-- **The envelope theorem, relative to a simple sofic ambient group.**  Inside
a simple sofic group, every countable subset containing a nontrivial element
lies in a countable simple *sofic* subgroup.  Soficity descends because it
passes along injective homomorphisms.

This is move 3 of the Elek--Szabó argument in the exact form the manuscript
needs; supplying a simple sofic ambient group receiving the manuscript's
witness is move 2, which is open. -/
theorem exists_countable_simple_sofic_subgroup [IsSimpleGroup Γ] (hsofic : IsSofic Γ)
    {s : Set Γ} (hs : s.Countable) {z : Γ} (hz : z ∈ s) (hz1 : z ≠ 1) :
    ∃ E : Subgroup Γ, s ⊆ (E : Set Γ) ∧ Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E := by
  obtain ⟨E, hsE, hcount, hsimple⟩ :=
    exists_countable_simple_subgroup
      (fun γ hγ => normalClosure_singleton_eq_top hγ) hs hz hz1
  exact ⟨E, hsE, hcount, hsimple,
    isSofic_of_injective E.subtype Subtype.val_injective hsofic⟩

/-! ## Move 1: the ambient ultraproduct

Everything here is bookkeeping around `Sofic.SoficUltraproduct`.  The one point
that needs care is that `isSofic_of_soficEmbedding` asks for models of positive
cardinality, while a sofic approximation only has cardinalities *diverging*;
shifting the index past the finitely many empty models fixes this. -/

/-- Reindexing a sofic approximation past its first `N` models. -/
def shiftApproximation {G : Type*} [Group G] (S : SoficApproximation G) (N : ℕ) :
    SoficApproximation G where
  model := fun n => S.model (n + N)
  map := fun n => S.map (n + N)
  card_tendsToInfinity := by
    intro M
    obtain ⟨K, hK⟩ := S.card_tendsToInfinity M
    exact ⟨K, fun n hn => hK (n + N) (le_trans hn (Nat.le_add_right n N))⟩
  asymptoticallyMultiplicative := by
    intro g h ε hε
    obtain ⟨K, hK⟩ := S.asymptoticallyMultiplicative g h ε hε
    exact ⟨K, fun n hn => hK (n + N) (le_trans hn (Nat.le_add_right n N))⟩
  asymptoticallyFaithful := by
    intro g hg ε hε
    obtain ⟨K, hK⟩ := S.asymptoticallyFaithful g hg ε hε
    exact ⟨K, fun n hn => hK (n + N) (le_trans hn (Nat.le_add_right n N))⟩

/-- Every countable sofic group has a sofic approximation all of whose models
are nonempty. -/
theorem exists_positive_soficApproximation {G : Type*} [Group G] [Countable G]
    (h : IsSofic G) :
    ∃ S : SoficApproximation G, ∀ n, 0 < Fintype.card (S.model n) := by
  obtain ⟨S⟩ := soficApproximation_of_isSofic h
  obtain ⟨N, hN⟩ := S.card_tendsToInfinity 1
  refine ⟨shiftApproximation S N, fun n => ?_⟩
  show 0 < Fintype.card (S.model (n + N))
  have h1 := hN (n + N) (Nat.le_add_left N n)
  omega

/-- A nonprincipal ultrafilter on `ℕ`, in the form the ultraproduct
construction consumes. -/
theorem exists_cofinite_ultrafilter :
    ∃ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ Filter.cofinite :=
  ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le Filter.cofinite⟩

/-- **Move 1, forward.**  A countable sofic group embeds into a metric
ultraproduct of finite symmetric groups over models that are all nonempty. -/
theorem exists_soficEmbedding_positiveModels {G : Type*} [Group G] [Countable G]
    (h : IsSofic G) {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ f : G →* UniversalSofic 𝒰 X, Function.Injective f := by
  obtain ⟨S, hS⟩ := exists_positive_soficApproximation h
  obtain ⟨f, hf⟩ := exists_soficEmbedding_of_soficApproximation S hcof
  exact ⟨S.model, hS, f, hf⟩

/-- **Move 1, backward.**  A metric ultraproduct of finite symmetric groups
over nonempty models is itself sofic. -/
theorem isSofic_universalSofic {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)
    (hX : ∀ i, 0 < Fintype.card (X i)) : IsSofic (UniversalSofic 𝒰 X) :=
  isSofic_of_soficEmbedding 𝒰 X hX (MonoidHom.id (UniversalSofic 𝒰 X))
    (fun _ _ h => h)

/-- Every subgroup of such an ultraproduct is sofic. -/
theorem isSofic_subgroup_universalSofic {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) (hX : ∀ i, 0 < Fintype.card (X i))
    (H : Subgroup (UniversalSofic 𝒰 X)) : IsSofic ↥H :=
  isSofic_of_soficEmbedding 𝒰 X hX H.subtype Subtype.val_injective

/-- The model cardinalities of a sofic approximation diverge along any
ultrafilter refining the cofinite filter.  This is the hypothesis under which
the ultraproduct can be simple at all. -/
theorem card_eventually_ge {G : Type*} [Group G] (S : SoficApproximation G)
    {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) (M : ℕ) :
    ∀ᶠ n in (𝒰 : Filter ℕ), M ≤ Fintype.card (S.model n) := by
  obtain ⟨N, hN⟩ := S.card_tendsToInfinity M
  exact eventually_of_atTop hcof N hN

/-! ## Reduction of move 2 to a finite combinatorial statement

Nontriviality in the ultraproduct is a positive-density condition on supports.
This is the interface through which simplicity of `UniversalSofic 𝒰 X` becomes
bounded normal generation of the finite symmetric groups `Sym (X i)`. -/

/-- Hamming length is the normalized size of the support. -/
theorem hammingLength_eq_support_div (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingLength Y p = ((p.support.card : ℝ)) / Fintype.card Y := by
  have hdef : hammingLength Y p = hammingDistance Y p 1 := rfl
  rw [hdef, hammingDistance_eq_support]
  simp

/-- A sequence of permutations represents a nontrivial class exactly when its
Hamming length stays bounded away from zero on a `𝒰`-large set. -/
theorem exists_pos_hammingLength_of_mk_ne_one {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) (σ : ∀ i, Equiv.Perm (X i))
    (hσ : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in (𝒰 : Filter ι), δ ≤ hammingLength (X i) (σ i) := by
  have hnot : σ ∉ nullSubgroup 𝒰 X := fun hmem =>
    hσ ((QuotientGroup.eq_one_iff σ).mpr hmem)
  have hnot' : ¬ IsNullSeq 𝒰 X σ := hnot
  have hex : ∃ δ : ℝ, 0 < δ ∧
      ¬ (∀ᶠ i in (𝒰 : Filter ι), hammingLength (X i) (σ i) < δ) := by
    by_contra hcon
    refine hnot' fun δ hδ => ?_
    by_contra hbad
    exact hcon ⟨δ, hδ, hbad⟩
  obtain ⟨δ, hδ, hev⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  have hcompl := (Ultrafilter.eventually_not
    (p := fun i => hammingLength (X i) (σ i) < δ)).mpr hev
  filter_upwards [hcompl] with i hi
  exact not_lt.mp hi

/-- **The reduction of move 2.**  A nontrivial class of the ultraproduct is
represented by permutations whose supports have density bounded below along
`𝒰`.  Simplicity of `UniversalSofic 𝒰 X` is therefore exactly the statement
that in `Sym (X i)` such a permutation normally generates the alternating
group in a number of conjugates depending only on the density. -/
theorem exists_pos_support_density_of_mk_ne_one {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) (hX : ∀ i, 0 < Fintype.card (X i))
    (σ : ∀ i, Equiv.Perm (X i))
    (hσ : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in (𝒰 : Filter ι),
      δ * (Fintype.card (X i) : ℝ) ≤ ((σ i).support.card : ℝ) := by
  obtain ⟨δ, hδ, hev⟩ := exists_pos_hammingLength_of_mk_ne_one 𝒰 X σ hσ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hev] with i hi
  rw [hammingLength_eq_support_div] at hi
  have hc : (0 : ℝ) < (Fintype.card (X i) : ℝ) := by exact_mod_cast hX i
  have hmul := mul_le_mul_of_nonneg_right hi hc.le
  calc δ * (Fintype.card (X i) : ℝ)
      ≤ ((σ i).support.card : ℝ) / (Fintype.card (X i) : ℝ) *
          (Fintype.card (X i) : ℝ) := hmul
    _ = ((σ i).support.card : ℝ) := div_mul_cancel₀ _ hc.ne'

end SoficEnvelopeExistence
end GroupApproximation
