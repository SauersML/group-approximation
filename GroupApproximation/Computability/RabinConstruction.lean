import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import GroupApproximation.Algebra.PresentedGroupEvaluation

/-!
# The Adian--Rabin construction `K(w)`, and its collapse half

This file writes down the finite presentation that the Adian--Rabin
construction attaches to a word `w` of a finitely presented source group, and
proves --- unconditionally, with no hypothesis standing in for any unformalized
theorem --- the half of its defining biconditional that the manuscript needs on
the positive side: **if `w = 1` in the source group then the presented group
`K(w)` is trivial.**

Nothing here asserts the Adian--Rabin theorem, the Novikov--Boone theorem, or
the embedding half of the construction.  The embedding half is *not* taken as a
hypothesis anywhere; it is simply absent, and the roadmap below says exactly
what it costs.

## Manuscript location

Navigate `non_mf_groups_exist.tex` by stable anchors only; the file is under
concurrent edit and every offset drifts within minutes of being written down.

* `\subsection{Undecidability of MF recognition}` inside `sec:consequences`;
* the corollary `\label{cor:undecidable}`;
* the discussion paragraph opening "This corollary carries one classical
  literature input, used only here" and closing "No completeness of the word
  problem under many-one reduction is needed, only its undecidability".

The sentence this file is aimed at is the manuscript's own description of what
the construction supplies:

> What the construction supplies is a computable map taking an instance
> `(P,w)` of the word problem of a fixed finitely presented group with
> undecidable word problem to a finite presentation whose group is trivial ---
> hence MF --- when `w=1`, and contains `E` --- hence non-MF, by subgroup
> heredity --- when `w≠1`.

`rabin_trivial_of_word_eq_one` below is exactly the clause "whose group is
trivial ... when `w=1`", for the explicit presentation defined in this file.
The clause "contains `E` ... when `w≠1`" is **not** proved here; see the
roadmap.

## The construction

The construction is Rabin's, in the modern HNN/amalgam form (Lyndon--Schupp,
*Combinatorial Group Theory*, IV.4.1; the staged presentation followed here is
the one in E. Bajo, *Amalgamated free products, HNN extensions, and decision
problems*, §8).  Only the *shape* of the construction is taken from there; the
Lean proof below is a self-contained proof of the collapse.

Fix a finite presentation `⟨x₁,…,xₙ | R⟩` of a source group `Γ`, and a word
`w` in the `xᵢ`.  The construction proceeds in four stages.

1. **A free `ℤ` factor and a change of generators.**  Put
   `G = Γ * ⟨s₀⟩` and `sᵢ = s₀ xᵢ` for `1 ≤ i ≤ n`.  Since `xᵢ = s₀⁻¹ sᵢ`, the
   letters `s₀,…,sₙ` generate `G`, and
   `G = ⟨s₀,…,sₙ | R(s₀⁻¹s₁, …, s₀⁻¹sₙ)⟩`.
   The point of the change of generators is that *every* `sᵢ` has infinite
   order in `G`, whatever the `xᵢ` do.

2. **A layer of Baumslag--Solitar HNN extensions.**  Adjoin stable letters
   `t₀,…,tₙ` with `tᵢ sᵢ tᵢ⁻¹ = sᵢ²`, i.e. `n+1` successive HNN extensions
   with associated subgroups `⟨sᵢ⟩` and `⟨sᵢ²⟩`; call the result `G'`.  Then
   adjoin one further stable letter `u` with `u tᵢ u⁻¹ = tᵢ²`, an HNN
   extension of `G'` with associated subgroups `⟨t₀,…,tₙ⟩` and
   `⟨t₀²,…,tₙ²⟩`, both free of rank `n+1`; call the result `G''`.

3. **A Baumslag--Solitar tower on the other side.**  Let
   `G₂ = ⟨a, b, c | b a b⁻¹ = a², c b c⁻¹ = b²⟩`, an HNN extension of an HNN
   extension of `⟨a⟩ ≅ ℤ`.

4. **The amalgam.**  `K(w)` is `G'' * G₂` subject to the two relations
   `u = a` and `c = [w, s₀]`, where `[w, s₀] = w s₀ w⁻¹ s₀⁻¹`.  When `w ≠ 1`
   this is the amalgamated free product of `G''` and `G₂` over the rank-two
   free subgroups `⟨u, [w,s₀]⟩` and `⟨a, c⟩`.

The whole presentation of `K(w)`, on `2n+6` generators, is therefore

```
⟨ s₀,…,sₙ, t₀,…,tₙ, u, a, b, c |
    R(s₀⁻¹s₁,…,s₀⁻¹sₙ),
    tᵢ sᵢ tᵢ⁻¹ = sᵢ²        (0 ≤ i ≤ n),
    u tᵢ u⁻¹  = tᵢ²         (0 ≤ i ≤ n),
    b a b⁻¹   = a²,
    c b c⁻¹   = b²,
    u = a,
    c = [w, s₀]                                            ⟩
```

and this is `relators R w` below, verbatim.

## What is proved here

* `rabin_trivial_of_word_eq_one` --- **the collapse half**.  If `w = 1` in
  `⟨x | R⟩` then `K(w)` is the trivial group.  The proof is Rabin's chain,
  read off the relations:
  `w = 1 ⟹ [w,s₀] = 1 ⟹ c = 1 ⟹ b = 1 ⟹ a = 1 ⟹ u = 1 ⟹ tᵢ = 1 ⟹ sᵢ = 1`,
  each step being the observation that a Baumslag--Solitar relation
  `x y x⁻¹ = y²` with `x = 1` forces `y = y²`, hence `y = 1`.
  It is isolated from the presentation in `collapse_of_relations`, which is a
  statement about an arbitrary group carrying the relations and so survives any
  re-encoding of the presentation (in particular the transport to the
  presentation-code layer of `Computability.PresentationCodes`).
* `rabin_isFinitelyPresented` --- `K(w)` is finitely presented, for every `w`.
  The alphabet is finite and the relator set is a `Finset`.
* The relations themselves, as named theorems `rabin_relation_ts`,
  `rabin_relation_ut`, `rabin_relation_ba`, `rabin_relation_cb`,
  `rabin_relation_ua`, `rabin_relation_cw`, together with the homomorphism
  `rabinTheta : Γ →* K(w)` carrying the source group into `K(w)`.

Note that the collapse uses the source relators exactly once, and only through
`rabinTheta`: they are what turns "`w = 1` in `Γ`" into "`ŵ = 1` in `K(w)`".
After that the argument is pure Baumslag--Solitar bookkeeping and does not see
`R` at all.

## The status of the biconditional

The mathematical content of Adian--Rabin is the biconditional

```
K(w) has P   ↔   w = 1 in Γ,
```

which is a statement about an *arbitrary* source group and word: no
undecidability input enters it, and nothing in this file or its companions is
conditional on anything.  Of its two directions:

* `w = 1 ⟹ K(w) trivial ⟹ K(w)` is MF: **proved**, here and in
  `RabinConstructionMF.lean`.
* `K(w)` is MF `⟹ w = 1`, equivalently `w ≠ 1 ⟹ E ↪ K(w) ⟹ ¬ MF (K(w))`:
  the last implication is already proved
  (`OperatorMFMarkovWitness.chosen_forbidden_subgroup`); the embedding
  `E ↪ K(w)` is **missing**.

## What is NOT proved here, and what it costs

The missing direction is: **if `w ≠ 1` in `Γ` then the forbidden group embeds
in `K(w)`.**  Following the four stages above it decomposes as below.  The
sizes were re-estimated against the pinned Mathlib source
(`905b9581…`, `v4.32.2`), which turns out to supply more than expected.

* **E1. `G ≅ Γ * ℤ`.**  Two halves.
  (i) *A presentation on a disjoint union of alphabets presents the free
  product.*  Mathlib already has this as
  `PresentedGroup.coprodPresentations`, and `RabinConstructionSource.lean`
  packages the two consequences the construction needs (each factor embeds;
  the word problem of a factor is the restriction of the word problem of the
  free product).  **Done.**
  (ii) *The Tietze change of free basis* `s₀ ↦ s₀`, `sᵢ ↦ s₀xᵢ`.  This is a
  free-group automorphism, not an alphabet permutation, so
  `PresentedGroup.equivPresentedGroup` does not apply; the tool is
  `PresentedGroup.map` (which transports along any `FreeGroup α →* FreeGroup β`
  carrying relators to relators) in both directions, glued by
  `MonoidHom.toMulEquiv`.  **~120 lines, no mathematical risk.**
* **E2. Every `sᵢ` has infinite order in `G = Γ * ⟨s₀⟩`.**  For `i ≥ 1`,
  `sᵢ = s₀xᵢ` is cyclically reduced of free-product length `2` when `xᵢ ≠ 1`
  in `Γ`, and equals `s₀` otherwise.  Mathlib has the free-product normal form
  (`CoprodI.Word`, `CoprodI.Word.equiv`) and the `NeWord` apparatus, but no
  order-of-an-element consequence.  **~250 lines.**
* **E3. The `t`-layer is a genuine iterated HNN extension, and
  `⟨t₀,…,tₙ⟩`, `⟨t₀²,…,tₙ²⟩` are free of rank `n+1` on the displayed
  generators.**  Britton's lemma is in Mathlib
  (`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`), and this
  repository already exercises it in `Algebra.HNNTorsionFree`.  What is needed
  is `n+1` successive applications plus the cyclic-subgroup isomorphisms
  `⟨sᵢ⟩ ≃* ⟨sᵢ²⟩`, which follow from E2.  **~500 lines.**
* **E4. `⟨u, [w,s₀]⟩ ≤ G''` is free of rank two when `w ≠ 1`.**  Needs
  `[w,s₀]` to have infinite order in `G''` (Britton plus E2) and `u`, a stable
  letter, to be Britton-independent of it.  **~400 lines.**
* **E5. `⟨a, c⟩ ≤ G₂` is free of rank two.**  The same Britton argument for
  the concrete tower `ℤ ≤ BS(1,2) ≤ G₂`; `BS(1,2)` already exists in this
  repository as `Algebra.DyadicRationals.BS`, with its defining relation
  extracted, and `Algebra.HNNTorsionFree.lengthHom` already gives the
  stable-letter grading that separates `a` from `⟨b⟩`.  **~250 lines.**
* **E6. A presented group given by HNN relations *is* the HNN extension, and
  one given by amalgamation relations *is* the amalgamated free product.**
  *The HNN half of this is now done*: `Algebra.HNNPresentation.equivPres` is
  the isomorphism

  ```
  ⟨X ⊔ {s} | R ∪ { s (w i) s⁻¹ (v i)⁻¹ }⟩  ≃*  HNNExtension ⟨X | R⟩ A B φ
  ```

  for `A = ⟨w i⟩`, `B = ⟨v i⟩`, both directions, axiom-clean.  It is stated for
  an arbitrary index type `I`, so the `t`-layer of stage 2 and the single `u`
  of stage 2' are instances of it, and it gives the forward map E6 says is the
  only strictly needed half *and* the inverse.  The one step that is not
  bookkeeping there --- and the reason Mathlib's universal property does not
  suffice on its own --- is that `HNNExtension.lift` demands the conjugation
  identity for *every* element of the associated subgroup while a presentation
  supplies it only at the generators; `HNNPresentation.conj_eq_of_mem` closes
  that by `Subgroup.closure_induction`, which is worth knowing before
  attempting the amalgam half.  What remains of E6 is the `PushoutI` analogue
  for stage 4.
  Mathlib nowhere identifies `HNNExtension` or `PushoutI` with a
  `PresentedGroup`, but it does give both universal properties in usable form
  (`HNNExtension.lift`, `HNNExtension.hom_ext`; `PushoutI.lift`,
  `PushoutI.hom_ext_nonempty`), and `HNNExtension` is literally defined as a
  `Con` quotient of `G ∗ Multiplicative ℤ` by the conjugation relations.  So
  each identification is two `toGroup`/`lift` maps glued by
  `MonoidHom.toMulEquiv`, with the only real work being that a relation
  imposed on a generating set of the associated subgroup holds on the whole
  subgroup.  **~400 lines.**
  *Only the forward map is strictly needed*: to conclude `E ↪ K(w)` it is
  enough to have a homomorphism `K(w) →* J` into the honest tower `J` whose
  restriction along `E → K(w)` is the known injection `E → J`.  That halves
  E6 in practice.
* **E7. Assembly**: `E ↪ Γ ↪ G ↪ G' ↪ G'' ↪ K(w)`, the last inclusion by
  `PushoutI.of_injective`, the middle three by `HNNExtension.of_injective`,
  the first by `RabinConstructionSource.inclRight_injective`.  **~150 lines**,
  once E1--E6 exist.

### The freeness entries are cheaper than priced

`E3`, `E4` and `E5` all ask for a subgroup generated by finitely many *named*
elements to be free on them, and all three are priced as Britton arguments.
They are not: freeness of a named family is the cheap direction, and
`Algebra.HNNRetraction` now supplies both halves of the tool.

* `HNNRetraction.freeGroupLift_injective`: a family some homomorphism carries
  to a free basis *is* a free basis.  Ten lines, because
  `f ∘ FreeGroup.lift h = FreeGroup.lift (f ∘ h) = id`.
* `HNNRetraction.killBase`: every HNN extension admits a homomorphism killing
  its base and sending the stable letter anywhere.  `HNNExtension.lift` asks
  for `x * f a = f (φ a) * x`, and when `f` is trivial both sides are `x`, so
  the condition is vacuous --- no hypothesis on `A`, `B` or `φ`.

For `E3` the two combine directly.  Every associated subgroup of the `t`-layer
lies in the *original* base `G`, so the retraction
`G' →* FreeGroup (Fin (n+1))` that kills `G` and sends `tᵢ` to the `i`th
generator exists layer by layer for the same vacuous reason, and
`freeGroupLift_injective` turns it into freeness of `⟨t₀,…,tₙ⟩`.  What is left
of `E3` is the iterated construction itself, not the freeness.

`HNNRetraction.zpow_t_ne_one` --- the stable letter has infinite order in every
HNN extension --- comes from the same retraction and is what `E4` and `E5` need
about `u` and about `a`; what those two still need on top is the *base* side
(`[w,s₀]` of infinite order in `G''`, which is `E2` plus Britton).

### A variant construction that removes E3, E4 and E5 entirely

The expensive entries all come from one place: Rabin's `u`-layer must force
`n+1` stable letters to be trivial at once, so its associated subgroups are
`⟨t₀,…,tₙ⟩` and `⟨t₀²,…,tₙ²⟩`, and the second has to be shown free *on the
squares*.  That fact (equivalently, injectivity of the squaring endomorphism of
a free group) is not in Mathlib at the pinned revision, which has neither
`PingPong.lean` nor `NielsenSchreier.lean`, so it would have to be proved from
reduced words.  `E4` and `E5` then ask for two more rank-two freeness facts.

All three disappear under one observation about what the collapse half has to
achieve.  **The collapse does not have to reach the trivial group.**  What
`cor:undecidable` needs is that `K(w)` is MF when `w = 1`, and free groups are
MF --- they are residually finite, so `lem:permanence(2)` applies.  It is
therefore enough to kill the *base*, and to let the stable letters survive.

That frees the `u`-layer to conjugate `⟨t₀,…,tₙ⟩` onto `⟨t₀s₀,…,tₙsₙ⟩` rather
than onto the squares.  Both are free on the displayed generators for the same
reason and by the same witness: the retraction `G' →* FreeGroup (Fin (n+1))`
of `HNNRetraction.killBase` kills the base, so it sends `tᵢ` and `tᵢsᵢ` alike
to the `i`th generator, and `HNNRetraction.freeGroupLift_injective` converts
that into freeness of both.  No squares fact, and no rank-two argument.  The
collapse still fires: `u = 1` turns `u tᵢ u⁻¹ = tᵢsᵢ` into `tᵢ = tᵢsᵢ`, hence
`sᵢ = 1` for every `i`, hence the base is trivial, since the `sᵢ` generate it.
What is left standing is a free group on the stable letters, which is MF.

The same move removes the amalgam of stage 4, whose associated subgroups
`⟨u,[w,s₀]⟩` and `⟨a,c⟩` are the other rank-two demand.  Continue instead with
HNN layers over `G''`: adjoin `b` along `⟨u⟩ ≅ ⟨u²⟩` and `c` along
`⟨b⟩ ≅ ⟨b²⟩`, both cyclic and both legitimate because a stable letter has
infinite order (`HNNRetraction.zpow_t_ne_one`), and close the cascade with a
final stable letter `k` adjoined along `⟨[w,s₀]⟩ ≅ ⟨b⟩`.  Then `w = 1` makes
`[w,s₀] = 1`, so `b = 1`, so `u = 1`, and the cascade runs as before.

Under this variant the *only* fact left that is not a retraction is:

> `[w,s₀]` has infinite order in `(Γ * E) * ⟨s₀⟩` when `w ≠ 1`,

a single free-product statement, provable from `CoprodI.Word`; every associated
subgroup in the tower is then either cyclic on an element of infinite order or
free on a family the retraction exhibits.  `E7` is unchanged: the composite
`E ↪ (Γ * E) * ⟨s₀⟩ ↪ ⋯ ↪ K(w)` is injective because each step is
`HNNExtension.of_injective` and the first is `inclRight_injective`.

This is a design, not a proof: nothing below implements it, the presentation in
this file is still Rabin's, and the embedding half is still absent.  It is
recorded because it changes what the remaining work is --- one free-product
lemma, the tower, and the assembly, rather than three Britton arguments and a
free-group fact Mathlib does not have.

Total for the missing direction: **~2000 lines** as first priced, dominated by
E3 and E4; less the HNN half of E6, which `Algebra.HNNPresentation` supplies,
and less the freeness of E3 and the infinite-order halves of E4 and E5, which
`Algebra.HNNRetraction` supplies.  The estimate has not been re-totalled: what
is certain is that the three entries priced as Britton arguments are no longer
Britton arguments, and that the embedding half is still absent.  The
critical difficulty is uniform: every one of E2--E5 is the statement that some
explicitly displayed subgroup of a free product or HNN extension is as free as
it looks, and each needs its own normal-form argument.

## Does the manuscript's specific Markov property admit a shorter route?

Essentially no, and the reason is structural: the cost of the construction is
concentrated in the *negative* side, and the negative side is the same for
every Markov property.  Four candidate shortcuts and their fate:

1. *Weaken the positive target.*  MF holds for every countable residually
   finite group, not just the trivial one, so `K(1)` need only be residually
   finite.  This is a genuine relaxation and it buys exactly one thing: the
   final amalgam may be replaced by an HNN extension with a fresh stable
   letter `z` conjugating `⟨u,[w,s₀]⟩` onto `⟨a,c⟩`, whose collapse leaves
   `K(1) ≅ ⟨z⟩ ≅ ℤ` rather than `1`.  Since `ℤ` is residually finite it is MF,
   so the reduction still works, and the construction then uses only
   `HNNExtension` --- Mathlib's `PushoutI` drops out of the dependency list
   entirely.  This is the one real, MF-specific engineering saving, and it is
   modest: it removes E6's amalgam half, not any of E2--E5.  It is *not* what
   this file builds, because the manuscript prints "trivial", and Lean moves
   toward the TeX.
2. *Shorten the Baumslag--Solitar tower.*  Each rung is forced.  `⟨a,c⟩` must
   be free of rank two, so `c` must be a stable letter over a base containing
   `a`; in `BS(1,2) = ⟨a,b⟩` the pair `⟨a,b⟩` is not free, so the intermediate
   rung `b` cannot be deleted.  Likewise `u` must be a stable letter for
   `⟨u,[w,s₀]⟩` to be free, and the `t`-layer cannot be skipped because
   `⟨s₀,…,sₙ⟩` is *not* free in `G` --- it satisfies the source relators ---
   whereas the fresh stable letters `t₀,…,tₙ` are.  The tower is minimal.
3. *Drop the collapse and impose `[w,s₀] tᵢ [w,s₀]⁻¹ = tᵢ²` directly.*  This
   does collapse `K(1)` to the trivial group with far fewer generators, and
   the exponent-sum obstruction that blocks pure HNN towers does not apply.
   But `[w,s₀]` is then a word in the base rather than a new letter, so the
   relation is a quotient, not an HNN or amalgam relation, and the embedding
   direction is destroyed.  The extra letters `a, b, c` exist precisely to
   turn that identification into an amalgamation.
4. *Change the source problem.*  The reduction must output group
   presentations and its correctness is about a group element being trivial,
   so some finitely presented group with undecidable word problem is
   unavoidable; and the decision problem is over *finite* presentations, so
   the elementary finitely generated recursively presented examples do not
   help without Higman embedding, which is harder than Novikov--Boone.

**Verdict: no.**  Beyond item 1's modest saving, the manuscript's instance
costs what the general theorem costs.  What the manuscript's own phrasing does
bank is that only *undecidability* is needed, never many-one completeness ---
so the upstream lane may target any single finitely presented group whose word
problem is undecidable, with no uniformity obligation.

## Docking with the presentation-code layer

`Computability.PresentationCodes` fixes a `Primcodable` code type and interprets
a code `c` as `PresentedGroup ↑(relatorFinset c)` over the alphabet
`Fin (genCount c)`.  The construction here is already in that shape --- a
`Finset` of relators over a finite alphabet --- except that the alphabet is
`Gen n = Fin (n+1) ⊕ Fin (n+1) ⊕ Extra` rather than a `Fin`.  Mathlib closes
that gap directly: `PresentedGroup.equivPresentedGroup rels (e : α ≃ β)` is an
isomorphism `PresentedGroup rels ≃* PresentedGroup (freeGroupCongr e '' rels)`,
so any bijection `Gen n ≃ Fin (2n+6)` transports `K(w)` onto a coded group.
What remains for an *effective* reduction is not this isomorphism but the
`Primrec` bookkeeping: that `w ↦ (code of relators R w)` is computable.  That is
list surgery on `ℕ × List (List (ℕ × Bool))` and belongs to the coding layer,
not here.  Note also that `MarkovMFConsequences.AdianRabinReduction` --- the
structure whose fields are exactly Rabin's construction and which nothing in
the repository currently inhabits --- is what the completed biconditional plus
that `Primrec` bookkeeping would discharge.

## One coordination fact, for the record

**The source group is not arbitrary.**  Stage 1 starts from `H * F`, where `F`
is the forbidden group.  For the manuscript's instance the forbidden group is
this repository's finitely presented non-MF group `E`, so the source must be
`H * E`: the reduction needs `E` to be a free factor of the source, because
that is how `E` ends up inside `K(w)`.  What the upstream word-problem lane
eventually owes is therefore undecidability for `H * E`, not for `H` alone ---
and that is not an extra debt, because
`RabinConstructionSource.mk_map_inl_eq_one_iff` reduces it to undecidability
for `H` with no further group theory.  No statement anywhere in these files
assumes it.
-/

namespace GroupApproximation
namespace RabinConstruction

/-! ## The collapse mechanism

Two relator shapes and the three-line piece of group theory that makes Rabin's
chain run.  Nothing in this section mentions presentations, so it applies
verbatim to any group carrying the relations, whatever encoding produced it.
-/

section Mechanism

variable {M : Type*} [Group M]

/-- The Baumslag--Solitar relator `x y x⁻¹ (y²)⁻¹`, asserting `x y x⁻¹ = y²`. -/
def bsWord (x y : M) : M := x * y * x⁻¹ * (y ^ 2)⁻¹

/-- The commutator word `x y x⁻¹ y⁻¹`. -/
def commWord (x y : M) : M := x * y * x⁻¹ * y⁻¹

theorem map_bsWord {N : Type*} [Group N] (f : M →* N) (x y : M) :
    f (bsWord x y) = bsWord (f x) (f y) := by
  simp only [bsWord, map_mul, map_inv, map_pow]

theorem map_commWord {N : Type*} [Group N] (f : M →* N) (x y : M) :
    f (commWord x y) = commWord (f x) (f y) := by
  simp only [commWord, map_mul, map_inv]

/-- A commutator with a trivial first entry is trivial.  This is the step
`w = 1 ⟹ [w, s₀] = 1` of Rabin's chain. -/
theorem commWord_one_left (y : M) : commWord (1 : M) y = 1 := by
  simp [commWord]

/-- Reading a Baumslag--Solitar relator as the relation it asserts. -/
theorem conj_eq_sq_of_bsWord_eq_one {x y : M} (h : bsWord x y = 1) :
    x * y * x⁻¹ = y ^ 2 := by
  have h' : x * y * x⁻¹ * (y ^ 2)⁻¹ = 1 := h
  exact mul_inv_eq_one.mp h'

/-- An element equal to its own square is trivial. -/
theorem eq_one_of_eq_sq {x : M} (h : x = x ^ 2) : x = 1 := by
  have h2 : x * x = x := by
    rw [← pow_two]
    exact h.symm
  calc x = x⁻¹ * (x * x) := by group
    _ = x⁻¹ * x := by rw [h2]
    _ = 1 := by group

/-- **The single step of Rabin's collapse chain.**  A Baumslag--Solitar
relation `x y x⁻¹ = y²` whose conjugator has died forces `y = y²`, hence
`y = 1`.  Iterating this down the tower `c → b → a = u → tᵢ → sᵢ` is the whole
content of the collapse. -/
theorem eq_one_of_conj_eq_sq {x y : M} (h : x * y * x⁻¹ = y ^ 2) (hx : x = 1) :
    y = 1 := by
  rw [hx, one_mul, inv_one, mul_one] at h
  exact eq_one_of_eq_sq h

end Mechanism

/-! ## The Rabin alphabet -/

/-- The four letters of the Rabin presentation that are not indexed by a source
generator: the stable letter `u` of the top HNN extension of the source side,
and the three generators `a, b, c` of the Baumslag--Solitar tower
`G₂ = ⟨a,b,c | b a b⁻¹ = a², c b c⁻¹ = b²⟩`. -/
inductive Extra : Type
  | u : Extra
  | a : Extra
  | b : Extra
  | c : Extra
  deriving DecidableEq

instance : Fintype Extra where
  elems := {Extra.u, Extra.a, Extra.b, Extra.c}
  complete := by
    intro x
    cases x <;> simp

/-- The generator alphabet of `K(w)` over a source alphabet `Fin n`: the `n+1`
letters `s₀,…,sₙ`, the `n+1` stable letters `t₀,…,tₙ`, and the four extra
letters.  In particular the alphabet is finite, with `2n + 6` letters. -/
abbrev Gen (n : ℕ) : Type := Fin (n + 1) ⊕ Fin (n + 1) ⊕ Extra

/-- The letter `sᵢ`, `0 ≤ i ≤ n`. -/
def sLetter {n : ℕ} (i : Fin (n + 1)) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inl i)

/-- The stable letter `tᵢ` of the `i`-th Baumslag--Solitar extension. -/
def tLetter {n : ℕ} (i : Fin (n + 1)) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inr (Sum.inl i))

/-- The stable letter `u` of the top HNN extension on the source side. -/
def uLetter (n : ℕ) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inr (Sum.inr Extra.u))

/-- The bottom generator `a` of the Baumslag--Solitar tower `G₂`. -/
def aLetter (n : ℕ) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inr (Sum.inr Extra.a))

/-- The middle generator `b` of the Baumslag--Solitar tower `G₂`. -/
def bLetter (n : ℕ) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inr (Sum.inr Extra.b))

/-- The top generator `c` of the Baumslag--Solitar tower `G₂`, the letter that
gets identified with the commutator `[w, s₀]`. -/
def cLetter (n : ℕ) : FreeGroup (Gen n) :=
  FreeGroup.of (Sum.inr (Sum.inr Extra.c))

/-- The change of generators `xᵢ ↦ s₀⁻¹ sᵢ₊₁` of stage 1, as a homomorphism of
free groups.  It rewrites every source word in the `s`-letters. -/
def sSubst (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Gen n) :=
  FreeGroup.lift fun i ↦ (sLetter (0 : Fin (n + 1)))⁻¹ * sLetter i.succ

@[simp] theorem sSubst_of {n : ℕ} (i : Fin n) :
    sSubst n (FreeGroup.of i) = (sLetter (0 : Fin (n + 1)))⁻¹ * sLetter i.succ := by
  simp only [sSubst, FreeGroup.lift_apply_of]

/-! ## The relators -/

/-- The relators of the source presentation, rewritten in the `s`-letters.
This is `R(s₀⁻¹s₁, …, s₀⁻¹sₙ)`. -/
def sourceRelators {n : ℕ} (R : Finset (FreeGroup (Fin n))) :
    Finset (FreeGroup (Gen n)) :=
  R.image (sSubst n)

/-- The relators `tᵢ sᵢ tᵢ⁻¹ = sᵢ²`, one for each `0 ≤ i ≤ n`.

Note the index range: the exposition in Bajo §8 prints `1 ≤ i ≤ n` for these
and for the `u`-relations while listing `n+1` stable letters `t₀,…,tₙ`, which
is a typographical slip.  The relation must be imposed for `i = 0` as well,
otherwise the collapse never reaches `s₀` and `t₀` is unconstrained. -/
def stRelators (n : ℕ) : Finset (FreeGroup (Gen n)) :=
  Finset.univ.image fun i : Fin (n + 1) ↦ bsWord (tLetter i) (sLetter i)

/-- The relators `u tᵢ u⁻¹ = tᵢ²`, one for each `0 ≤ i ≤ n`. -/
def utRelators (n : ℕ) : Finset (FreeGroup (Gen n)) :=
  Finset.univ.image fun i : Fin (n + 1) ↦ bsWord (uLetter n) (tLetter i)

/-- The four remaining relators: the two Baumslag--Solitar relations of `G₂`,
and the two amalgamating relations `u = a` and `c = [w, s₀]`. -/
def tailRelators (n : ℕ) (w : FreeGroup (Fin n)) : Finset (FreeGroup (Gen n)) :=
  {bsWord (bLetter n) (aLetter n),
    bsWord (cLetter n) (bLetter n),
    uLetter n * (aLetter n)⁻¹,
    cLetter n * (commWord (sSubst n w) (sLetter (0 : Fin (n + 1))))⁻¹}

/-- **The relator set of `K(w)`.**  A finite set, computed from the finite
source presentation `R` and the source word `w` by explicit word surgery. -/
def relators {n : ℕ} (R : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n)) :
    Finset (FreeGroup (Gen n)) :=
  sourceRelators R ∪ stRelators n ∪ utRelators n ∪ tailRelators n w

/-- **The Rabin group `K(w)`.** -/
abbrev RabinGroup {n : ℕ} (R : Finset (FreeGroup (Fin n)))
    (w : FreeGroup (Fin n)) : Type :=
  PresentedGroup ((relators R w : Finset (FreeGroup (Gen n))) :
    Set (FreeGroup (Gen n)))

/-- The source group `Γ = ⟨x₁,…,xₙ | R⟩`. -/
abbrev SourceGroup {n : ℕ} (R : Finset (FreeGroup (Fin n))) : Type :=
  PresentedGroup ((R : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n)))

/-- Evaluation of a free word of the Rabin alphabet in `K(w)`. -/
abbrev eval {n : ℕ} (R : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n)) :
    FreeGroup (Gen n) →* RabinGroup R w :=
  PresentedGroup.mk _

section Presentation

variable {n : ℕ} (R : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n))

/-- **`K(w)` is finitely presented, for every `w`.**  This is the output
requirement of the reduction: the construction must land in finite
presentations, not merely in recursive ones. -/
theorem rabin_isFinitelyPresented :
    Group.IsFinitelyPresented (RabinGroup R w) :=
  inferInstance

/-! ### Membership of the individual relators -/

theorem mem_relators_source {r : FreeGroup (Fin n)} (hr : r ∈ R) :
    sSubst n r ∈ relators R w := by
  have h : sSubst n r ∈ sourceRelators R := Finset.mem_image_of_mem _ hr
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl h))

theorem mem_relators_st (i : Fin (n + 1)) :
    bsWord (tLetter i) (sLetter i) ∈ relators R w := by
  have h : bsWord (tLetter i) (sLetter i) ∈ stRelators n :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem mem_relators_ut (i : Fin (n + 1)) :
    bsWord (uLetter n) (tLetter i) ∈ relators R w := by
  have h : bsWord (uLetter n) (tLetter i) ∈ utRelators n :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inr h)

theorem mem_relators_ba :
    bsWord (bLetter n) (aLetter n) ∈ relators R w := by
  have h : bsWord (bLetter n) (aLetter n) ∈ tailRelators n w := by
    simp only [tailRelators]
    exact Finset.mem_insert_self _ _
  simp only [relators, Finset.mem_union]
  exact Or.inr h

theorem mem_relators_cb :
    bsWord (cLetter n) (bLetter n) ∈ relators R w := by
  have h : bsWord (cLetter n) (bLetter n) ∈ tailRelators n w := by
    simp only [tailRelators]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  simp only [relators, Finset.mem_union]
  exact Or.inr h

theorem mem_relators_ua :
    uLetter n * (aLetter n)⁻¹ ∈ relators R w := by
  have h : uLetter n * (aLetter n)⁻¹ ∈ tailRelators n w := by
    simp only [tailRelators]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  simp only [relators, Finset.mem_union]
  exact Or.inr h

theorem mem_relators_cw :
    cLetter n * (commWord (sSubst n w) (sLetter (0 : Fin (n + 1))))⁻¹ ∈
      relators R w := by
  have h : cLetter n * (commWord (sSubst n w) (sLetter (0 : Fin (n + 1))))⁻¹ ∈
      tailRelators n w := by
    simp only [tailRelators]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  simp only [relators, Finset.mem_union]
  exact Or.inr h

/-- Every relator dies in `K(w)`. -/
theorem relator_eval_eq_one {r : FreeGroup (Gen n)} (hr : r ∈ relators R w) :
    eval R w r = 1 :=
  PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)

/-! ### The defining relations of `K(w)` -/

/-- `tᵢ sᵢ tᵢ⁻¹ = sᵢ²` in `K(w)`. -/
theorem rabin_relation_ts (i : Fin (n + 1)) :
    eval R w (tLetter i) * eval R w (sLetter i) * (eval R w (tLetter i))⁻¹ =
      eval R w (sLetter i) ^ 2 := by
  have h := relator_eval_eq_one R w (mem_relators_st R w i)
  rw [map_bsWord] at h
  exact conj_eq_sq_of_bsWord_eq_one h

/-- `u tᵢ u⁻¹ = tᵢ²` in `K(w)`. -/
theorem rabin_relation_ut (i : Fin (n + 1)) :
    eval R w (uLetter n) * eval R w (tLetter i) * (eval R w (uLetter n))⁻¹ =
      eval R w (tLetter i) ^ 2 := by
  have h := relator_eval_eq_one R w (mem_relators_ut R w i)
  rw [map_bsWord] at h
  exact conj_eq_sq_of_bsWord_eq_one h

/-- `b a b⁻¹ = a²` in `K(w)`. -/
theorem rabin_relation_ba :
    eval R w (bLetter n) * eval R w (aLetter n) * (eval R w (bLetter n))⁻¹ =
      eval R w (aLetter n) ^ 2 := by
  have h := relator_eval_eq_one R w (mem_relators_ba R w)
  rw [map_bsWord] at h
  exact conj_eq_sq_of_bsWord_eq_one h

/-- `c b c⁻¹ = b²` in `K(w)`. -/
theorem rabin_relation_cb :
    eval R w (cLetter n) * eval R w (bLetter n) * (eval R w (cLetter n))⁻¹ =
      eval R w (bLetter n) ^ 2 := by
  have h := relator_eval_eq_one R w (mem_relators_cb R w)
  rw [map_bsWord] at h
  exact conj_eq_sq_of_bsWord_eq_one h

/-- `u = a` in `K(w)`: the first amalgamating relation. -/
theorem rabin_relation_ua :
    eval R w (uLetter n) = eval R w (aLetter n) := by
  have h := relator_eval_eq_one R w (mem_relators_ua R w)
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- `c = [w, s₀]` in `K(w)`: the second amalgamating relation, and the only
place where the source word `w` enters the presentation. -/
theorem rabin_relation_cw :
    eval R w (cLetter n) =
      commWord (eval R w (sSubst n w)) (eval R w (sLetter (0 : Fin (n + 1)))) := by
  have h := relator_eval_eq_one R w (mem_relators_cw R w)
  rw [map_mul, map_inv, map_commWord] at h
  exact mul_inv_eq_one.mp h

/-! ### The source group maps into `K(w)`

Stage 1 of the construction says that the source generator `xᵢ` is `s₀⁻¹sᵢ₊₁`.
That assignment respects the source relators --- they are among the relators of
`K(w)`, rewritten --- so it defines a homomorphism `Γ →* K(w)`.  This is the
only step in which the source relators are used at all. -/

/-- The image of the source generator `xᵢ` in `K(w)`, namely `s₀⁻¹ sᵢ₊₁`. -/
def sourceGen (i : Fin n) : RabinGroup R w :=
  (eval R w (sLetter (0 : Fin (n + 1))))⁻¹ * eval R w (sLetter i.succ)

/-- Evaluating a source word at `s₀⁻¹sᵢ₊₁` is the same as rewriting it in the
`s`-letters first and then evaluating. -/
theorem lift_sourceGen (v : FreeGroup (Fin n)) :
    FreeGroup.lift (sourceGen R w) v = eval R w (sSubst n v) := by
  have key : ∀ v : FreeGroup (Fin n),
      FreeGroup.lift (sourceGen R w) v = ((eval R w).comp (sSubst n)) v := by
    refine freeGroup_hom_eq_on_generators ?_
    intro i
    simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, sSubst_of, map_mul,
      map_inv, sourceGen]
  exact key v

/-- The source relators are killed by the assignment `xᵢ ↦ s₀⁻¹sᵢ₊₁`. -/
theorem lift_sourceGen_relator_eq_one :
    ∀ r ∈ ((R : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n))),
      FreeGroup.lift (sourceGen R w) r = 1 := by
  intro r hr
  rw [lift_sourceGen]
  exact relator_eval_eq_one R w (mem_relators_source R w (Finset.mem_coe.mp hr))

/-- **The canonical homomorphism `Γ →* K(w)`.**  It is not claimed to be
injective; injectivity for `w ≠ 1` is exactly the missing embedding half. -/
def rabinTheta : SourceGroup R →* RabinGroup R w :=
  PresentedGroup.toGroup (lift_sourceGen_relator_eq_one R w)

/-- A universal map out of a presented group computes by free evaluation on
every represented word. -/
theorem presented_toGroup_mk {X : Type*} {N : Type*} [Group N]
    {rels : Set (FreeGroup X)} {f : X → N}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (v : FreeGroup X) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels v) = FreeGroup.lift f v := by
  refine freeGroup_hom_eq_on_generators
    (f := (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels))
    (g := FreeGroup.lift f) ?_ v
  intro i
  rw [MonoidHom.comp_apply,
    show PresentedGroup.mk rels (FreeGroup.of i) = PresentedGroup.of i from rfl,
    PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]

theorem rabinTheta_mk (v : FreeGroup (Fin n)) :
    rabinTheta R w (PresentedGroup.mk _ v) = eval R w (sSubst n v) := by
  have h1 : rabinTheta R w (PresentedGroup.mk _ v) =
      FreeGroup.lift (sourceGen R w) v :=
    presented_toGroup_mk (lift_sourceGen_relator_eq_one R w) v
  rw [h1, lift_sourceGen]

/-- **The step `w = 1 in Γ ⟹ ŵ = 1 in K(w)`.**  This is the only use the
collapse makes of the source presentation. -/
theorem sSubst_word_eq_one
    (hw : PresentedGroup.mk ((R : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) w = 1) :
    eval R w (sSubst n w) = 1 := by
  have h : rabinTheta R w (PresentedGroup.mk _ w) = 1 := by
    rw [hw, map_one]
  rw [rabinTheta_mk] at h
  exact h

end Presentation

/-! ## Rabin's collapse chain

The chain, stated for an arbitrary group carrying the relations.  Keeping it
free of `PresentedGroup` means that any other encoding of the same presentation
--- in particular the transport to the presentation codes of
`Computability.PresentationCodes`, which an effective reduction has to go
through --- can reuse it unchanged. -/

/-- **Rabin's collapse chain.**  In any group carrying the defining relations of
`K(w)`, a trivial image `ω` of the source word forces every displayed generator
to be trivial:
`ω = 1 ⟹ γ = [ω,σ₀] = 1 ⟹ β = 1 ⟹ α = 1 ⟹ μ = α = 1 ⟹ τᵢ = 1 ⟹ σᵢ = 1`. -/
theorem collapse_of_relations {M : Type*} [Group M] {N : ℕ}
    {σ τ : Fin (N + 1) → M} {μ α β γ ω : M}
    (hts : ∀ i, τ i * σ i * (τ i)⁻¹ = σ i ^ 2)
    (hut : ∀ i, μ * τ i * μ⁻¹ = τ i ^ 2)
    (hba : β * α * β⁻¹ = α ^ 2)
    (hcb : γ * β * γ⁻¹ = β ^ 2)
    (hua : μ = α)
    (hcw : γ = commWord ω (σ 0))
    (hω : ω = 1) :
    (∀ i, σ i = 1) ∧ (∀ i, τ i = 1) ∧ μ = 1 ∧ α = 1 ∧ β = 1 ∧ γ = 1 := by
  have hγ : γ = 1 := by rw [hcw, hω, commWord_one_left]
  have hβ : β = 1 := eq_one_of_conj_eq_sq hcb hγ
  have hα : α = 1 := eq_one_of_conj_eq_sq hba hβ
  have hμ : μ = 1 := by rw [hua, hα]
  have hτ : ∀ i, τ i = 1 := fun i ↦ eq_one_of_conj_eq_sq (hut i) hμ
  have hσ : ∀ i, σ i = 1 := fun i ↦ eq_one_of_conj_eq_sq (hts i) (hτ i)
  exact ⟨hσ, hτ, hμ, hα, hβ, hγ⟩

section Collapse

variable {n : ℕ} (R : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n))

/-- Every generator of `K(w)` is trivial once `w = 1` in the source group. -/
theorem generator_eq_one_of_word_eq_one
    (hw : PresentedGroup.mk ((R : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) w = 1) (g : Gen n) :
    eval R w (FreeGroup.of g) = 1 := by
  obtain ⟨hσ, hτ, hμ, hα, hβ, hγ⟩ :=
    collapse_of_relations
      (σ := fun i ↦ eval R w (sLetter i))
      (τ := fun i ↦ eval R w (tLetter i))
      (μ := eval R w (uLetter n)) (α := eval R w (aLetter n))
      (β := eval R w (bLetter n)) (γ := eval R w (cLetter n))
      (ω := eval R w (sSubst n w))
      (rabin_relation_ts R w) (rabin_relation_ut R w) (rabin_relation_ba R w)
      (rabin_relation_cb R w) (rabin_relation_ua R w) (rabin_relation_cw R w)
      (sSubst_word_eq_one R w hw)
  rcases g with i | i | e
  · exact hσ i
  · exact hτ i
  · cases e
    · exact hμ
    · exact hα
    · exact hβ
    · exact hγ

/-- **The collapse half of the Adian--Rabin construction.**  If the source word
`w` is trivial in `Γ = ⟨x | R⟩`, then the finitely presented group `K(w)` is
trivial.

This is the manuscript's clause "a finite presentation whose group is trivial
--- hence MF --- when `w = 1`", proved for the explicit presentation
`relators R w`.  It is unconditional: no Novikov--Boone input, no reduction
data, no hypothesis encoding an unformalized theorem.  The companion clause,
that `E` embeds in `K(w)` when `w ≠ 1`, is not proved anywhere in this
repository. -/
theorem rabin_trivial_of_word_eq_one
    (hw : PresentedGroup.mk ((R : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) w = 1) :
    Subsingleton (RabinGroup R w) := by
  have hall : ∀ x : RabinGroup R w, x = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := PresentedGroup.mk_surjective _ x
    induction v using FreeGroup.induction_on with
    | C1 => exact map_one _
    | of g => exact generator_eq_one_of_word_eq_one R w hw g
    | inv_of g hg => rw [map_inv, hg, inv_one]
    | mul p q hp hq => rw [map_mul, hp, hq, mul_one]
  exact ⟨fun x y ↦ by rw [hall x, hall y]⟩

end Collapse

end RabinConstruction
end GroupApproximation
