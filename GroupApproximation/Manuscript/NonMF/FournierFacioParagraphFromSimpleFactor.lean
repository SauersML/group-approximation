import GroupApproximation.Manuscript.NonMF.FournierFacioParagraph
import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fournier-Facio paragraph, from the construction the manuscript used to print

`non_mf_groups_exist.tex`, `sec:torsion-free`, the opening paragraph:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with
> property (T), a subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with
> `tΓt⁻¹ ≤ Γ`, and a subgroup `J ≤ G₀` isomorphic to a finitely presented
> infinite simple group, such that `[Γ,J] = 1` and `tJt⁻¹ ≤ Γ` [FFF, §2].

`TorsionFreePrinted.FournierFacioParagraph` is that sentence as one closed
proposition, and it is a hypothesis of `thm:torsion-free`, of
`cor:relative-quotient` and of `cor:regular-nonmf-algebra`.  Nothing inhabits
it.

This module reduces it.  **The construction is not new: it is the one the
manuscript itself printed until the current draft**, and this repository already
formalizes it — `TheoremC.LiteratureInputs` and `TheoremC.exists_configuration`.
The earlier text read

> Following Fournier-Facio [FFF, §2], let `U` be a universal finitely presented
> torsion-free group … and let `H₀` be a torsion-free hyperbolic group with
> property (T), obtained from the density model at a parameter between `1/3`
> and `1/2`

and built `G₀` from `U`, `H₀`, a small-cancellation quotient `P`, a double HNN
extension `E` and Hull's Corollary 7.4.  The current draft replaced all of that
by the single citation of §2.

## The one thing the earlier route gives up, and how to get it back

`TheoremC.exists_configuration` produces a `TheoremC.Configuration`, whose
`Witness` is `FreeCommutatorWitness = F₂`.  The header of
`Manuscript/NonMF/FournierFacioInput.lean` says why:

> The protected element is the explicit nonidentity commutator of the two free
> generators.  This removes the infinite-simple-group input: the later argument
> saturates the normal closure of the image of `[F₂,F₂]` directly.

So a `Configuration` cannot be a `PrintedFournierFacioData`: `F₂` is not simple.
It is otherwise a *stronger* object than the printed paragraph asks for, and the
gap closes in one move.

**Take `Γ` to be `t · core(P) · t⁻¹`, not `core(P)`.**  A `Configuration` records

* `t_compresses` — `t · core(p) · t⁻¹ = core(q)`, so the *conjugated* core is
  again compressed by `t`;
* `witness_commute_conj` — the witness factor commutes with `t · core(p) · t⁻¹`,
  and **not** with `core(p)` itself.  Inside `P₁ × P₂ × W` the third factor
  centralizes the first two, and `t = π(u₁)` conjugates `core(P)` onto the image
  of `P₁`; so the subgroup the witness centralizes is the conjugated one;
* `core_mem_of_witness` — `J ≤ core(P)`, whence `tJt⁻¹ ≤ t · core(P) · t⁻¹ = Γ`.

Those are exactly the three printed relations `tΓt⁻¹ ≤ Γ`, `[Γ,J] = 1` and
`tJt⁻¹ ≤ Γ` at `Γ = t · core(P) · t⁻¹`, and property (T) survives the change
because `Γ` is then the image of `P` under `p ↦ t · core(p) · t⁻¹`, a
homomorphism.  `printedFournierFacioDataOfSimpleFactor` is that bridge; it takes
the three clauses as hypotheses, so it applies to a `Configuration` and to the
existence proof below alike.

The second move is that simplicity turns the earlier route's *protected
element* into an *injective witness*.  `Configuration.distinguished_image_ne_one`
says Hull's quotient does not kill the distinguished element; over a simple
`W` the kernel of the witness map is `⊥` or `⊤`, so one surviving element makes
the whole map injective and `J ≅ W` — which is what *"isomorphic to a finitely
presented infinite simple group"* asks for.  That is
`injective_of_isSimpleGroup_of_map_ne_one`.

## What this costs: nothing that Section 2 does not already cite

`fournierFacioParagraph_of_literatureInputs` proves the paragraph from
`TheoremC.LiteratureInputs` together with `FinitelyPresentedInfiniteSimpleStatement`
— the existence of a finitely presented torsion-free infinite simple group.

**That is not a citation this module adds.  Section 2 makes it itself**, in
these words:

> A finitely presented simple torsion-free group `S`, e.g. a Burger–Mozes
> [BM97] or Hyde–Lodha group [HL25]

and it is an input Section 2 cites rather than a group Section 2 constructs.  So
the reduction below *surfaces* an input of the source; it does not trade one
citation for another, and an earlier version of this header said otherwise.  See
"Provenance" at the end for exactly how well that sentence is attested.

Section 2 is therefore replaced by

* Chiodo — `TheoremC.chiodo`, from Higman's ω-closure.  **Closed**;
* Kotowski–Kotowski and Ollivier–Wise, the density model — an admitted proof,
  `TheoremC.kotowskiOllivier`, one of the five open admissions of
  `TheoremCAssembly`;
* Fournier-Facio et al., Proposition 2.3 with Osin's Theorem 2.4(5) —
  `TheoremC.smallCancellationQuotient`, from Hull's one-step small cancellation
  over the free product.  Reduced, **not closed**: it consumes
  `TorsionFree.hullLemma44FamilyInclusion`, which routes through
  `hullLemma44FamilyInclusionJoint`, of which `TheoremCAssembly` says in so many
  words *"Reports `sorryAx`, inherited from the four admissions it is assembled
  from"*;
* Minasyan–Osin at `E` — `TheoremC.minasyanOsin`, down to Osin's Theorem 1.2,
  which is `GGT.Elementary.osinTheorem12_unconditional`.  **Closed**;
* Hull, Corollary 7.4 — `TheoremC.hullCommonQuotient`, from
  `TorsionFree.hullOneStep` and a free-product geometry that is unconditional.
  Reduced to Hull's Theorem 7.1 for one relator, **not closed**: `hullOneStep`
  rests on the same four §5/§6 admissions;
* a finitely presented torsion-free infinite simple group — stated here as
  `FinitelyPresentedInfiniteSimpleStatement`, and **cited by Section 2 too**,
  so it is new to this development but not to the argument.

So two of the five are closed and three are not, and supplying
`TheoremC.literatureInputs` for `I` is a reduction rather than a discharge.  The
four §5/§6 admissions are the leaves of Hull's Theorem 7.1, so what
`sec:torsion-free` is really waiting on, after this module, is Hull's Theorem 7.1
and the density model.

What this establishes is that the paragraph is **not** an irreducible input: it
is the earlier printed construction with a simple third factor, and every step
of it that this repository had already proved for the earlier text still
applies.  Whether the manuscript should say so is an editorial question and this
module does not answer it — but the question is *not* "keep simplicity and pay a
new citation, or drop simplicity and pay nothing".  It is "state Section 2's own
input, or depart from Section 2 and cite the author's earlier construction
instead", because the route that dispenses with the simple factor is the `F₂`
one, which is this manuscript's earlier text and not Fournier-Facio's.

## Two further readings of Section 2, recorded and not acted on

* Section 2 uses **two** stable letters `t₁, t₂` with `tᵢΓtᵢ⁻¹ ⊆ Γ` where
  `sec:torsion-free` prints one `t`.  Having one is weaker than having two, so
  the print is a sound weakening of the source rather than a defect, and
  `PrintedFournierFacioData` carrying a single `t` is right.
* The docstring of `TheoremC.LiteratureInputs.smallCancellationQuotient`
  attributes its content to "**Fournier-Facio et al., Proposition 2.3**".  The
  plural *et al.* does not match `[FFF]`, which is single-author, so that
  docstring is most likely naming a **different** Fournier-Facio paper; that
  inference is from the text of the docstring itself.  A one-source enumeration
  of `[FFF]`'s numbered statements returned only Theorem 1.1, Proposition 1.2
  and Theorem 1.3, which would agree — but one source is not enough to assert
  that `[FFF]` lacks a Proposition 2.3, and this module does not assert it.
  The note belongs next to that docstring in
  `Manuscript/NonMF/FournierFacioInput.lean`; it is here because that file is
  not this lane's to edit.

## Provenance of the Section 2 readings

Everything this header says about `[FFF]` comes from **one source**: WebFetch
over the arXiv HTML of `arXiv:2608.02025v1`, not from reading the PDF.  The
quoted sentence introducing `S` is verbatim and is the load-bearing one; the
surrounding argument of Section 2 was not read, and the two readings in the
previous section are one-source too.  Nothing in the Lean below depends on any
of it — `FinitelyPresentedInfiniteSimpleStatement` is a hypothesis either way,
and these paragraphs change only what the reduction is worth, not what it
proves.

## What is *not* claimed

This is not a formalization of Fournier-Facio's own §2.  It is a proof of the
*statement* that §2 is cited for, along the route the manuscript used to print,
and the group `G₀` it produces need not be the one §2 constructs.  For
`thm:torsion-free` that is all that is used: the theorem consumes the paragraph
only through `FournierFacioParagraph`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

/-! ## The compressed core `Γ = t · core(C) · t⁻¹` -/

/-- **The printed `Γ`.**  The image of the core under conjugation by `t`, which
is `t · core(C) · t⁻¹` — the same spelling `PrintedFournierFacioData.conjFactor`
uses for the printed `S = tJt⁻¹`. -/
def compressedCore {G₀ C : Type} [Group G₀] [Group C] (core : C →* G₀)
    (t : G₀) : Subgroup G₀ :=
  core.range.map (MulAut.conj t).toMonoidHom

/-- Membership in `Γ`, unfolded: its elements are exactly the `t · core(p) · t⁻¹`. -/
theorem mem_compressedCore_iff {G₀ C : Type} [Group G₀] [Group C]
    {core : C →* G₀} {t : G₀} {x : G₀} :
    x ∈ compressedCore core t ↔ ∃ p : C, t * core p * t⁻¹ = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
    exact ⟨p, by rw [hp]; exact hyx⟩
  · rintro ⟨p, rfl⟩
    exact Subgroup.mem_map.mpr ⟨core p, MonoidHom.mem_range.mpr ⟨p, rfl⟩, rfl⟩

/-- **`Γ` has property (T) when the core does.**  `Γ` is the range of
`p ↦ t · core(p) · t⁻¹`, so it is a quotient of `C`. -/
theorem hasKazhdanPropertyT_compressedCore {G₀ C : Type} [Group G₀] [Group C]
    (core : C →* G₀) (t : G₀) (hC : HasKazhdanPropertyT.{0, 0} C) :
    HasKazhdanPropertyT.{0, 0} ↥(compressedCore core t) := by
  have hrange : ((MulAut.conj t).toMonoidHom.comp core).range
      = compressedCore core t := by
    rw [MonoidHom.range_comp]
    rfl
  rw [← hrange]
  exact HasKazhdanPropertyT.of_surjective
    ((MulAut.conj t).toMonoidHom.comp core).rangeRestrict
    ((MulAut.conj t).toMonoidHom.comp core).rangeRestrict_surjective hC

/-! ## One surviving element makes a map out of a simple group injective -/

/-- **A homomorphism out of a simple group that does not kill one element is
injective.**  Its kernel is normal, so it is `⊥` or `⊤`, and `⊤` would kill
everything.

This is what turns the earlier route's *protected element* — Hull's quotient is
injective on a prescribed finite set — into the printed *"isomorphic to a
finitely presented infinite simple group"*. -/
theorem injective_of_isSimpleGroup_of_map_ne_one {W G₀ : Type} [Group W]
    [Group G₀] [IsSimpleGroup W] (witness : W →* G₀) {w : W}
    (hw : witness w ≠ 1) : Function.Injective witness := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal witness.ker inferInstance with
    h | h
  · exact h
  · refine absurd ?_ hw
    have hmem : w ∈ witness.ker := by
      rw [h]
      exact Subgroup.mem_top w
    exact MonoidHom.mem_ker.mp hmem

/-! ## The bridge -/

/-- **The printed datum `(Γ, t, J)`, from the three clauses a
`TheoremC.Configuration` records.**

`Γ` is `t · core(C) · t⁻¹` and `J` is the range of the witness map.  The three
hypotheses are `Configuration.t_compresses`, `Configuration.core_mem_of_witness`
and `Configuration.witness_commute_conj` verbatim, and `hw` is
`Configuration.distinguished_image_ne_one`.

The `nonabelian` field is not asked for: `printedFournierFacioDataOfInfiniteSimple`
derives it from *infinite simple*, exactly as the printed paragraph does. -/
noncomputable def printedFournierFacioDataOfSimpleFactor {G₀ C W : Type}
    [Group G₀] [Group C] [Group W] [IsSimpleGroup W] [Infinite W]
    (core : C →* G₀) (witness : W →* G₀) (t : G₀)
    (hcompress : ∀ p : C, ∃ q : C, t * core p * t⁻¹ = core q)
    (hmem : ∀ x : W, ∃ p : C, witness x = core p)
    (hcomm : ∀ (x : W) (p : C), Commute (witness x) (t * core p * t⁻¹))
    {w : W} (hw : witness w ≠ 1) : PrintedFournierFacioData G₀ :=
  printedFournierFacioDataOfInfiniteSimple (compressedCore core t) t witness.range
    -- `tΓt⁻¹ ≤ Γ`
    (by
      intro γ hγ
      obtain ⟨p, hp⟩ := mem_compressedCore_iff.mp hγ
      obtain ⟨q, hq⟩ := hcompress p
      refine mem_compressedCore_iff.mpr ⟨q, ?_⟩
      rw [← hq, hp])
    -- `[Γ, J] = 1`
    (by
      rintro c hc γ hγ
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc
      obtain ⟨p, rfl⟩ := mem_compressedCore_iff.mp hγ
      exact hcomm x p)
    -- `tJt⁻¹ ≤ Γ`
    (by
      rintro c hc
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc
      obtain ⟨p, hp⟩ := hmem x
      rw [hp]
      exact mem_compressedCore_iff.mpr ⟨p, rfl⟩)
    -- `J` is simple, and infinite, because the witness map is injective
    ((MonoidHom.ofInjective
      (injective_of_isSimpleGroup_of_map_ne_one witness hw)).symm.isSimpleGroup)
    (Infinite.of_injective _ (MonoidHom.ofInjective
      (injective_of_isSimpleGroup_of_map_ne_one witness hw)).injective)

@[simp]
theorem printedFournierFacioDataOfSimpleFactor_core {G₀ C W : Type}
    [Group G₀] [Group C] [Group W] [IsSimpleGroup W] [Infinite W]
    (core : C →* G₀) (witness : W →* G₀) (t : G₀)
    (hcompress : ∀ p : C, ∃ q : C, t * core p * t⁻¹ = core q)
    (hmem : ∀ x : W, ∃ p : C, witness x = core p)
    (hcomm : ∀ (x : W) (p : C), Commute (witness x) (t * core p * t⁻¹))
    {w : W} (hw : witness w ≠ 1) :
    (printedFournierFacioDataOfSimpleFactor core witness t hcompress hmem hcomm
      hw).core = compressedCore core t := rfl

@[simp]
theorem printedFournierFacioDataOfSimpleFactor_simpleFactor {G₀ C W : Type}
    [Group G₀] [Group C] [Group W] [IsSimpleGroup W] [Infinite W]
    (core : C →* G₀) (witness : W →* G₀) (t : G₀)
    (hcompress : ∀ p : C, ∃ q : C, t * core p * t⁻¹ = core q)
    (hmem : ∀ x : W, ∃ p : C, witness x = core p)
    (hcomm : ∀ (x : W) (p : C), Commute (witness x) (t * core p * t⁻¹))
    {w : W} (hw : witness w ≠ 1) :
    (printedFournierFacioDataOfSimpleFactor core witness t hcompress hmem hcomm
      hw).simpleFactor = witness.range := rfl

/-! ## The paragraph, from a configuration with a simple witness -/

/-- **`FournierFacioParagraph` from a `TheoremC.Configuration` whose witness
factor is a finitely presented infinite simple group.**

Every field of the paragraph comes off the configuration: the four adjectives on
`G₀` are `fpAmbient`, `torsionFreeAmbient`, `kazhdanAmbient` and `acylAmbient`;
`Γ`, `t` and `J` are the bridge above; property (T) of `Γ` is property (T) of
`Core` transported along `p ↦ t · core(p) · t⁻¹`; and finite presentation and
infinitude of `J` come from `W` along the isomorphism `W ≅ J`.

Nothing else is used, and in particular `distinguished_mem_commutator` is not:
that field belongs to the earlier route's saturation argument, not to the
printed paragraph. -/
theorem fournierFacioParagraph_of_configuration (C : Configuration)
    [IsSimpleGroup C.Witness] [Infinite C.Witness]
    [Group.IsFinitelyPresented C.Witness] : FournierFacioParagraph := by
  have hinj : Function.Injective C.witness :=
    injective_of_isSimpleGroup_of_map_ne_one C.witness C.distinguished_image_ne_one
  refine ⟨C.Ambient, C.groupAmbient, C.fpAmbient, C.torsionFreeAmbient,
    C.kazhdanAmbient, C.acylAmbient,
    printedFournierFacioDataOfSimpleFactor C.core C.witness C.t C.t_compresses
      C.core_mem_of_witness C.witness_commute_conj C.distinguished_image_ne_one,
    ?_, ?_, ?_⟩
  · rw [printedFournierFacioDataOfSimpleFactor_core]
    exact hasKazhdanPropertyT_compressedCore C.core C.t C.kazhdanCore
  · rw [printedFournierFacioDataOfSimpleFactor_simpleFactor]
    exact Group.IsFinitelyPresented.equiv (MonoidHom.ofInjective hinj)
  · rw [printedFournierFacioDataOfSimpleFactor_simpleFactor]
    exact Infinite.of_injective _ (MonoidHom.ofInjective hinj).injective

/-! ## The one new citation -/

/-- **A finitely presented, torsion-free, infinite simple group.**

Burger–Mozes, *Lattices in product of trees*, Publ. Math. IHÉS 92 (2000): the
irreducible cocompact lattices in a product of two trees include finitely
presented torsion-free simple groups.  Fournier-Facio's Section 2 cites this
statement itself, naming Burger–Mozes **or a Hyde–Lodha group** as admissible
witnesses, so this proposition is that paper's input and not an extra one.

Hyde–Lodha is likely the cheaper road for anyone who attacks this statement —
finitely presented simple groups of homeomorphisms of the line, left-orderable
and so torsion-free, with no product-of-trees lattices and no Margulis-type
normal subgroup theorem to build first.  **That is a recollection of what those
groups are, not something read in either paper**, and it is recorded as a
direction to survey rather than as a claim.  Infinitude is not a separate assertion —
a simple group that is not infinite is finite — but it is stated because the
printed paragraph states it, and because a *finite* simple group would satisfy
every other clause vacuously in the wrong direction.

This is the whole of what `fournierFacioParagraph_of_literatureInputs` needs
beyond `TheoremC.LiteratureInputs`. -/
def FinitelyPresentedInfiniteSimpleStatement : Prop :=
  ∃ (W : Type) (_ : Group W), Group.IsFinitelyPresented W ∧
    IsPowerTorsionFree W ∧ IsSimpleGroup W ∧ Infinite W

/-! ## The paragraph, assembled -/

/-- **`FournierFacioParagraph` from the earlier printed construction.**

The script is `TheoremC.exists_configuration`'s, with the witness factor `W`
taken from `hW` instead of being `FreeCommutatorWitness = F₂`, and with the
output assembled as a `PrintedFournierFacioData` rather than as a
`Configuration`.  Each step is the corresponding printed sentence of the earlier
text:

* `I.chiodo` gives the universal finitely presented torsion-free `U`;
* `I.kotowskiOllivier` gives the density-model group `H₀`;
* `I.smallCancellationQuotient` gives `P`, a finitely presented torsion-free
  quotient of `H₀` containing `U`;
* property (T) of `P` is `kazhdan_of_fournierFacioQuotient`, universality of `P`
  is `containsEveryFPTorsionFree_of_fournierFacioQuotient`, and the embedding
  `P × P × W ↪ P` is `exists_injective_prodProdWitness`;
* `E = Skeleton f hf` is the double HNN extension, finitely presented and
  torsion-free by `skeleton_isFinitelyPresented` and `skeleton_torsionFree`, and
  acylindrically hyperbolic by `I.minasyanOsin`;
* `I.hullCommonQuotient` gives `π : E ↠ G₀` injective on the protected pair
  `{1, ι(f(1,1,w))}`, which is what keeps the witness image nontrivial and hence,
  by simplicity of `W`, keeps the witness map injective.

`Γ` is `t · π(ι(P)) · t⁻¹` with `t = π(u₁)`, and `J` is `π(ι(f(1,1,W)))`. -/
theorem fournierFacioParagraph_of_literatureInputs (I : LiteratureInputs)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : FournierFacioParagraph := by
  classical
  obtain ⟨W, instW, hWfp, hWtf, hWsimple, hWinf⟩ := hW
  letI := instW
  haveI := hWfp
  haveI := hWsimple
  haveI := hWinf
  obtain ⟨U, instU, hUfp, hUtf, hUuniv⟩ := I.chiodo
  obtain ⟨H₀, instH₀, hH₀inf, hH₀fp, hH₀tf, hH₀hyp, hH₀T⟩ := I.kotowskiOllivier
  obtain ⟨P, instP, hPfp, hPtf, ⟨quot, hquot⟩, ⟨emb, hemb⟩⟩ :=
    I.smallCancellationQuotient H₀ U instH₀ instU hH₀inf hH₀fp hH₀tf
      hH₀hyp hH₀T hUfp hUtf
  letI := instU
  letI := instH₀
  letI := instP
  haveI := hPfp
  -- "Consequently, `P` has property (T)."
  have hPT : HasKazhdanPropertyT.{0, 0} P :=
    kazhdan_of_fournierFacioQuotient hH₀T quot hquot
  -- By universality, `P` contains a subgroup `P₁ × P₂ × W`.
  have hPuniv : ChiodoBelegradek.ContainsEveryFPTorsionFree P :=
    containsEveryFPTorsionFree_of_fournierFacioQuotient hUuniv emb hemb
  obtain ⟨f, hf⟩ :=
    exists_injective_prodProdWitness (P := P) (W := W) hPtf hWtf hPuniv
  -- `E`, the double HNN extension, and its three printed properties.
  have hEfp : Group.IsFinitelyPresented (Skeleton f hf) :=
    skeleton_isFinitelyPresented f hf
  have hEtf : IsPowerTorsionFree (Skeleton f hf) := skeleton_torsionFree f hf hPtf
  let groupSkeleton : Group (Skeleton f hf) := inferInstance
  have hEacyl : TorsionFree.IsAcylindricallyHyperbolic (Skeleton f hf) :=
    I.minasyanOsin P W instP instW f hf
  -- a nonidentity element of `W`, to be protected by Hull's injectivity
  obtain ⟨w, hw1⟩ := exists_ne (1 : W)
  obtain ⟨G₀, instG₀, pi, -, hG₀fp, hG₀tf, hG₀T, hG₀acyl, hinj⟩ :=
    I.hullCommonQuotient (Skeleton f hf) groupSkeleton H₀ instH₀ hEfp hEtf hEacyl
      hH₀inf hH₀fp hH₀tf hH₀hyp hH₀T
      {1, skeletonIota f hf (factorSimple f w)}
  letI := instG₀
  haveI := hG₀fp
  have hmem1 : (1 : Skeleton f hf) ∈
      ((({1, skeletonIota f hf (factorSimple f w)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  have hmemw : skeletonIota f hf (factorSimple f w) ∈
      ((({1, skeletonIota f hf (factorSimple f w)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  -- Hull's injectivity on the protected pair keeps the witness image nontrivial.
  have hne : pi (skeletonIota f hf (factorSimple f w)) ≠ 1 := by
    intro hz
    have h1 : pi (skeletonIota f hf (factorSimple f w)) = pi 1 := by
      rw [hz, map_one]
    have h2 := hinj hmemw hmem1 h1
    apply hw1
    apply factorSimple_injective f hf
    apply skeletonIota_injective f hf
    rw [h2, map_one, map_one]
  -- The compression relation, transported through `π`.
  have hconj : ∀ p : P, pi (skeletonU₁ f hf) *
      (pi.comp (skeletonIota f hf)) p * (pi (skeletonU₁ f hf))⁻¹
        = (pi.comp (skeletonIota f hf)) (factorOne f p) := by
    intro p
    have h := congrArg pi (skeleton_conj_u₁ f hf p)
    simpa using h
  set core : P →* G₀ := pi.comp (skeletonIota f hf) with hcore
  set witness : W →* G₀ := (pi.comp (skeletonIota f hf)).comp (factorSimple f)
    with hwitness
  set t : G₀ := pi (skeletonU₁ f hf) with ht
  have hcompress : ∀ p : P, ∃ q : P, t * core p * t⁻¹ = core q :=
    fun p => ⟨factorOne f p, hconj p⟩
  have hmemcore : ∀ x : W, ∃ p : P, witness x = core p :=
    fun x => ⟨factorSimple f x, rfl⟩
  have hcomm : ∀ (x : W) (p : P), Commute (witness x) (t * core p * t⁻¹) := by
    intro x p
    rw [hconj p]
    exact (factorSimple_commute_factorOne f x p).map (pi.comp (skeletonIota f hf))
  have hwne : witness w ≠ 1 := hne
  have hwinj : Function.Injective witness :=
    injective_of_isSimpleGroup_of_map_ne_one witness hwne
  refine ⟨G₀, instG₀, hG₀fp, hG₀tf, hG₀T, hG₀acyl,
    printedFournierFacioDataOfSimpleFactor core witness t hcompress hmemcore
      hcomm hwne, ?_, ?_, ?_⟩
  · rw [printedFournierFacioDataOfSimpleFactor_core]
    exact hasKazhdanPropertyT_compressedCore core t hPT
  · rw [printedFournierFacioDataOfSimpleFactor_simpleFactor]
    exact Group.IsFinitelyPresented.equiv (MonoidHom.ofInjective hwinj)
  · rw [printedFournierFacioDataOfSimpleFactor_simpleFactor]
    exact Infinite.of_injective _ (MonoidHom.ofInjective hwinj).injective

/-! ## The axioms

`fournierFacioParagraph_of_literatureInputs` takes both of its inputs as
hypotheses, so `#audit_closed_axioms` does not apply; `#audit_axioms` reports
that nothing else reaches it.  `TheoremC.literatureInputs` itself rests on the
five open admissions of `Manuscript/NonMF/TheoremCAssembly.lean`, and this module
does not import that file, so no `sorryAx` enters here. -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.injective_of_isSimpleGroup_of_map_ne_one

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.hasKazhdanPropertyT_compressedCore

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.fournierFacioParagraph_of_configuration

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.fournierFacioParagraph_of_literatureInputs

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation
