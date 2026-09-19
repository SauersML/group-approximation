import GroupApproximation.Sofic.ContainsSquareWitness
import GroupApproximation.Monsters.UniversalFinitelyPresentedTorsionFreeGroup

/-!
# `KC.21`: Fournier-Facio's universal group, resolved into its inputs

`non_mf_groups_exist.tex`, `\begin{remark}[a small-cancellation realization]`
(`\label{rem:ff-realization}`), opens with a citation:

> His finitely presented torsion-free property-`(T)` group `P` contains every
> finitely presented torsion-free group, in particular a direct product
> `P₁ × P₂` with `Pᵢ ≅ P`.

Everything the remark deduces *from* that sentence is proved elsewhere and
unconditionally: `Sofic.RealizationFromUniversalGroup` (rows `KC.22`, `KC.23`)
runs the Kazhdan--Clifford construction off the extracted datum, and
`Sofic.ContainsSquareWitness` proves the *"in particular"* and settles that
the datum is satisfiable.  **The sentence itself was carried as a single
opaque input, `ContainsSquareWitness.UniversalFPTorsionFree`, and this module
takes that input apart.**

## What is new here

The existence statement is not one theorem, it is a composite of two, and the
step that joins them is not a citation.  Fournier-Facio, arXiv:2608.02025 §2,
builds `P` as follows (the reading is recorded in
`research/fournier-facio-torsion-free-skeleton-proof.md`, verified from the
full text):

1. take `U`, a **finitely presented torsion-free group universal for finitely
   presented torsion-free groups** (Chiodo, arXiv:1107.1489v4, Theorem 3.10,
   which is Belegradek's Theorem A.1 in the appendix to Belegradek--
   Szczepanski);
2. embed `U` into a **finitely presented torsion-free group `P` with property
   `(T)`**, by small cancellation over the relatively hyperbolic pair
   `(U * H, U)` with `H` a torsion-free hyperbolic Kazhdan group (Osin's
   small cancellation over relatively hyperbolic groups, Theorem 2.4.5, whose
   torsion-preservation clause is what keeps `P` torsion-free);
3. observe that `P` is then universal, because `U` is and `U` embeds in `P`.

Step 3 is an inference, it is the step that produces the printed sentence,
and it is `universal_comp` below — proved, in three lines, with no hypothesis
at all beyond the two it composes.  Steps 1 and 2 are the literature, and
they are carried here as the two typed inputs `UniversalTorsionFreeHost` and
`KazhdanEnvelope`.  `UniversalKazhdanGroup.ofInputs` is the composite, so
that

    KC.21  =  Chiodo/Belegradek  +  Osin small cancellation  +  one proof.

`Sofic.SmallCancellationKazhdanEnvelope` then takes input 2 apart in the same
way: the small-cancellation route is a *common quotient* of `U * H`, and
property `(T)` of the envelope is not postulated there but **derived** from
the hyperbolic partner's `(T)` through the second epimorphism.  That module
is proof-ledger row `LI.12b`.

## What is proved here, and what is not

Proved, unconditionally:

* `universal_comp` --- universality transfers along an injective
  homomorphism.  This is the whole of step 3.
* `UniversalKazhdanGroup.toHost` and `.toEnvelope`, with
  `ofInputs_toHost_toEnvelope` --- the split is *faithful*: the two inputs
  together are exactly `KC.21`, since Fournier-Facio's group is its own host
  and its own envelope.  So nothing was strengthened in the reading.
* `containsEveryFiniteRankFreeGroup` --- free groups of every finite rank sit
  inside `P`, in the `Monsters` lane's own vocabulary.
* `exists_ne_one_of_universal` --- a universal group is nontrivial, because
  `Multiplicative ℤ` is finitely presented and torsion-free.  The remark
  needs `a ≠ 1` and never says where it comes from.
* `nonempty_containsSquare` --- the remark's *"in particular"*, in the
  vocabulary of this module (`P × P` is finitely presented by this
  repository's `ProductFinitePresentation.instProd` and torsion-free by
  `IsPowerTorsionFree.prod`).
* `realization_of_universalKazhdanGroup` --- the entire remark, off a
  `UniversalKazhdanGroup` and nothing else: a finitely presented group with a
  nontrivial central involution that is not `CDE`-operator-MF.
* `universal_of_embedding_universalPayload` --- **a reduction of input 1 to a
  bare embedding statement.**  This repository already builds, with no
  hypothesis whatever, a countable torsion-free group containing every
  finitely presented torsion-free group
  (`Monsters.UniversalFinitelyPresentedTorsionFreeGroup`).  So what input 1
  owes the literature is not universality --- that half is already
  unconditional here --- but only the *upgrade to finite presentation*: any
  injection of that explicit group into a finitely presented torsion-free
  group discharges input 1 outright.  This does **not** discharge it: the
  explicit group is a restricted direct product over a non-recursive index
  set, so it is not recursively presented and Higman's theorem (or Chiodo's
  torsion-order-preserving refinement, `torsion-free-higman-embedding`) does
  not apply to it as it stands.  The declaration records what shape of
  embedding theorem would suffice.

Not proved, and not provable from anything in this repository:

* `UniversalTorsionFreeHost` --- Chiodo Theorem 3.10 / Belegradek Theorem
  A.1.  **Nothing inhabits it.**  It is, since 2026-08-19, no longer an
  irreducible input either: `Sofic.ChiodoUniversalHost` derives it from one
  embedding of one explicit group into a finitely presented torsion-free
  group, which is Chiodo's Theorem 2.2 applied once, and proves every other
  clause of Theorem 3.10 unconditionally.
* `KazhdanEnvelope` --- the small-cancellation step of `\cite[\S2]{FFF}`.
  **Nothing inhabits it.**

## A note for the corpus audit, recorded rather than left to be found

`scripts/check_non_mf_unconditional.py --audit-corpus` will now carry three
further undischarged names --- `UniversalTorsionFreeHost`, `KazhdanEnvelope`,
`UniversalKazhdanGroup` --- where before it carried one,
`UniversalFPTorsionFree`.  That is the intended reading: the literature
dependency has been *split*, not increased, and each of the three names says
which half of the citation it is.  A fourth name joined the list on
2026-08-19, `ChiodoHost.TorsionFreeHigmanHull`, and it is a *replacement* for
half of `UniversalTorsionFreeHost` rather than an addition: the host is now
produced by `ChiodoHost.universalTorsionFreeHost` from that one structure, so
the producer fixpoint keeps the host undischarged exactly as long as the hull
is, and the hull is the smaller statement --- one embedding of one named
group, instead of an existence claim quantified over every finitely presented
torsion-free group.  `UniversalFPTorsionFree` remains on the
list and is now also reachable from here, through
`universalFPTorsionFree_of_universalKazhdanGroup`, so no consumer of the old
input is orphaned.

Two shapes are avoided deliberately, both of which would make the audit
report the inputs as discharged when they are not (see
`scripts/check_non_mf_unconditional.py`'s producer fixpoint).  No declaration
here concludes an input structure from premises that are bare logical
formulas: `universal_comp` and `universal_of_embedding_universalPayload`
conclude the universality *formula*, never a packaged input, so a reader who
has an embedding must assemble the input by hand and the audit keeps seeing
it as open.  And no statement here is an `↔` between two of these names.
-/

namespace GroupApproximation
namespace FournierFacioUniversal

open RealizationFromUniversalGroup KazhdanCliffordConstruction

/-! ## 1.  Universality, and the one law it obeys -/

/-- **The step that produces the printed sentence.**  If `U` contains a copy
of every finitely presented torsion-free group, and `U` embeds in `P`, then
`P` contains a copy of every finitely presented torsion-free group.

This is step 3 of Fournier-Facio's construction, and it is the reason the
envelope of a universal group is again universal.  It assumes nothing about
`P` --- not finite presentation, not torsion-freeness, not property `(T)` ---
which is why the three properties of `P` in `KC.21` all come from the
envelope and none of them from universality. -/
theorem universal_comp {U P : Type} [Group U] [Group P]
    (hU : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* U, Function.Injective f)
    (g : U →* P) (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f := by
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := hU Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

/-- **A universal group is nontrivial.**  `Multiplicative ℤ` is finitely
presented and torsion-free, so it embeds, and it has a nonidentity element.

The remark says "any `a ∈ P₂ ∖ {1}`" without saying why `P₂ ∖ {1}` is
inhabited; this is the missing half-line. -/
theorem exists_ne_one_of_universal {P : Type} [Group P]
    (huniv : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f) :
    ∃ b : P, b ≠ 1 := by
  obtain ⟨f, hf⟩ :=
    huniv (Multiplicative ℤ) IsPowerTorsionFree.of_isMulTorsionFree
  refine ⟨f (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
  intro hone
  have hx : (Multiplicative.ofAdd (1 : ℤ)) = 1 :=
    hf (hone.trans (map_one f).symm)
  have hz := congrArg (fun x : Multiplicative ℤ ↦ Multiplicative.toAdd x) hx
  change (1 : ℤ) = 0 at hz
  exact one_ne_zero hz

/-! ## 2.  The two literature inputs

Neither structure is inhabited anywhere in this repository, and neither is
postulated.  Every declaration in section 3 takes them as explicit
arguments. -/

/-- **Input 1: a finitely presented torsion-free universal group.**

Chiodo, arXiv:1107.1489v4, Theorem 3.10, which is Theorem A.1 of Belegradek's
appendix to Belegradek--Szczepanski; it is the form Fournier-Facio uses as
the first input of arXiv:2608.02025 §2.  Chiodo's Theorem 3.9 is strictly
stronger --- one finitely presented torsion-free group absorbing every
countably generated *recursively presentable* torsion-free group --- and this
is the weaker form, because it is all the construction consumes.

**Nothing inhabits this structure**, but it is no longer an *input*:
`Sofic.ChiodoUniversalHost.universalTorsionFreeHost` builds one from a single
embedding of one explicit group, `Monsters.ChiodoAbsorber`, into a finitely
presented torsion-free group --- Chiodo's Theorem 2.2 applied once.  What is
owed to the literature at this node is therefore that one embedding and
nothing else; every other clause of Theorem 3.10 is proved there.

`universal_of_embedding_universalPayload` below is the older form of the same
reduction and is superseded: its payload is indexed by an undecidable set, so
Theorem 2.2 cannot be applied to it.  The note on that declaration says why,
and `Sofic.ChiodoUniversalHost` says how the obstruction is removed. -/
structure UniversalTorsionFreeHost where
  /-- The universal finitely presented torsion-free group `U`. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  /-- `U` is torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- `U` contains a copy of every finitely presented torsion-free group. -/
  universal : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
    IsPowerTorsionFree Q → ∃ f : Q →* Carrier, Function.Injective f

instance hostGroup (H : UniversalTorsionFreeHost) : Group H.Carrier :=
  H.groupCarrier

instance hostFinitelyPresented (H : UniversalTorsionFreeHost) :
    Group.IsFinitelyPresented H.Carrier :=
  H.finitelyPresentedCarrier

/-- **Input 2: the Kazhdan envelope of a finitely presented torsion-free
group.**  A finitely presented torsion-free property-`(T)` group containing
`U`.

This is the small-cancellation step of `\cite[\S2]{FFF}`: `U * H` is
hyperbolic relative to `U` for `H` a torsion-free hyperbolic Kazhdan group,
and a small-cancellation quotient of it in the sense of Osin keeps `U`
embedded and keeps torsion-freeness (Osin, *Small cancellations over
relatively hyperbolic groups and embedding theorems*, Theorem 2.4.5).

**Nothing inhabits this structure.**  `Sofic.SmallCancellationKazhdanEnvelope`
resolves it one level further, into the common-quotient shape in which
property `(T)` is derived rather than assumed; that is where the route's own
clause list lives, and it is proof-ledger row `LI.12b`.

Note what is *not* asked for: no relation between `U` and the envelope beyond
one injective homomorphism, and no property of `U` at all.  The construction
downstream uses the envelope only through `emb`. -/
structure KazhdanEnvelope (U : Type) [Group U] where
  /-- The envelope `P`. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  /-- Osin's torsion-preservation clause. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- The envelope has property `(T)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier
  /-- `U` sits inside the envelope. -/
  emb : U →* Carrier
  /-- The peripheral subgroup really embeds. -/
  emb_injective : Function.Injective emb

instance envelopeGroup {U : Type} [Group U] (E : KazhdanEnvelope U) :
    Group E.Carrier :=
  E.groupCarrier

instance envelopeFinitelyPresented {U : Type} [Group U]
    (E : KazhdanEnvelope U) : Group.IsFinitelyPresented E.Carrier :=
  E.finitelyPresentedCarrier

/-! ## 3.  `KC.21` as the composite -/

/-- **The statement of `KC.21`.**  A finitely presented torsion-free group
with property `(T)` containing a copy of every finitely presented torsion-free
group.

This is the object the remark's first sentence asserts to exist.  It is a
*conclusion* here, not an input: `ofInputs` builds one from the two inputs of
section 2, and nothing else in this repository builds one. -/
structure UniversalKazhdanGroup where
  /-- Fournier-Facio's group `P`. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  /-- `P` is torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- `P` has property `(T)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier
  /-- `P` contains a copy of every finitely presented torsion-free group. -/
  universal : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
    IsPowerTorsionFree Q → ∃ f : Q →* Carrier, Function.Injective f

instance universalGroupGroup (P : UniversalKazhdanGroup) :
    Group P.Carrier :=
  P.groupCarrier

instance universalGroupFinitelyPresented (P : UniversalKazhdanGroup) :
    Group.IsFinitelyPresented P.Carrier :=
  P.finitelyPresentedCarrier

/-- **Fournier-Facio's theorem, from its two inputs.**  A universal finitely
presented torsion-free group, placed inside a Kazhdan envelope, is a finitely
presented torsion-free property-`(T)` group that is still universal.

The three properties come from the envelope; universality comes from the host
through `universal_comp`, which is the only mathematics in this declaration
and is the step the printed sentence hides.  Torsion-freeness of the host is
carried but not consumed here: the construction needs it in order to *apply*
the small-cancellation step, which is why it is a field of the host rather
than a hypothesis of this composition. -/
def UniversalKazhdanGroup.ofInputs (H : UniversalTorsionFreeHost)
    (E : KazhdanEnvelope H.Carrier) : UniversalKazhdanGroup where
  Carrier := E.Carrier
  groupCarrier := E.groupCarrier
  finitelyPresentedCarrier := E.finitelyPresentedCarrier
  torsionFree := E.torsionFree
  kazhdan := E.kazhdan
  universal := universal_comp H.universal E.emb E.emb_injective

/-- The composite changes nothing but the label: Fournier-Facio's group *is*
the envelope, and the host survives only as the source of its universality.
Recorded so that a reader can see the composite carries no hidden
construction. -/
@[simp]
theorem ofInputs_carrier (H : UniversalTorsionFreeHost)
    (E : KazhdanEnvelope H.Carrier) :
    (UniversalKazhdanGroup.ofInputs H E).Carrier = E.Carrier := rfl

/-! ### The decomposition is faithful

`ofInputs` shows the two inputs suffice.  The two declarations below show
they are not more than enough either: Fournier-Facio's group is its own
host and its own envelope, so `UniversalTorsionFreeHost` together with
`KazhdanEnvelope` is exactly as strong as `KC.21` and not stronger.  This is
the same check `RelativeCommonQuotientData.toRoutingLemmaData` performs for
the routing interface, and it is what makes the split a *reading* of the
citation rather than a weakening of it. -/

/-- Fournier-Facio's group is itself a universal finitely presented
torsion-free group --- input 1, evaluated at the conclusion. -/
def UniversalKazhdanGroup.toHost (P : UniversalKazhdanGroup) :
    UniversalTorsionFreeHost where
  Carrier := P.Carrier
  groupCarrier := P.groupCarrier
  finitelyPresentedCarrier := P.finitelyPresentedCarrier
  torsionFree := P.torsionFree
  universal := P.universal

/-- ... and it is its own Kazhdan envelope, through the identity --- input 2,
evaluated at the conclusion. -/
def UniversalKazhdanGroup.toEnvelope (P : UniversalKazhdanGroup) :
    KazhdanEnvelope P.Carrier where
  Carrier := P.Carrier
  groupCarrier := P.groupCarrier
  finitelyPresentedCarrier := P.finitelyPresentedCarrier
  torsionFree := P.torsionFree
  kazhdan := P.kazhdan
  emb := MonoidHom.id P.Carrier
  emb_injective := fun _ _ hxy ↦ hxy

/-- **The split loses nothing.**  Sending `KC.21` through its own two inputs
returns the group it started from. -/
@[simp]
theorem ofInputs_toHost_toEnvelope (P : UniversalKazhdanGroup) :
    (UniversalKazhdanGroup.ofInputs P.toHost P.toEnvelope).Carrier =
      P.Carrier := rfl

/-! ## 4.  What the printed remark then does with it -/

/-- **The remark's *"in particular"*, at a `UniversalKazhdanGroup`.**  `P × P`
is finitely presented (`ProductFinitePresentation.instProd`, this
repository's theorem, since Mathlib closes finite presentation under free but
not direct products) and torsion-free (`IsPowerTorsionFree.prod`), so
universality applies to it and returns the printed `P₁ × P₂ ≤ P`. -/
theorem nonempty_containsSquare (P : UniversalKazhdanGroup) :
    Nonempty (ContainsSquare P.Carrier) := by
  obtain ⟨f, hf⟩ :=
    P.universal (P.Carrier × P.Carrier)
      (IsPowerTorsionFree.prod P.torsionFree P.torsionFree)
  exact ⟨⟨f, hf⟩⟩

/-- **Free subgroups of every finite rank.**  A free group of finite rank is
finitely presented and torsion-free, so universality places it inside `P`.

This is `Monsters.ContainsEveryFiniteRankFreeGroup`, the subgroup-universality
fragment the `Monsters` lane isolates, so the universal object built here and
the one built there are comparable in the vocabulary that lane already
uses. -/
theorem containsEveryFiniteRankFreeGroup (P : UniversalKazhdanGroup) :
    Monsters.ContainsEveryFiniteRankFreeGroup P.Carrier := by
  intro m
  exact P.universal (FreeGroup (Fin m)) IsPowerTorsionFree.of_isMulTorsionFree

/-- **The whole of `rem:ff-realization`, off `KC.21` and nothing else.**

Given Fournier-Facio's group, there are a self-square datum `h` and an
element `b ≠ 1` at which the Kazhdan--Clifford extension is finitely
presented, carries a nontrivial central involution, and is not
`CDE`-operator-MF.

Every hypothesis of `Sofic.RealizationFromUniversalGroup.realization` is
discharged from the structure: finite presentation and property `(T)` are
fields, the datum is `nonempty_containsSquare`, and the nonidentity element
is `exists_ne_one_of_universal`.  Property `(T)` is stored in the real form
and converted by `hasKazhdanPropertyT_iff_complex`, which is a theorem, not a
second definition. -/
theorem realization_of_universalKazhdanGroup (P : UniversalKazhdanGroup) :
    ∃ (h : ContainsSquare P.Carrier) (b : P.Carrier), b ≠ 1 ∧
      Group.IsFinitelyPresented (Extension h.alpha (h.emb (1, b))) ∧
        mark h.alpha (h.emb (1, b)) ≠ 1 ∧
          mark h.alpha (h.emb (1, b)) ^ 2 = 1 ∧
            (∀ g : Extension h.alpha (h.emb (1, b)),
              Commute (mark h.alpha (h.emb (1, b))) g) ∧
              ¬ IsCDEOperatorMF (Extension h.alpha (h.emb (1, b))) := by
  obtain ⟨h⟩ := nonempty_containsSquare P
  obtain ⟨b, hb⟩ := exists_ne_one_of_universal P.universal
  exact ⟨h, b, hb,
    realization (hasKazhdanPropertyT_iff_complex.mp P.kazhdan) h hb⟩

/-- **The bridge to the input this module replaces.**  A
`UniversalKazhdanGroup` inhabits `ContainsSquareWitness.UniversalFPTorsionFree`,
the opaque form of `KC.21` that `Sofic.ContainsSquareWitness` consumes.

The direction is the only one available and is the right one: that structure
quantifies over Mathlib's `IsMulTorsionFree`, which for a noncommutative
group is strictly stronger than having no elements of finite order, so it
asks for embeddings of *fewer* groups; `IsPowerTorsionFree.of_isMulTorsionFree`
supplies the weaker hypothesis this module's `universal` field wants.  So
nothing downstream of the old input is orphaned by the split. -/
theorem universalFPTorsionFree_of_universalKazhdanGroup
    (P : UniversalKazhdanGroup) :
    ContainsSquareWitness.UniversalFPTorsionFree P.Carrier :=
  ⟨fun Q _ _ _ ↦ P.universal Q IsPowerTorsionFree.of_isMulTorsionFree⟩

/-! ## 5.  How much of input 1 is already unconditional -/

/-- **Input 1 reduces to a single embedding statement.**  This repository
builds, with no hypothesis at all, a countable torsion-free group into which
every finitely presented torsion-free group embeds
(`Monsters.UniversalFinitelyPresentedTorsionFreeGroup`, a restricted direct
product over the presentation codes whose presented group is torsion-free).
Composing that with any injection into a group `P` makes `P` universal.

So the half of Chiodo Theorem 3.10 that is about *absorbing every group* is
already proved here; what remains owed to the literature is only the upgrade
to a **finitely presented** absorber.

**This does not discharge input 1, and is not a route to discharging it as it
stands.**  The explicit group is a restricted direct product indexed by
`{c // IsPowerTorsionFree (CodedPresentedGroup c)}`, and that set is not
recursive --- torsion-freeness is a Markov property, so Adian--Rabin makes it
undecidable.  The group is therefore countable but not recursively presented,
and Higman's embedding theorem --- or Chiodo's torsion-order-preserving
refinement, `research/torsion-free-higman-embedding.md` --- does not apply to
it as it stands.  The declaration says what shape of theorem suffices, and
deliberately concludes the universality *formula* rather than
`UniversalTorsionFreeHost`, so that the corpus audit keeps reporting the input
as open.

**Superseded 2026-08-19, and kept because the obstruction it names is the
point.**  `Monsters.ChiodoTorsionFreeAbsorber` runs the same construction over
the *full* code type and takes the universal torsion-free quotient afterwards
instead of filtering the index beforehand; the filtering was the only source
of the undecidability, and the quotient is Chiodo's own device (Proposition
3.8).  `Monsters.universal_of_embedding_chiodoAbsorber` is this declaration
with the repaired payload, and `Sofic.ChiodoUniversalHost` turns it into
`UniversalTorsionFreeHost`. -/
theorem universal_of_embedding_universalPayload {P : Type} [Group P]
    (g : Monsters.UniversalFinitelyPresentedTorsionFreeGroup →* P)
    (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f :=
  universal_comp
    (fun Q _ _ hQ ↦
      Monsters.embeds_universalFinitelyPresentedTorsionFreeGroup Q hQ) g hg

end FournierFacioUniversal
end GroupApproximation
