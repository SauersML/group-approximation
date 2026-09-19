import GroupApproximation.Sofic.FournierFacioUniversalGroup
import GroupApproximation.Monsters.ChiodoTorsionFreeAbsorber

/-!
# Chiodo's Theorem 3.10 (= Belegradek's Theorem A.1), reduced to one embedding

`Sofic.FournierFacioUniversalGroup` carries Fournier-Facio's first input as
the opaque structure `UniversalTorsionFreeHost`: *a finitely presented
torsion-free group containing a copy of every finitely presented torsion-free
group*, cited to Chiodo, arXiv:1107.1489v4, Theorem 3.10, which is Theorem
A.1 of Belegradek's appendix to Belegradek--Szczepanski.  Nothing inhabited
it, and the note attached to it said what stood in the way.

This file takes that citation apart in the same way the Fournier-Facio
citation was taken apart, and the result is that `UniversalTorsionFreeHost`
is no longer an input at all: it is *derived*, here, from one embedding
statement about one explicit group.

## Chiodo's proof, and which parts are now formal

Chiodo proves Theorem 3.10 from Theorem 3.9, and Theorem 3.9 from Theorem 2.2
together with the torsion-free-radical machinery of §3.  In this repository:

1. **§3, the torsion-free radical.**  `Algebra.TorsionFreeRadical`,
   `Algebra.TorsionFreeRadicalTower`, `Algebra.TorsionFreeQuotient`:
   Definition 3.1, Lemma 3.2, Proposition 3.3 and Corollary 3.4, proved
   unconditionally.  Corollary 3.4 is what makes the passage `G ↦ G^tf` legal
   and universal; Proposition 3.3 identifies it with Chiodo's transfinite
   tower.
2. **The absorbing group.**  `Monsters.ChiodoTorsionFreeAbsorber`: the
   restricted direct product of the groups of *all* finite presentation
   codes, passed to its universal torsion-free quotient.  Countable,
   torsion-free, and containing a copy of every finitely presented
   torsion-free group --- all proved unconditionally.  Chiodo uses a free
   product where this uses a direct sum; both work, and for the same reason.
   What the argument needs is a retraction of the ambient group onto one
   factor (`Chiodo.injective_of_retraction`), and a free product has one
   (`Monoid.CoprodI.of_leftInverse`) exactly as a direct sum does.  The
   Kurosh-type input that torsion in a free product is conjugate into a
   factor, which Mathlib does not have, is *not* needed: the free product is
   never claimed torsion-free, only its `^tf` quotient is.
   `Monsters.ChiodoFreeProductAbsorber` carries out Chiodo's own free-product
   construction on that basis, and `Sofic.ChiodoBelegradekTheorem` reduces
   Theorem 3.10 to either absorber.
3. **Definition 2.1 and the specialization Chiodo's proof performs**, below:
   `TorsionOrders`, and the equivalence between "no torsion orders" and
   torsion-freeness, which is the only inference made when Theorem 2.2 --- an
   equality of torsion-order *sets* --- is used to produce a torsion-*free*
   group.
4. **Theorem 2.2 itself**, the torsion-order-preserving Higman embedding, is
   the input, and it is carried as `TorsionFreeHigmanHull` evaluated at the
   absorber.

## What is owed, exactly

    Chiodo Theorem 3.10  =  ChiodoAbsorber (proved here)
                              + one embedding of it into a finitely presented
                                torsion-free group.

`TorsionFreeHigmanHull ChiodoAbsorber` is that embedding, and
`universalTorsionFreeHost` turns it into `UniversalTorsionFreeHost`.
**Nothing inhabits `TorsionFreeHigmanHull`**, so `UniversalTorsionFreeHost`
is still not inhabited; what has changed is what has to be supplied.  Before,
it was an existence claim quantified over every finitely presented
torsion-free group.  Now it is a single embedding claim about one named,
explicitly constructed group.

## Why the previous payload could not do this, and this one can

The earlier reduction, `FournierFacioUniversal.universal_of_embedding_universalPayload`,
had the same shape but was a dead end, and its docstring says why: its
payload is indexed by the presentation codes whose group is torsion-free,
an undecidable set by Adian--Rabin, so the payload is not recursively
presented and Chiodo's Theorem 2.2 --- whose hypothesis is a *recursive*
presentation --- cannot be applied to it.

`ChiodoAbsorber` is indexed by the full code type and is a torsion-free
quotient of that direct sum; the filtering that made the old payload
non-recursive has been replaced by the passage to `^tf`, which Chiodo's
Proposition 3.8 makes effective.  So the input carried here is one Chiodo's
Theorem 2.2 can actually discharge, which is the point of the file.

**Two honest caveats, recorded rather than left to be found.**

* This file does not prove that `ChiodoAbsorber` is recursively presented.
  That is a statement about presentations and computability; it needs
  Proposition 3.8, and this repository's computability layer has no notion of
  recursive presentation for infinitely generated groups.  What is proved is
  that the *obstruction* to recursive presentability which the old payload
  had is absent: the index type is decidable and the only non-syntactic step
  is the torsion-free quotient.
* `TorsionFreeHigmanHull ChiodoAbsorber` is, as a typed input, a priori
  *stronger* than `UniversalTorsionFreeHost`: it embeds one fixed countable
  group, where the host only has to absorb finitely presented ones, and no
  declaration here goes back the other way (a host absorbs finitely presented
  groups, and `ChiodoAbsorber` is not finitely presented).  It is not
  stronger than the *literature*: Chiodo's Theorem 3.9 gives a single
  finitely presented torsion-free group containing every countably generated
  recursively presentable torsion-free group, which is stronger still.  The
  split is therefore a reading of Theorem 3.9 rather than of Theorem 3.10,
  and Theorem 3.10 is the corollary this file proves.

## Why the input names a group instead of quantifying

`TorsionFreeHigmanHull` is stated for a group variable `K` but is only ever
used at `ChiodoAbsorber`, and that is deliberate: the general statement "every
countable torsion-free group embeds in a finitely presented torsion-free
group" is **false**, so an input of that shape would be an inconsistency
waiting to be found rather than a citation.  A countable group has only
countably many finitely generated subgroups --- a finitely generated subgroup
is named by a finite tuple of its elements --- while there are uncountably
many pairwise non-isomorphic two-generated torsion-free groups, so no single
countable group, finitely presented or not, can contain them all.  Chiodo's
Theorem 2.2 avoids this by hypothesizing a *recursive* presentation, and the
only way to carry that hypothesis without a formal notion of recursive
presentation is to name a group for which it holds.  That argument is prose
here; nothing below depends on it.
-/

namespace GroupApproximation
namespace ChiodoHost

open GroupApproximation.FournierFacioUniversal
open GroupApproximation.Monsters

universe u

/-! ## 1.  Chiodo's Definition 2.1 -/

/-- **Chiodo's Definition 2.1.**  `Tord(G)`, the set of orders of the
nontrivial torsion elements of `G`. -/
def TorsionOrders (G : Type u) [Group G] : Set ℕ :=
  {n : ℕ | 2 ≤ n ∧ ∃ g : G, orderOf g = n}

/-- **Empty torsion-order set means torsion-free.**

This is the whole of the inference Chiodo's proof makes when it applies
Theorem 2.2: that theorem preserves `Tord`, an equality of *sets of orders*,
and what is wanted from it is that a torsion-*free* group goes to a
torsion-free group.  Empty in, empty out, and empty means torsion-free. -/
theorem torsionOrders_eq_empty_iff (G : Type u) [Group G] :
    TorsionOrders G = ∅ ↔ IsPowerTorsionFree G := by
  constructor
  · intro h g n hn hpow
    by_contra hg
    have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩
    have h0 : orderOf g ≠ 0 := fun hcon => (orderOf_eq_zero_iff.mp hcon) hfin
    have h1 : orderOf g ≠ 1 := fun hcon => hg (orderOf_eq_one_iff.mp hcon)
    have hmem : orderOf g ∈ TorsionOrders G := ⟨by omega, ⟨g, rfl⟩⟩
    rw [h] at hmem
    simp at hmem
  · intro hG
    ext n
    constructor
    · rintro ⟨hn, g, hg⟩
      exfalso
      have hpos : 0 < orderOf g := by omega
      have hone : g ^ orderOf g = 1 := pow_orderOf_eq_one g
      have hg1 : g = 1 := hG g (orderOf g) hpos hone
      rw [hg1, orderOf_one] at hg
      omega
    · intro hmem
      simp at hmem

/-! ## 2.  The one remaining input -/

/-- **Chiodo, arXiv:1107.1489v4, Theorem 2.2, at a torsion-free group.**

Theorem 2.2 is a uniform algorithm sending a countably generated recursive
presentation `P = ⟨X | R⟩` to a finite presentation `T(P)` with an explicit
embedding `P⁻ ↪ T(P)` and `Tord(P⁻) = Tord(T(P))`.  Applied to a
recursive presentation of a torsion-free group, the torsion-order clause says
the finitely presented output is torsion-free too
(`torsionOrders_eq_empty_iff`), and what is left is this structure: a
finitely presented torsion-free group with `K` inside it.

Chiodo attributes Theorem 2.2 to his own earlier work and notes it is
implicit in Rotman's proof of the Higman embedding theorem; the reading is
recorded at `research/torsion-free-higman-embedding-via-chiodo-torsion-orders.md`.

**Nothing in this repository inhabits this structure**, at any `K`.  The
algorithmic content --- the whole of Higman embedding --- is not formalized,
and no declaration below pretends otherwise. -/
structure TorsionFreeHigmanHull (K : Type) [Group K] where
  /-- The finitely presented torsion-free group `T(P)`. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  /-- Theorem 2.2's torsion-order clause, specialized: empty in, empty out. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- Theorem 2.2's explicit embedding `P⁻ ↪ T(P)`. -/
  emb : K →* Carrier
  /-- ... which is an embedding. -/
  emb_injective : Function.Injective emb

instance hullGroup {K : Type} [Group K] (H : TorsionFreeHigmanHull K) :
    Group H.Carrier :=
  H.groupCarrier

instance hullFinitelyPresented {K : Type} [Group K]
    (H : TorsionFreeHigmanHull K) : Group.IsFinitelyPresented H.Carrier :=
  H.finitelyPresentedCarrier

/-- The hull's carrier has no torsion orders at all: Definition 2.1 read back
off the structure.  Recorded because it is the clause Theorem 2.2 actually
delivers, and `torsionFree` is the form the rest of the development
consumes. -/
theorem torsionOrders_hull_eq_empty {K : Type} [Group K]
    (H : TorsionFreeHigmanHull K) : TorsionOrders H.Carrier = ∅ :=
  (torsionOrders_eq_empty_iff H.Carrier).mpr H.torsionFree

/-! ## 3.  Theorem 3.9 and Theorem 3.10 -/

/-- **Chiodo Theorem 3.9, in the only instance Theorem 3.10 needs.**  A
finitely presented torsion-free group containing the absorber contains a copy
of every finitely presented torsion-free group.

This concludes the universality *formula*, deliberately, and not
`UniversalTorsionFreeHost`: a reader who has an embedding from somewhere else
can use this without going through the structure, and the corpus audit keeps
reporting the input as open. -/
theorem universal_of_hull (H : TorsionFreeHigmanHull ChiodoAbsorber) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* H.Carrier, Function.Injective f :=
  universal_of_embedding_chiodoAbsorber H.emb H.emb_injective

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1.**  The universal finitely
presented torsion-free group, built from the absorber and one embedding.

Every field but `emb` comes from the hull; `universal` is the theorem of this
lane, and it is `Monsters.embeds_chiodoAbsorber` composed with the embedding.
So

    KC.21 input 1  =  Chiodo Theorem 2.2 at `ChiodoAbsorber`  +  this file,

where before it was Theorem 3.10 taken whole. -/
def universalTorsionFreeHost (H : TorsionFreeHigmanHull ChiodoAbsorber) :
    UniversalTorsionFreeHost where
  Carrier := H.Carrier
  groupCarrier := H.groupCarrier
  finitelyPresentedCarrier := H.finitelyPresentedCarrier
  torsionFree := H.torsionFree
  universal := universal_of_hull H

/-- The construction changes nothing but the label: the universal group *is*
the hull's carrier. -/
theorem universalTorsionFreeHost_carrier
    (H : TorsionFreeHigmanHull ChiodoAbsorber) :
    (universalTorsionFreeHost H).Carrier = H.Carrier := rfl

/-- The hull's own embedding, recorded as a statement about the group the
universal host is built on.  With `universalTorsionFreeHost_carrier` above,
this says the absorber itself --- and not only the groups it absorbs --- sits
inside the output. -/
theorem absorber_embeds_hull (H : TorsionFreeHigmanHull ChiodoAbsorber) :
    ∃ f : ChiodoAbsorber →* H.Carrier, Function.Injective f :=
  ⟨H.emb, H.emb_injective⟩

end ChiodoHost
end GroupApproximation
