import GroupApproximation.Higman.OmegaDebt
import GroupApproximation.Manuscript.NonMF.ChiodoOfHigman
import GroupApproximation.Manuscript.NonMF.HullFillTheoremCCorrected
import GroupApproximation.Manuscript.NonMF.HullInputsProved
import GroupApproximation.Manuscript.NonMF.TheoremCPrinted
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.GGT.HullSCFilling
import GroupApproximation.GGT.HullSCHypEmbedded
import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.TreeWPDAxis

/-!
# Theorem C, closed: the cited inputs as recorded debts

Theorem C is proved from two bundles of cited results: Fournier-Facio's
paragraph (`TheoremC.LiteratureInputs`: Chiodo, Kotowski–Ollivier–Wise,
Fournier-Facio et al. with Osin, Minasyan–Osin, and Hull's common quotient
theorem) and Hull's small cancellation theorem with its companion
(`HullCorrectedInputs.HullInputsCorrected`).

The Hull bundle is the corrected one.  `TorsionFree.HullInputs` is not used
anywhere below `lem:saturation` any more: one of its four fields is false as
recorded, and `Manuscript.NonMF.HullFillKernelRefutation` proves that, so
`Saturation.saturation` and the two printed forms of Theorem C take
`HullCorrectedInputs.HullInputsCorrected` instead.

This module records what is still owed, one declaration per cited result, the
ones still owed proved by `sorry`, so that the debts are visible in the kernel's
axiom report rather than hidden in a leading binder, and closes the two printed
statements of Theorem C on top of them.  The names say which theorem of the
literature each `sorry` stands for.

## The Chiodo field is no longer one of them

`ChiodoOfHigman.chiodo_of_omega` proves Chiodo's Theorem 3.10 from Higman's
ω-closure, so the first field of `LiteratureInputs` is discharged down to the
single construction `Higman.Omega.OmegaInput`.  That construction is proved, in
`Higman.OmegaFillLeadLinkBenign`, and read once for the whole repository from
`Higman.OmegaDebt`, which the recognition lane's debt file imports as well: one
theorem, shared by the two lanes that stand on it.

## What each remaining debt is

* `kotowskiOllivier` — the density model at a parameter between `1/3` and
  `1/2`.  `Hyperbolic.SharpExistence` asks for an *infinite* finitely presented
  torsion-free hyperbolic group with property (T); every clause but property
  (T) is met by `Multiplicative ℤ`, and
  `Hyperbolic.CharTwoTorsionObstruction` records why no group this repository
  builds meets that one.
* `smallCancellationQuotient` — Osin's Theorem 2.4(5) on small cancellation
  over relatively hyperbolic groups.  Nothing here constructs a quotient of a
  hyperbolic group in which a prescribed subgroup embeds.
* `osinTheorem12` — Osin's Theorem 1.2 in the implication `(AH₃) ⇒ (AH₁)`, which
  is what is left of the Minasyan–Osin citation.  `minasyanOsin` is no longer a
  citation of its own: `E` acts on the Bass–Serre tree of its second HNN
  splitting (`GGT.BassSerreHNN`), the tree is `0`-hyperbolic, `u₂u₁⁻¹` is
  loxodromic on it, and `GGT.BassSerreDoubleHNN.isWPDAt_axisElt_unconditional`
  proves it satisfies the WPD condition — Minasyan–Osin's Corollary 4.3, proved
  in `GGT/TreeWPDAxis.lean` from the shift invariant of a tree action.  `E` is
  never virtually cyclic (`GGT.BassSerreDoubleHNN.not_isVirtuallyCyclic`), so
  the `(AH₃)` datum of `E` is unconditional and only the passage from it to the
  Cayley-graph form remains.  `GGT/WPDAcylindricalHyperbolicity.lean` reduces
  that passage further, to Dahmani–Guirardel–Osin's Theorem 6.8 and Osin's
  Theorem 5.4 with his Lemma 5.12.
* `hullCommonQuotient` — Hull's Corollary 7.4, which is Hull's Theorem 7.1
  applied to the free product of `E` with `H₀`, so it rests on the same four
  leaves as `hullTheorem71` does, together with the free product input;
  `HullSCCommonQuotientCorrected.hullCommonQuotient_of_oneStep_corrected` is
  that reduction, and `HullSC.FreeProductStatementCorrected` is the extra
  input.  The uncorrected `HullSC.FreeProductStatement` is **refuted**
  (`HullSCCommonQuotientCorrected.not_freeProductStatement`): it omits the
  non-elementarity of `H₀`, which `HullCommonQuotientStatement` supplies twice
  over.
* `hullHypEmbeddedConeOff`, `dgoTheorem53`, `hullFillingData`,
  `hullSection6Relator` — Hull's §5 and §6, with Dahmani–Guirardel–Osin's
  Theorem 5.3 separated out of the first of them.  **`hullTheorem71` is not one
  of the debts any longer**, and neither is `hullTheorem51`: the first is proved
  through `HullSC.hullOneStep_of_relator_of_quotient` and
  `HullSC.hullBallFormNG_of_oneStep`, the second through
  `HullSC.hullQuotient_of_fillingData`.  What the reduction contributes is the
  whole of the manuscript's own bookkeeping — the induction on `m`, the two
  clauses that mention the targets `t₁, …, t_m`, and the arithmetic of the
  kernel (`HullSC.ker_comp_eq`), so that the manuscript's separate remark on
  Hull's construction is a citation only at `m = 1`, where it reads `ker q` is
  the normal closure of the single relator `t⁻¹u`.
* `hullTheorem71`, `osinLemma71` — the two fields of
  `HullCorrectedInputs.HullInputsCorrected`, both of them now proved.  They
  replace the four fields of
  `TorsionFree.HullInputs`, which cannot all be discharged: the kernel field of
  that structure quantifies over every `HullQuotient`, and at `m = 0` it asserts
  that the printed clauses alone force `q` to be injective, which the first
  projection `Q × Q → Q` of an acylindrically hyperbolic `Q` refutes
  (`HullFillKernelRefutation.not_kerNormallyGeneratedStatement`).  The remark on
  the kernel is a property of Hull's construction, so it travels with the
  quotient as a field of `HullCorrectedInputs.HullQuotientNG`; and Hull's
  Corollary 5.7 with Lemma 5.8 is not a citation at all over a torsion-free
  ambient group
  (`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`),
  which is the only case `lem:saturation` uses.  So Hull's four cited results
  are two.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Manuscript
namespace NonMF

namespace TorsionFree

open GroupApproximation.HullGeometry

/-! ## Hull's small cancellation theorem and its companion -/

/-- **DEBT (literature).**  Hull, §5 (his Corollary 5.7 with Lemma 5.8, after
Dahmani–Guirardel–Osin's Theorem 6.14 and Osin's Theorem 5.4), in the
hyperbolic-embedding form: a suitable subgroup contains a subgroup that is
hyperbolically embedded in the ambient group over a base whose cone-off is
Hull's own alphabet, and that contains an element loxodromic on `Γ(G,A)`.

This is a different consequence of Hull's §5 from the two-generator form
`HullInputs.twoGeneratedSuitable`, which over a torsion-free ambient group is
not a citation at all
(`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`).
Torsion-freeness buys the choice of two loxodromics generating a suitable
subgroup; it does not buy the hyperbolic embedding, which is what Theorem 5.1
runs over.

Not derivable from `GGT.DGOTheorem68` either, which produces `E(g) ↪_h (G,X)`
for an `X` with no relation to a prescribed alphabet: the enlargement of `X`
that makes the coned-off action acylindrical is Osin's Theorem 5.4 and is in
general infinite, so `GGT.DGOCorollary427` — invariance under finite symmetric
difference of the base — does not bridge it.

Recorded on the cone-off, which is the statement with no bookkeeping in it:
three conditions on one subgroup.  `HullSC.existsHypEmbeddedConeOff_of_core`
proves the converse, so nothing has been strengthened. -/
theorem hullHypEmbeddedConeOff : HullSC.ExistsHypEmbeddedConeOff.{0} := by
  sorry

/-- Hull's §5 leaf in the form Theorem 5.1 consumes it, from the cone-off form
above: `HullSC.HypEmbeddedCore` adds a relative generating set and two equations
pinning its base and its family, and `HullSC.HypEmbeddedCore.ofConeOff` supplies
both by `rfl`. -/
theorem hullHypEmbeddedInSuitable : HullSC.ExistsHypEmbeddedInSuitable.{0} :=
  HullSC.existsHypEmbeddedInSuitable_of_coneOff hullHypEmbeddedConeOff

/-- **DEBT (literature).**  Dahmani–Guirardel–Osin, *Hyperbolically embedded
subgroups and rotating families*, Theorem 5.3: the quotient of a group acting
on a hyperbolic space by a separated very rotating family.  The clauses
recorded are the ones Hull's §5 consumes — the kernel is the subgroup the
rotations generate, its nonidentity elements are rotations up to conjugacy or
loxodromic, finite order lifts with the order preserved, and the injectivity
radius at a basepoint `ρ`-far from the apices is at least the separation.

Two of those restrictions are forced rather than chosen.
`HullSC.eq_one_of_dist_lt_everywhere` refutes the displacement clause stated at
every point of the space — a rotation fixes its apex and lies in the kernel — and
`HullSC.not_rotation_or_loxodromic_of_empty` refutes the dichotomy stated for
every element of the kernel, the identity being neither conjugate into a
rotation subgroup nor loxodromic. -/
theorem dgoTheorem53 : HullSC.DGOQuotientStatement.{0, 0} := by
  sorry

/-- **DEBT (literature).**  Hull, §5, with Dahmani–Guirardel–Osin's Theorem 5.3
taken out of it: for every radius and every prescribed family of suitable
subgroups there are parameters `ε, μ, ρ` such that every `C(ε, μ, ρ)` family
gives a separated very rotating family on the cone-off, with separation above
`2R` and with the rotations generating the normal closure of the relator; and
every quotient by that normal closure carries a Hull alphabet containing the
image of `A` in which the images of the prescribed subgroups are suitable.

The small cancellation condition is not an opaque predicate here:
`HullSC.RelWord.IsSmallCancellation` has a body — symmetrized, admissible, long,
`H`-letters outside `GGT.RelGenSet.relBall ρ`, `ε`-pieces shorter than `μ` times
their word — so this citation and its consumer cannot drift apart.

The space carrying the family is abstract, and it has to be:
`HullSC.rot_eq_bot_of_cayley` proves that a rotating family on a Cayley graph of
`G` has trivial rotation subgroups, since the translation action is free, so
Theorem 5.3 applied on `Γ(G, A ⊔ H)` would produce only the identity. -/
theorem hullFillingData : HullSC.HullFillingDataStatement.{0} := by
  sorry

/-- **Hull, Theorem 5.1**, proved rather than cited: the two debts above give
it through `HullSC.hullQuotient_of_fillingData`, which supplies seven of the ten
clauses of the filling quotient from Dahmani–Guirardel–Osin's theorem — the
quotient group and map, surjectivity, the kernel, the lifting of finite order,
and injectivity on the `R`-ball of `Γ(G,A)` through
`HullSC.injOn_cayleyBall_of_action`.  Only the three alphabet clauses are
carried by `hullFillingData`. -/
theorem hullTheorem51 : HullSC.HullQuotientStatement.{0} :=
  HullSC.hullQuotient_of_fillingData dgoTheorem53 hullFillingData

/-- **DEBT (literature).**  Hull, §6: the relator can be chosen.  For any
parameters `ε, μ, ρ` there is `u ∈ N` and a `C(ε, μ, ρ)` family containing a
word spelling `t⁻¹u` — Hull takes `u = h₁^{n₁} h₂^{n₂} ⋯` in two independent
loxodromics of `N` with the exponents large, which is what puts the `H`-letters
outside the relative ball of radius `ρ` and makes the `ε`-pieces short.

This statement was false until Olshanskii's exclusion clause was put back into
`HullSC.RelWord.IsPiece`.  Without it a family closed under cyclic permutation
has every one of its words as an `ε`-piece of itself — a cyclic permutation
names the conjugate of what the word names, by the prefix it moves, and for a
first letter of the base that prefix has base-length one — so `pieces_small`
read `|v| < μ|v|` and nothing with `μ ≤ 1` satisfied the condition.
`HullSC.RelWord.exists_naive_piece_of_rotate` and
`HullSC.RelWord.false_of_pieces_small_self` are that refutation. -/
theorem hullSection6Relator : HullSC.HullRelatorStatement.{0} := by
  sorry

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*, Theorem
7.1**, in the finite-set formulation the manuscript records, together with the
manuscript's remark on his construction: the kernel of `q` is normally
generated by `m` elements.  The remark is a field of the quotient
(`HullCorrectedInputs.HullQuotientNG`) because it is a property of the
construction rather than of an arbitrary quotient with the printed properties.

**No longer a citation of its own.**  Everything between the four leaves above
and this statement is proved in `GGT/HullSC*.lean`:

* `HullSC.hullOneStep_of_relator_of_quotient` — Hull's §6 relator fed to his
  Theorem 5.1, and then the two clauses that mention the target `t`: the relator
  `t⁻¹u` dies, so `q(t) = q(u) ∈ q(N)`, and `ker q` is the normal closure of the
  single element `t⁻¹u`.
* `HullSC.hullBallFormNG_of_oneStep` — the induction on `m`, whose kernel
  arithmetic is `HullSC.ker_comp_eq` and whose radius bookkeeping is
  `HullSC.image_cayleyBall_subset`: the balls of `Γ(G,A)` are infinite when `A`
  is, so the image of the `R`-ball has to be shown to sit in the `R`-ball of the
  quotient at the *same* radius rather than swallowed by a larger one.
* `HullCorrectedInputs.smallCancellation_of_ballFormNG` — the published
  injectivity-radius form turned into the finite-set form. -/
theorem hullTheorem71 :
    ∀ {G : Type} [Group G] [IsAcylindricallyHyperbolic G]
      (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
        ∀ {m : ℕ} (t : Fin m → G) {F : Set G}, F.Finite →
          Nonempty (HullCorrectedInputs.HullQuotientNG N t F) := by
  intro G _ _ A N hN m t F hF
  exact HullCorrectedInputs.smallCancellation_of_ballFormNG
    (HullSC.hullBallFormNG_of_oneStep
      (HullSC.hullOneStep_of_relator_of_quotient hullHypEmbeddedInSuitable
        hullSection6Relator hullTheorem51)) A hN t hF

/-- **Osin, *Acylindrically hyperbolic groups*, Lemma 7.1, proved**
(`GGT.Elementary.osinLemma71_closed`: the Morse theorem, the common-power
theorem and the acylindrical pigeonhole, with no Bowditch dichotomy): an
`s`-normal subgroup of an acylindrically hyperbolic group acts
non-elementarily.  Recorded in the case `lem:saturation` uses it — a normal
subgroup of a torsion-free group — which is also the case the repository's
partial machinery is stated for
(`HullGeometry.exists_escaping_or_noncommuting_of_isSNormal` carries
`IsPowerTorsionFree G`, `HullGeometry.actsNonElementarily_of_normal_conjugate`
carries `[S.Normal]`).
`HullCorrectedInputs.osinNonElementary_of_osinLemma71` checks that this is a
special case of Osin's lemma as it is usually stated. -/
theorem osinLemma71 :
    ∀ {G : Type} [Group G] (A : HullGeneratingSet G),
      IsPowerTorsionFree G → ∀ (N : Subgroup G) [N.Normal],
        HullSuitable.IsSNormal N →
          ActsNonElementarily N (Cayley.base A.alphabet) :=
  GGT.Elementary.osinLemma71_closed

/-- Hull's inputs, as a term: the two debts above, and nothing else.  Hull's
Corollary 5.7 with Lemma 5.8 is not a field of the corrected bundle — over a
torsion-free ambient group it is
`Manuscript.NonMF.HullInputsProved.exists_pair_suitable_of_torsionFree`, and
that is the only case `lem:saturation` uses. -/
def hullInputs : HullCorrectedInputs.HullInputsCorrected.{0} where
  smallCancellation := hullTheorem71
  osinNonElementary := osinLemma71

end TorsionFree

namespace TheoremC

/-! ## Chiodo's Theorem 3.10, reduced to Higman's ω-closure -/

/-- **Chiodo, Theorem 3.10 (= Belegradek, Theorem A.1)**, on the ω-closure
rather than on a citation of its own: `chiodo_of_omega` proves it outright from
Higman's ω-closure, and the ω-closure is `Higman.OmegaDebt.omegaInput`, the
repository's single record of that construction. -/
theorem chiodo : ChiodoBelegradek.Statement :=
  chiodo_of_omega Higman.OmegaDebt.omegaInput

/-! ## The four citations of Fournier-Facio's paragraph that remain -/

/-- **DEBT (literature).**  Kotowski–Kotowski and Ollivier–Wise: the density
model at a parameter between `1/3` and `1/2` gives an infinite finitely
presented torsion-free hyperbolic group with property (T). -/
theorem kotowskiOllivier : KotowskiOllivierStatement := by
  sorry

/-- **DEBT (literature).**  Fournier-Facio et al., Proposition 2.3, with Osin,
*Small cancellations over relatively hyperbolic groups and embedding theorems*,
Theorem 2.4(5). -/
theorem smallCancellationQuotient : FournierFacioQuotientStatement := by
  sorry

/-- **DEBT (literature).**  Osin, *Acylindrically hyperbolic groups*, Theorem
1.2, in the implication `(AH₃) ⇒ (AH₁)`: a group that is not virtually cyclic
and acts on a hyperbolic space with a loxodromic WPD element is acylindrically
hyperbolic.  This is the theorem Minasyan–Osin cite as their Theorem 3.3, and
after `GGT/TreeWPDAxis.lean` it is all that is left of their tree criterion at
`E`.  `GGT.osinTheorem12_of` splits it into Dahmani–Guirardel–Osin's Theorem
6.8 and Osin's `(AH₄) ⇒ (AH₁)`. -/
theorem osinTheorem12 : GGT.OsinTheorem12.{0, 0} := by
  sorry

/-- **Minasyan–Osin at `E`, no longer a citation of its own.**  The tree half is
proved: `E` acts on the Bass–Serre tree of its second HNN splitting, `u₂u₁⁻¹` is
loxodromic on it and satisfies the WPD condition by Minasyan–Osin's Corollary
4.3 — which `GGT/TreeWPDAxis.lean` proves, in the form that asks for the
basepoint to lie on the axis — and `E` is never virtually cyclic.  So the
`(AH₃)` datum of `E` is unconditional and the citation reduces to Osin's
Theorem 1.2. -/
theorem minasyanOsin : MinasyanOsinStatement :=
  GGT.BassSerreDoubleHNN.minasyanOsinStatement_of_osinTheorem12 osinTheorem12

/-- **DEBT (geometry).**  The one clause of Hull's Corollary 7.4 still owed:
the Cayley graph of `E * H₀` over the union of two Hull alphabets is
hyperbolic and the translation action on it is acylindrical — the tree of
spaces.  Everything else of the corollary is proved in
`GGT/HullSCFreeProductFactor.lean` and `GGT/HullSCCommonQuotient.lean`. -/
theorem hullFreeProductUnionGeometry : HullSC.FreeProductUnionGeometryStatement := by
  sorry

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*,
Corollary 7.4, on the recorded debts**: his Theorem 7.1 in one-step form
(`TorsionFree`'s three §5/§6 leaves) applied twice over the free product,
with the union-alphabet geometry the only further input. -/
theorem hullCommonQuotient : HullCommonQuotientStatement :=
  HullSC.hullCommonQuotient_of_oneStep_of_geometry
    (HullSC.hullOneStep_of_relator_of_quotient TorsionFree.hullHypEmbeddedInSuitable
      TorsionFree.hullSection6Relator TorsionFree.hullTheorem51)
    hullFreeProductUnionGeometry

/-- The cited inputs, as a term.  The first field is proved; the other four are
the debts above. -/
def literatureInputs : LiteratureInputs :=
  { chiodo := chiodo
    kotowskiOllivier := kotowskiOllivier
    smallCancellationQuotient := smallCancellationQuotient
    minasyanOsin := minasyanOsin
    hullCommonQuotient := hullCommonQuotient }

/-! ## Theorem C, closed -/

/-- **Theorem C (`thm:torsion-free`), in radical form, as a closed
declaration** on the recorded debts. -/
theorem manuscriptTorsionFreeFullMFRadical_closed : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical literatureInputs TorsionFree.hullInputs

/-- **Theorem C, in the simplified printed statement, as a closed
declaration** on the recorded debts. -/
theorem manuscriptTorsionFreeSimplified_closed : PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified literatureInputs TorsionFree.hullInputs

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
