import GroupApproximation.Higman.OmegaDebt
import GroupApproximation.Manuscript.NonMF.ChiodoOfHigman
import GroupApproximation.Manuscript.NonMF.HullFillTheoremCCorrected
import GroupApproximation.Manuscript.NonMF.HullInputsProved
import GroupApproximation.Manuscript.NonMF.TheoremCPrinted
import GroupApproximation.GGT.DGOWindmillTheorem53
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.GGT.HullSCFilling
import GroupApproximation.GGT.HullSCHypEmbedded
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.GGT.HullSCRelatorWord
import GroupApproximation.GGT.HullSCConeOffSpace
import GroupApproximation.GGT.HullSCRelatorSeparation2Published
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.HullSCUnionGeometryAssembly
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
ones still owed represented by explicit proof holes, so that the debts are visible in the kernel's
dependency report rather than hidden in a leading binder, and closes the two printed
statements of Theorem C on top of them.  The names say which theorem of the
literature each proof hole stands for.

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
* `hullLemma44Canonical`, `hullLemma49KernelPower`,
  `hullSection6Relator` — the source-faithful §5 and §6 leaves.  Lemma 4.4 is
  recorded only as injectivity of the natural quotient on the requested ball
  and preservation of the simultaneously selected peripheral family.  Lemma
  4.9 is recorded as its quotient-free kernel-power correction, exactly
  equivalent to order-preserving finite-order lifts.  Neither lemma is
  attributed a cone-off, rotating family, apex separation, or DGO conclusion.
  `HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49`
  assembles their literal quotient `G ⧸ normalClosure {w}`.  The remaining
  interface work is to state the §6 relator over the selected auxiliary index
  family; the historical Bool-pair one-step seam is deliberately not presented
  as a consequence of these lemmas.
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
Dahmani–Guirardel–Osin and Osin's Theorem 5.4), in the hyperbolic-embedding
form **over a pair**: a suitable subgroup contains two subgroups whose cone-off
over Hull's own alphabet is hyperbolically embedded, which contain independent
loxodromic elements of `Γ(G,A)`, and which meet trivially — Hull's (W4).

**Over a pair and not over one subgroup, and that is forced.**  Hull's relator
is `p·h₁^{m₁}h₂^{m₂}⋯`, and over a single hyperbolically embedded `H` all of
its `H`-letters lie in one component of `Γ(G, X ⊔ H)`, so the word runs between
vertices at distance at most one and is not quasi-geodesic —
`HullSC.not_quasiGeodesic_relatorWord`.  His §5 needs it to be.  With two
subgroups the relator alternates between the components
(`HullSC.isComp_relatorWord₂`) and the obstruction is gone.  So the single-
subgroup forms of this row and the next, `HullSC.ExistsHypEmbeddedConeOff` and
`HullSC.HullConeOffStatement`, are superseded rather than merely unused: they
cannot carry the relator Theorem 5.1 runs over.

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

**Four of its five clauses are free**, and `GGT/HullSCConeOffCyclicReduction.lean`
proves it: at the cyclic subgroups `⟨h₀⟩`, `⟨h₁⟩` the containment in `N` is
`Subgroup.zpowers_le`, the membership is `Subgroup.mem_zpowers`, the pair of
independent loxodromics is the first conjunct of Hull's Definition 1.4 read
back, and (W4) is
`GGT.Elementary.zpowers_disjoint_of_independent` — a common element is
`h₀^p = h₁^q`, and nonzero exponents contradict independence.  What is left of
this row is one geometric clause, the hypothesis of
`GGT.HullSC.existsHypEmbeddedConeOff₂_of_zpowers`: *for a suitable `N` there
**are** independent loxodromic `h₀, h₁ ∈ N` with the cone-off of `A` along
`⟨h₀⟩` and `⟨h₁⟩` hyperbolically embedded.*

The existential is not decoration.  With the pair quantified universally the
clause is false: a base letter outside a family member that normalises it puts
that member in the relative ball of radius three, so `{⟨a²⟩, ⟨b⟩}` over
`{a, a⁻¹, b, b⁻¹}` in `F₂` is a pair of independent loxodromics whose cone-off
is not hyperbolically embedded
(`GGT.HullSC.not_isHyperbolicallyEmbedded_zpowers_pow`). -/
theorem hullHypEmbeddedConeOff : HullSC.ExistsHypEmbeddedConeOff₂.{0} := by
  sorry

/-- **DEBT (literature).**  Dahmani–Guirardel–Osin, *Hyperbolically embedded
subgroups and rotating families*, Theorem 5.3(b): for a separated very rotating
family on a hyperbolic geodesic space, every nonidentity element of the subgroup
the rotations generate is conjugate into a rotation subgroup or is loxodromic.

**That is now the whole of the debt**, and three findings put it in this shape.

The geodesic hypothesis is not decoration: `GGT/HullSCDGO.lean` shows the
statement without it lets an empty annulus make the very rotating condition
vacuous.  The clauses of the conclusion other than the dichotomy are not cited
at all — `GGT/DGORotatingQuotientResidual.lean` proves the quotient, the map,
its surjectivity and its kernel are `G ⧸ ⟨⟨Rot⟩⟩` and nothing more.  And the
clause this row used to carry alongside the dichotomy, that finite order lifts
with the order preserved, is **not a consequence of Theorem 5.3 and is false as
recorded** (issue #50): `GGT/DGORotatingQuotientRefutation.lean` refutes it at a
one-point space, where the very rotating condition is vacuous and the clause
asserts that `ℤ` has an element of order two, and
`GGT/DGOFreeSplittingOnePoint.lean` shows the same model satisfies DGO's other
conclusion, the free splitting, so no route from the theorem reaches it.  It is
Hull's §5 and lives with the family he builds, as
`HullSC.RotatingData.finiteOrder_lift`.

Two further restrictions are forced rather than chosen.
`HullSC.eq_one_of_dist_lt_everywhere` refutes a displacement clause stated at
every point of the space — a rotation fixes its apex and lies in the kernel — and
`HullSC.not_rotation_or_loxodromic_of_empty` refutes the dichotomy stated for
every element of the kernel, the identity being neither conjugate into a
rotation subgroup nor loxodromic. -/
theorem dgoTheorem53 : HullSC.DGOQuotientStatementGeodesic.{0, 0} := by
  exact DGOWindmill.dgoQuotientStatementGeodesic

/-- **DEBT (literature).**  Hull, Lemma 4.4, after the simultaneous auxiliary
peripheral family has been selected.  This is the exact natural-quotient
conclusion: injectivity on the requested Cayley ball and hyperbolic embedding
of every mapped peripheral.  No rotating-space geometry is attributed to the
lemma. -/
theorem hullLemma44Canonical :
    HullSC.HullLemma44CanonicalQuotientStatement.{0} := by
  sorry

/-- **DEBT (literature).**  Hull, Lemma 4.9, in its quotient-free form.  The
kernel-power correction is precisely the diagram property needed to lift a
finite-order quotient element with its order preserved. -/
theorem hullLemma49KernelPower :
    HullSC.HullLemma49KernelPowerStatement.{0, 0} := by
  sorry

/-- **DEBT (literature).**  Hull, Corollary 5.7, in the printed finite-family
form needed to select all cyclic peripherals before applying Lemma 4.4 once.
Theorem 3.16 supplies the hyperbolic embedding of the resulting simultaneous
family unconditionally. -/
theorem hullYiSuitableFiniteFamily : HullSC.YiSuitableFiniteFamily.{0} := by
  sorry

/-- Hull's torsion-free canonical filling quotient, assembled directly from
Lemmas 4.4 and 4.9.  The quotient is literally the quotient by the normal
closure of the chosen relator; Lemma 5.8 supplies its alphabet and suitability
clauses. -/
theorem hullCanonicalQuotient :
    HullSC.TorsionFreeHullCanonicalQuotientStatement.{0} :=
  HullSC.torsionFreeHullCanonicalQuotientStatement_of_lemma44_of_lemma49
    (HullSC.simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      hullYiSuitableFiniteFamily)
    hullLemma44Canonical hullLemma49KernelPower

/-- **Temporary exact interface debt.**  The historical Bool-pair quotient
statement is still consumed by the existing one-step reduction below.  The
canonical quotient above uses the full selected auxiliary index family, so it
cannot be projected to this statement without restating §6 over that same
family. -/
theorem hullTheorem51 : HullSC.HullQuotientStatement₂Published.{0} := by
  sorry

/-- **DEBT (literature).**  Hull, §6 over a pair: the relator can be chosen.
For any parameters `ε, μ, ρ` there is `u ∈ N` and a published `C₁` family over
`{H₀, H₁}` containing a word spelling `t⁻¹u` — Hull takes
`u = h₀^{n₁} h₁^{n₂} ⋯` alternating between two independent loxodromics of `N`
with the exponents large, which is what puts the `H`-letters outside the
relative ball of radius `ρ` and makes the `ε`-pieces short.

**The single-subgroup form of this row is refuted, and is not what stands
here.**  `HullSC.RelatorSeparation` and `HullSC.RelatorChoice` quantify over the
diagonal `w' = w`, because `HullSC.RelWord.pieces_small_of_longMatch` discarded
Olshanskii's exclusion clause `v' ≠ v`; on the diagonal the conclusion asserts
that a short `y` centralises `t⁻¹·lox^{Σm}`, and in `D∞ ∗ ℤ` with a `t` that
inverts the loxodromic that is false for every spelling and every exponent list.
`GGT/HullSCRelatorSeparationRefuted.lean` carries the witness.  The two rows
that recorded them are gone with the Unit chain they belonged to, and a
torsion-free ambient group does not rescue them, because this row quantifies
over every acylindrically hyperbolic group.

**The replacement path is now typed at the chosen exponent list.**  Issue #180
and `HullSC.not_relatorSideExclusionAtUnrestricted₂_one_of_two_le` refute the
former unrestricted-anchor side-exclusion premise.  The exact-length
finite-avoidance construction in
`HullSC.exists_relator_exponents_window_diff_through_exact` instead chooses one
list jointly with the deep-letter, difference, pure-tail, and through-base-tail
exclusions.  That chosen list must feed the remaining block-count argument and
all the extra `IsLemma49Input` fields; no projection to the weaker predicate is
accepted by the one-step seam.

Two of those extra fields are already bookkeeping rather than debts.
`RelWord.finite_componentLetters_symmetrized` proves strong boundedness, and
`RelWord.publishedPiecesSmall_symmetrized_of_piecesSmall_of_sameWord` proves
the two-sided published-piece estimate on distinct symmetrized words from the
existing corrected piece estimate in both directions.  The remaining piece
case is exactly two prefixes of the same word, alongside the prime-piece and
`(1/4,1)` quasi-geodesic clauses.

The seam adjoins `t^{±1}` first and applies both halves to that enlarged core,
so no claim over the original relative metric remains in this row. -/
theorem hullSection6Relator :
    HullSC.HullRelatorStatement₂OfBaseLetterPublished.{0} := by
  sorry

/-- **Hull's Theorem 7.1 at `m = 1`, over the pair.**

`HullSC.hullOneStep_of_published₂` is the seam: after the target
`t` is known it adjoins `t^{±1}` to the core, feeds the one-letter §6 relator to
the quotient half of Theorem 5.1 on that same core, and proves the two clauses
that mention `t` — the
relator `t⁻¹u` dies in the quotient, so `q(t) = q(u) ∈ q(N)`, and `ker q` is the
normal closure of that single element, which is the manuscript's remark on
Hull's construction at `m = 1`.

Nothing in `HullSC.HullOneStepStatement` mentions the index type, so this is the
same statement the single-subgroup route used to produce, and everything above
it — the tower, the ball form, and Hull's Corollary 7.4 — is unchanged. -/
theorem hullOneStep : HullSC.HullOneStepStatement.{0} :=
  HullSC.hullOneStep_of_published₂ hullHypEmbeddedConeOff
    hullSection6Relator hullTheorem51

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*, Theorem
7.1**, in the finite-set formulation the manuscript records, together with the
manuscript's remark on his construction: the kernel of `q` is normally
generated by `m` elements.  The remark is a field of the quotient
(`HullCorrectedInputs.HullQuotientNG`) because it is a property of the
construction rather than of an arbitrary quotient with the printed properties.

**No longer a citation of its own.**  Everything between the four leaves above
and this statement is proved in `GGT/HullSC*.lean`:

* `hullOneStep` above — Hull's §6 relator fed to his Theorem 5.1 over the pair,
  and then the two clauses that mention the target `t`.
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
    (HullSC.hullBallFormNG_of_oneStep hullOneStep) A hN t hF

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

/-- **Proved.**  The last clause of Hull's Corollary 7.4: the Cayley graph of
`E * H₀` over the union of two Hull alphabets is hyperbolic and the translation
action on it is acylindrical.  Hyperbolicity is the four-point condition on
the syllable normal form (`GGT/HullSCUnionGeometryCoprod`), acylindricity is
the branch-point estimate with constant zero together with the factors' own
acylindricity at a long syllable (`GGT/HullSCUnionGeometryAssembly`); the
naive tree inequality this replaces is refuted in
`GGT/HullSCUnionGeometryAcylindrical`. -/
theorem hullFreeProductUnionGeometry : HullSC.FreeProductUnionGeometryStatement :=
  HullSCUnionGeometry.freeProductUnionGeometryStatement_unconditional

/-- **Hull, *Small cancellation in acylindrically hyperbolic groups*,
Corollary 7.4, on the recorded debts**: his Theorem 7.1 in one-step form
(`TorsionFree.hullOneStep`, on that section's four §5/§6 leaves over a pair)
applied twice over the free product, with the union-alphabet geometry the only
further input. -/
theorem hullCommonQuotient : HullCommonQuotientStatement :=
  HullSC.hullCommonQuotient_of_oneStep_of_geometry TorsionFree.hullOneStep
    hullFreeProductUnionGeometry

/-- The cited inputs, as a term.  The first field is proved; the other four are
the debts above. -/
theorem literatureInputs : LiteratureInputs :=
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
