# Lane `thm-e` — Theorem 5 (`thm:torsion-free`) and `sec:torsion-free`

Ground truth for this note is the committed manuscript,
`git show origin/main:non_mf_groups_exist.tex` at lines 316–330 (the theorem)
and 1367–1445 (the section).  Every quotation below is from that text.

## 1.  Audit of `Saturation.lean` and `TorsionFreeTheoremC.lean`

### 1.1  `Manuscript/NonMF/Saturation.lean`

**The statement matches.**  `TorsionFree.saturation` takes `G` finitely
presented (instance), torsion-free (`IsPowerTorsionFree`), acylindrically
hyperbolic (instance), `N` normal (instance) and nontrivial, and `F` finite;
it returns `Nonempty (SaturationQuotient N F)`, whose eight fields are the
printed clauses one for one — surjection, two generators with
`closure {g₁,g₂} = ⊤`, finite presentation, torsion-freeness, acylindrical
hyperbolicity, injectivity on `F`, and `N.map q = ⊤`.  Nothing printed is
missing and nothing unprinted is concluded.  The extra binder is `hHull`, the
citation bundle, which is the point.

**Divergences found.**

1. **The module docstring quotes a sentence that is no longer printed.**  Its
   proof table opens with

   > "Because `N ⊴ G`, one has `N ∩ gNg⁻¹ = N` for every `g ∈ G`"

   attributed to `twistedInter_eq_of_normal`.  The current printed proof has no
   such sentence: it says only *"The subgroup `N` is normal, and it is infinite
   because `G` is torsion-free and `N ≠ 1`, so it acts non-elementarily on
   `Cay(G,A)` by Osin [Lemma 7.1]"*.  The Lean is not wrong — it proves
   `s`-normality, which is what its Osin citation consumes — but the docstring
   attributes it to a sentence of an earlier draft.  Documentation defect only.

2. **`HullInputsCorrected.smallCancellation` carries a hypothesis `thm:hull`
   does not print.**  Its binders include `(_hG : IsPowerTorsionFree G)`.

   > *Printed (`thm:hull`).*  "Let `G` be acylindrically hyperbolic, let
   > `N ≤ G` be suitable with respect to `A`, and let `g₁,…,g_m ∈ G` and a
   > finite subset `Ω ⊆ G` be given.  Then there is a surjective homomorphism
   > `φ : G → Q` such that `Q` is acylindrically hyperbolic, `φ|_Ω` is
   > injective, `φ(gᵢ) ∈ φ(N)` for all `i`, and every element of finite order in
   > `Q` is the image of an element of the same order in `G`."

   No torsion-freeness anywhere in it.  The divergence is in the safe direction
   — the Lean assumes more of `G`, so it asks less of Hull — but the field is
   not the printed theorem.  Fixed by
   `TorsionFreePrinted.HullSmallCancellationPrinted`, which drops the
   hypothesis; `HullPrintedInputs.toCorrected` recovers the field.

3. **`HullInputsCorrected.osinNonElementary` asks for more than the print
   cites.**  Its hypothesis is `HullSuitable.IsSNormal N`.

   > *Printed (proof of `lem:saturation`).*  "The subgroup `N` is normal, and it
   > is infinite because `G` is torsion-free and `N ≠ 1`, so it acts
   > non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1]."

   The printed hypotheses are therefore: `G` torsion-free, `N` normal, `N ≠ 1`.
   Since the repository *proves* `normal + torsion-free + nontrivial ⇒
   s-normal` (`isSNormal_of_torsionFree`), the field as stated applies to
   strictly more subgroups than the printed sentence, so the bundle is a
   stronger assumption than the section makes.  Fixed by
   `TorsionFreePrinted.OsinLemma71Printed` plus `ne_bot_of_isSNormal`;
   `osinNonElementary_of_printed` shows the printed form still supplies the
   field.

   *Against the source.*  Osin's Lemma 7.1 (arXiv:1304.1246) is stated for
   `s`-normal subgroups, so `HullInputsCorrected`'s field is closer to Osin's
   own words than to the manuscript's sentence.  Both are defensible readings of
   the citation; what is not defensible is a bundle that assumes the stronger of
   the two while the printed proof only ever uses the weaker.

4. **The two-generated suitable subgroup `N₀` (Hull 5.7 with 5.8) is present,
   and it is proved rather than cited.**  `HullInputsProved.exists_pair_suitable_of_torsionFree`
   produces `h₁,h₂ ∈ N` with `⟨h₁,h₂⟩` suitable, and `saturation` calls it at
   the line the print cites Hull.  Two remarks:

   * The print hedges — *"possibly with respect to a larger generating set
     `A' ⊇ A`, and Theorem `thm:hull` holds for `A'` as well"*.  The Lean does
     **not** need the hedge: it returns suitability for the same `A`, because
     the repository's `ActsNonElementarily` is *contains two independent
     loxodromic elements*, so the pair the hypothesis hands out already
     generates a non-elementary subgroup, and Hull's clause (3) is free over a
     torsion-free group.  The Lean is therefore stronger than the printed
     sentence here.  `HullSuitablePairPrinted` records the printed sentence
     including the hedge, and `hullSuitablePair_of_torsionFree` proves it with
     `A' = A`.
   * Consequently `HullPrintedInputs` has **two** fields where the section
     prints **three** citations.  That is a discharge, not an omission.

5. **`Ω` is called `F` in Lean.**  Cosmetic; noted because the section's `Ω` and
   the Fournier-Facio datum `F` collide in the reader's eye.

6. **The kernel clause.**  The print puts it in the paragraph after `thm:hull`
   (*"so `ker φ` is the normal closure of `m` elements and `Q` is finitely
   presented when `G` is"*), and the Lean puts it in the output structure
   `HullQuotientNG`.  That placement is forced:
   `HullFillKernelRefutation.not_kerNormallyGeneratedStatement` refutes the
   version quantified over arbitrary Hull quotients.  Faithful, and correctly
   documented in the tree.

### 1.1a  The Lean against Hull's own words

Verbatim statements, read from Hull, arXiv:1308.4345v2, supplied by the lead.

> **Theorem 7.1.**  Suppose `G ∈ AH` and `S` is suitable with respect to `A`.
> Then for any `{t₁,…,t_m} ⊂ G` and `N ∈ ℕ`, there exists a group `Ḡ` and a
> surjective homomorphism `γ : G → Ḡ` which satisfy (a) `Ḡ ∈ AH`; (b)
> `γ|_{B_A(N)}` is injective; (c) `γ(tᵢ) ∈ γ(S)`; (d) `γ(S)` is suitable with
> respect to `A'`, where `γ(A) ⊆ A'`; (e) every element of `Ḡ` of order `n` is
> the image of an element of `G` of order `n`.

Three observations.

* **The manuscript drops Hull's clause (d).**  `thm:hull` prints (a), (b) in
  finite-set form, (c) and (e), and says nothing about `γ(S)` remaining suitable.
  The tree's `HullQuotient` has exactly four fields and so matches the
  manuscript, not Hull.  Dropping a conclusion weakens a citation, which is the
  safe direction, and nothing in `lem:saturation` uses (d).  Recorded because a
  reader comparing the Lean with Hull will notice the missing clause.
* **Clause (b) is the ball form**, and the tree carries the reduction honestly:
  `HullBallFormStatementNG` is the published radius formulation and
  `smallCancellation_of_ballFormNG` derives the finite-set form from it, which
  is the manuscript's own preamble sentence.
* **Clause (e) is what makes the saturation quotient torsion-free**, and
  `torsionFree_of_finiteOrder_lift` uses it in exactly that form.

> **Corollary 5.7.**  Suppose `S` is suitable with respect to `A`.  Then for all
> `k`, `S` contains non-commensurable loxodromic elements `h₁,…,h_k` such that
> `E_G(hᵢ) = ⟨hᵢ⟩`.  In particular `{⟨h₁⟩,…,⟨h_k⟩} ↪_h (G,A)`.
>
> **Lemma 5.8.**  If `S` contains an infinite order element `h` such that `⟨h⟩`
> is a proper subgroup of `S` and `⟨h⟩ ↪_h (G,X)`, then `S` is suitable with
> respect to `A` for some `A ⊇ X`.

The manuscript's one-sentence combination of these is
`HullSuitablePairPrinted`, alphabet enlargement included.  The repository's
torsion-free proof `exists_pair_suitable_of_torsionFree` reaches the same
conclusion without either result, and without enlarging the alphabet, because
its notion of non-elementarity is *contains two independent loxodromics*.  What
Hull's pair buys and the torsion-free proof does not need is the hyperbolic
embedding of `⟨hᵢ⟩` — which is also exactly what the tree cannot state.

> **Corollary 7.4.**  Let `G₁, G₂ ∈ AH` with `G₁` finitely generated, `G₂`
> countable.  Then there exists a non-virtually-cyclic group `Q` and surjective
> homomorphisms `αᵢ : Gᵢ → Q`.  In addition, if `G₂` is finitely generated then
> we can choose `Q ∈ AH₀`, and if `K(Gᵢ) = 1` then for any finite `Fᵢ ⊆ Gᵢ` we
> can choose `αᵢ` injective on `Fᵢ`.

**Corollary 7.4 says nothing about torsion or finite presentability.**  Both
places where this repository uses it read those conclusions off its *proof*, and
both should say so.  `TheoremC.HullCommonQuotientStatement` (the old route)
asserts a finitely presented torsion-free `G₀` with property (T) as if the
corollary printed it; `TorsionFreePrinted.HullCommonQuotientPrinted` (the new
one) asserts the same two conclusions but its docstring records that they come
from the two applications of `thm:hull` to the free product.  It carries no
property-(T) clause at all, where the old statement does: property (T) of the
common quotient is not Hull's to give, and `cor:relative-quotient` gets it by
pushing it along the surjection from `Q`.  The same reading applies to
`FournierFacioParagraph`, which attributes finite
presentation and torsion-freeness of `G₀` to Fournier-Facio §2 and only the
adjective *acylindrically hyperbolic* to Corollary 7.4 — which is what the
printed paragraph does.

### 1.2  `Manuscript/NonMF/TorsionFreeTheoremC.lean`

**The assembly does not follow the current printed proof.**
`manuscriptTorsionFreeFullMFRadical (I : TheoremC.LiteratureInputs) (hHull)`
builds `G₀` from five citations — Chiodo's universal finitely presented
torsion-free group, a Kotowski--Ollivier density-model group, the
small-cancellation quotient `P`, Minasyan--Osin's tree criterion, and Hull's
Corollary 7.4 — and protects an explicit commutator of a free group `F₂` in
place of Fournier-Facio's simple `J`.  The current print (September 2026) does
none of this: it takes `G₀`, `Γ`, `t`, `J` from Fournier-Facio §2 directly and
uses Hull's Corollary 7.4 only for the adjective *acylindrically hyperbolic*.
There is no Kotowski--Ollivier, Chiodo, or Osin Theorem 1.2 input in the printed
proof any more.  So the theorem in this module is a proof of the same
conclusion over a superseded input set; it is not the printed route.

**The conclusion is not the printed statement either.**
`PrintedTorsionFreeFullMFRadical` asserts

* `IsTwoGenerated`, finite presentation, `IsPowerTorsionFree`, acylindrical
  hyperbolicity, property (T) — the five printed adjectives, matching; then
* `manuscriptCoronaMFResidual Q = ⊤`, where the print says *"every homomorphism
  from `Q` to an MF group is trivial"*.  Over a countable group these are
  interchangeable through
  `OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets`, but the printed
  clause is not literally stated anywhere in the module;
* `∀` nontrivial quotient `L`, `manuscriptCoronaMFResidual L = ⊤` — **strictly
  stronger than anything printed**.  The print says only *"no nontrivial
  quotient of `Q` is MF"*;
* `∀` nontrivial quotient `L`, `¬ IsOperatorMF L` — this is the printed last
  sentence, matching.

`TorsionFreePrinted.PrintedTorsionFreeTheorem` is the printed statement, clause
for clause, including the printed *"every homomorphism from `Q` to an MF group
is trivial"*.  The old Prop is untouched and is also proved from the new
inputs (`manuscriptTorsionFreeFullMFRadicalFromParagraph`).

**Other observations.**

7. `TorsionFreeTheoremC`'s §3 docstring quotes a version of `thm:torsion-free`
   (*"…with property (T) and `Rad_MF(Q) = Q`.  Every nontrivial quotient of `Q`
   also equals its own MF radical…"*) that is not the printed theorem.  Stale
   docstring, same class as (1).
8. `coronaMFResidual_eq_top_of_normallyGenerating` carries `[Nontrivial L]` and
   never uses it.
9. The section `sec:torsion-free` and `thm:torsion-free` carry **no
   `\leanverified` anchor at all** in the committed tex, although the tree has
   carried the conditional argument since August.  Wiring the badges is the
   lead's call; the declarations to point at are listed in §3 below.

## 2.  What landed

| module | endpoint | commit | jobs |
| --- | --- | --- | --- |
| `Manuscript/NonMF/FournierFacioParagraph.lean` | `TorsionFreePrinted.FournierFacioParagraph` | `8b5a34ac399b046ce37f5c5e8ff44504b2ac2796` | 4066 |
| `Manuscript/NonMF/HullPrintedInputs.lean` | `HullSmallCancellationPrinted`, `OsinLemma71Printed`, `HullSuitablePairPrinted`, `HullPrintedInputs`, `HullPrintedInputs.toCorrected` | `8572454bc7de0fb7e0274efa40d0ed98c3b1ae17` | 3637 |
| `Manuscript/NonMF/TorsionFreePrintedTheorem.lean` | `PrintedSaturation`, `manuscriptSaturation`, `PrintedTorsionFreeTheorem`, `manuscriptTorsionFreeTheorem`, `manuscriptTorsionFreeFullMFRadicalFromParagraph` | `40756d73a1d4f57d7e9655fae3e82e0bacb4fcf3` | 4440 |
| `Manuscript/NonMF/TorsionFreeRelativeQuotient.lean` | `HasTrivialFiniteRadical`, `hasTrivialFiniteRadical_of_torsionFree`, `HullCommonQuotientPrinted`, `PrintedRelativeQuotient`, `manuscriptRelativeQuotient` | `5aba8488403b5696b406fe7ce94e740d480527e2` | 4441 |
| `Manuscript/NonMF/RegularNonMFAlgebra.lean` | `infinite_of_acylHyperbolic`, `IsStableRankOne`, `HasUniqueTracialState`, `unitary_leftRegularOperator`, `leftRegularPreimage`, `topologicalClosure_adjoin_pair`, `DGOTheorem235Printed`, `GerasimovaOsinTheorem11Printed`, `PrintedRegularNonMFAlgebra`, `manuscriptRegularNonMFAlgebra` | `80b748885c21f9d191ebc7093175885295577513` | 4451 |
| `Manuscript/OneSidedMFRadical/PrintedDefectFunctorial.lean` | `PrintedDefectFunctorial`, `manuscriptPrintedDefectFunctorial` | `7479aaeecc97bef572b8d3b5305b5a1fabfe9870` | 4069 |
| `Manuscript/NonMF/PrintedDefectParagraph.lean`, with `TorsionFreePrintedTheorem.lean` rewired | `defect_generator_mem_of_simpleFactor`, `commutator_conjFactor_le_printedDefect`, `conjFactor_le_printedDefect`, `PrintedSimpleFactorInDefect`, `manuscriptSimpleFactorInDefect`, `map_conjFactor_le_printedDefect_of_functorial` | `d67dd4e47308018cce7854de3d65bf8a89c33887` | 4455 |

Only one existing file was edited: `TorsionFreePrintedTheorem.lean`, this
lane's own, rewired to the new printed route and landed in the same commit as
the module it consumes.  New declarations live in the sub-namespace
`GroupApproximation.Manuscript.NonMF.TorsionFreePrinted`, except the two in
`PrintedDefectFunctorial.lean`, which sit beside `printedDefect` in
`Manuscript.OneSidedMFRadical` because that is where the printed display and
its consumers live.

**For the lead.**  Two housekeeping consequences, neither of them this lane's to
act on.  The root import list needs the seven new modules.  And the sentence
census may classify the new endpoints as `conditional-data`, since they quantify
over or consume `PrintedFournierFacioData`; if it does, they belong in
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` beside the twelve rows already
registered there for that datum.

## 3.  What Theorem 5 now rests on

`TorsionFreePrinted.manuscriptTorsionFreeTheorem` has exactly two hypotheses.

| Lean name | literature |
| --- | --- |
| `TorsionFreePrinted.FournierFacioParagraph` | Fournier-Facio, §2 (`G₀`, `Γ`, `t`, `J` and the four relations) together with Hull, *Small cancellation in acylindrically hyperbolic groups*, Corollary 7.4 (the quotient may be chosen acylindrically hyperbolic) |
| `TorsionFreePrinted.HullPrintedInputs.smallCancellation` (`HullSmallCancellationPrinted`) | Hull, Theorem 7.1, in the finite-set form, with *"`ker φ` is the normal closure of `m` elements"* from the proof |
| `TorsionFreePrinted.HullPrintedInputs.osinNonElementary` (`OsinLemma71Printed`) | Osin, *Acylindrically hyperbolic groups*, Lemma 7.1, in the printed case |

Discharged, and therefore **not** hypotheses:

* Hull, Corollary 5.7 with Lemma 5.8 — `hullSuitablePair_of_torsionFree`;
* Hull, Theorem 3.12 — `TorsionFree.exists_hullGeneratingSet`, unpacking, because
  acylindrical hyperbolicity is taken in its Cayley-graph form;
* nonabelianness of `J` — `exists_not_commute_of_isSimpleGroup_of_infinite`.

## 3a.  The two corollaries of `sec:torsion-free`

**`cor:relative-quotient`** is `TorsionFreePrinted.PrintedRelativeQuotient`,
proved by `manuscriptRelativeQuotient` from three hypotheses: the two of
Theorem 5, plus `HullCommonQuotientPrinted`.  The printed sentence *"since a
torsion-free acylindrically hyperbolic group has no nontrivial finite normal
subgroup"* is `hasTrivialFiniteRadical_of_torsionFree`, proved; normality is not
even used, because a finite subgroup of a torsion-free group is already trivial.
The route through the free product `G * Q` is **not** formalized: it would need
acylindrical hyperbolicity of a free product of two acylindrically hyperbolic
groups together with suitability of the factors inside it, none of which this
repository has, so the citation is the honest carrier and its docstring
separates the corollary's printed clauses from what the manuscript reads off its
proof.

**`cor:regular-nonmf-algebra`** is
`TorsionFreePrinted.PrintedRegularNonMFAlgebra`, proved by
`manuscriptRegularNonMFAlgebra` from four hypotheses: the two of Theorem 5, plus
`DGOTheorem235Printed` and `GerasimovaOsinTheorem11Printed`.  Of the eight
printed adjectives, five are proved outright:

| printed adjective | Lean |
| --- | --- |
| separable | `reducedGroupCStar_separable_stablyFinite` |
| unital | the `CStarAlgebra` instance, plus `(1 : ReducedGroupCStar Q) ≠ 0` |
| generated by two unitaries | `unitary_leftRegularOperator`, `topologicalClosure_adjoin_pair` |
| stably finite | `reducedGroupCStar_separable_stablyFinite`, through the canonical faithful trace |
| not MF | `not_isMFAlgebra_reducedGroupCStar`, on `¬ IsCDEOperatorMF Q` from Theorem 5 |

and three are the citations: simple and unique trace (Dahmani--Guirardel--Osin,
Theorem 2.35) and stable rank one (Gerasimova--Osin, Theorem 1.1).

Two remarks on the formalization.  *Generated by two unitaries* turns out to be
pure algebra: `leftRegularPreimage` makes the elements whose left translation
lies in a star-subalgebra into a subgroup, so two group generators already
adjoin the whole regular representation and the two star-subalgebras of
`B(ℓ²Q)` are equal before any closure is taken.  And **Osin's Theorem 1.2 is not
a separate Prop**: the printed proof cites it only to turn *countable,
acylindrically hyperbolic, trivial finite radical* into DGO's own hypothesis, a
non-degenerate hyperbolically embedded subgroup, and this module has no
vocabulary for that notion.  Folding it into the hypotheses of the two C⋆-Props
is recorded in both docstrings.  If the lead wants Osin 1.2 named, the place to
get the vocabulary is the `GGT/` hyperbolically-embedded development, at the
cost of a new dependency from `Manuscript/NonMF` into `GGT`.

Also proved on the way, closing a sentence of Theorem 5's own proof that nothing
carried before: `infinite_of_acylHyperbolic`, *"The group `Q` is infinite because
it is acylindrically hyperbolic."*

## 3b.  `lem:commutator-in-defect` is gone; `eq:defect-functorial` replaces it

The print changed under this lane (origin/main `e51f655d2`).  The lemma

> For every homomorphism `ρ : G₀ → Ḡ`, `ρ(S) ≤ 𝔇_Ḡ(ρ(Γ))`

is **deleted**.  In its place a displayed inequality follows
`eq:intrinsic-defect`,

> for every homomorphism `f : G → H`, `f(𝔇_G(L)) ≤ 𝔇_H(f(L))`,

and section 5 argues inside `G₀`: `[tct⁻¹, ℓ] ∈ 𝔇_{G₀}(Γ)` for `c ∈ J` and
`ℓ ∈ S` straight from the definition, so `[S,S] ≤ 𝔇_{G₀}(Γ)`, and `S` is
perfect, so `S ≤ 𝔇_{G₀}(Γ)`.  Theorem 5 then cites the display for
`φ(S) ≤ 𝔇_Q(φ(Γ))`.

Three consequences for the tree.

1. **The display already existed as a theorem.**  `map_printedDefect_le` in
   `Manuscript/OneSidedMFRadical/DefectSaturation.lean` is exactly
   `f(𝔇_G(L)) ≤ 𝔇_H(f(L))`, proved by the printed clauses one for one.  What
   was missing is a closed named proposition for the display, so
   `PrintedDefectFunctorial.lean` wraps it as
   `manuscriptPrintedDefectFunctorial` with an axiom audit, and re-proves
   nothing.  The older module's docstring calls the display
   `eq:defect-functoriality`; the tex labels it `eq:defect-functorial`.
2. **The section-5 paragraph is now carried sentence by sentence** in
   `PrintedDefectParagraph.lean`, and its closed conclusion is
   `manuscriptSimpleFactorInDefect : S ≤ 𝔇_{G₀}(Γ)`.  Perfectness is unchanged:
   it is still `PrintedFournierFacioData.commutator_conjFactor_eq` from
   simplicity and nonabelianness of `J`.  What moved is *where* the containment
   is proved and *how* it reaches the quotient.
3. **`manuscriptLemmaCommutatorInDefect` is kept and untouched.**  It is still
   true; it is no longer the printed route.  But the census register
   `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` carries a
   `conditional-data` row naming it for `lem:commutator-in-defect`, and that
   label no longer exists in the tex.  Twelve further rows in that register name
   the `PrintedFournierFacioData` theorems the deleted lemma's proof used.  The
   register is metadata and this lane does not edit it; the lead should decide
   whether those rows now point at a sentence that is not printed.

## 4.  What discharging Hull's Theorem 7.1 would take

Hull's Theorem 7.1 is not a lemma away.  Its proof runs through his §5, whose
gate is his Lemma C — *"`{H_λ} ↪_h G` implies there is a `C` such that for a
geodesic `n`-gon `P` with isolated components `p_i`, `i ∈ I`, one has
`Σ_{i∈I} ℓ̂_{λ_i}(p_i) ≤ Cn`"* — which is Dahmani–Guirardel–Osin
Proposition 4.14 verbatim, with one constant `C` uniform in the number of
sides.  The repository has the fixed-side-count instances of Lemma C (landed as
`GGT/HullYiLemmaC.exists_radius_notMem_fam_mul`), and those are enough for
Hull's two *direct* uses, because his threshold `d̂ ≥ 50C` is chosen after `C`.
What it does not have is the uniform bound, `OsinComponents.IsolatedComponentBound`,
and the one consumer that needs the linear-sum form is DGO Lemma 4.21, which
gates all of Hull §5.  So the honest sizing is: Hull 7.1 sits behind DGO 4.21,
which sits behind uniform DGO 4.14, and the tree's DGO lane
(`GGT/DGOLemma421*.lean`, some two dozen modules) is exactly the attempt to
close that.  This is a hyperbolic-geometry programme measured in lanes and
weeks, not an afternoon, and it also drags in hyperbolically embedded
subgroups, rotating families, and the cone-off geometry that DGO Corollary 4.27
moves between alphabets.

Two cautions from the tree's history, both recorded in memory and both worth
repeating before anyone starts.  First, the routed-quotient blocker elsewhere in
this repository is **not** Hull: the bespoke `C'(1/6)` router was built to avoid
acylindrical hyperbolicity altogether and bottoms out in two open Greendlinger
leaves, so "formalize Hull" is not a way to make those constructions
unconditional.  Second, the record shows how easy it is to state Hull's theorem
in a form that is false rather than merely unproved:
`TorsionFree.HullInputs.kerNormallyGenerated` quantified the kernel remark over
every Hull quotient and is refuted outright by `pr₁ : Q × Q → Q` at `m = 0`.
Any new statement of Theorem 7.1 should therefore be written the way
`HullQuotientNG` writes it — the construction's data travelling with the
quotient the construction produces — and should be model-tested at `m = 0`,
`N = ⊥`, and `Ω = ∅` before a single line of geometry is attempted.  Starting
the geometry programme is the lead's decision and this lane has not begun it.
