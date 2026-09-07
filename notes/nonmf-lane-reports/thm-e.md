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
   does not print.**  Its binders include `(_hG : IsPowerTorsionFree G)`.  The
   printed `thm:hull` reads *"Let `G` be acylindrically hyperbolic, let `N ≤ G`
   be suitable with respect to `A`, and let `g₁,…,g_m ∈ G` and a finite subset
   `Ω ⊆ G` be given"* — no torsion-freeness.  The divergence is in the safe
   direction (the Lean assumes more of `G`, so it asks less of Hull), but the
   field is not the printed theorem.  Fixed by
   `TorsionFreePrinted.HullSmallCancellationPrinted`, which drops the
   hypothesis; `HullPrintedInputs.toCorrected` recovers the field.

3. **`HullInputsCorrected.osinNonElementary` asks for more than the print
   cites.**  Its hypothesis is `HullSuitable.IsSNormal N`; the printed sentence's
   hypotheses are `G` torsion-free, `N` normal, `N ≠ 1`.  Since the repository
   *proves* `normal + torsion-free + nontrivial ⇒ s-normal`
   (`isSNormal_of_torsionFree`), the field as stated applies to strictly more
   subgroups than the printed sentence, so the bundle is a stronger assumption
   than the section makes.  Fixed by `TorsionFreePrinted.OsinLemma71Printed`
   plus `ne_bot_of_isSNormal`; `osinNonElementary_of_printed` shows the printed
   form still supplies the field.

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

None of the three modules edits an existing file, so nothing downstream had to
move.  All new declarations live in the sub-namespace
`GroupApproximation.Manuscript.NonMF.TorsionFreePrinted`.

**For the lead.**  Two housekeeping consequences, neither of them this lane's to
act on.  The root import list needs the three new modules.  And the sentence
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
