# Lane `sp-lh` — the coefficient parameter through Leray–Hirsch, Chern, projective space and the chart tower

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5.  Clone: `stw-fix` (cores 6-11).
Owns, inside `GroupApproximation/CharClass/`: `LerayHirsch*`, `Chern*` (except
`ChernTotalRing`, which is `sp-coeff`'s), `Projective*`, `CohomologyChart*`,
`CohomologyLHRingComponent`, and the `Wu.HasSplitting` **producers** (the `HasSplitting`
declaration itself is in `SqDataInstance.lean`, prefix `Sq*`, owner `sp-steenrod`).
Upstream, binding: `sp-coeff.md` §0c (the naming convention), `sp-cupone.md`.

> **This file was destroyed and rewritten at 15:27** by a runaway `str.replace` in my own
> editing script — the replacement text contained its own search text, and the report grew
> to 168 MB of one duplicated section.  It was untracked, so there was nothing to restore.
> Rewritten from the conversation record.  The lesson is in TRAPS and it is not a Lean one.

## 0. The census

**128 files, 14,979 lines.**

**Only 13 files (2,612 lines) need no edit at all**, and my first count was wrong.  I said
33, by testing whether a file *names* `Hmod2`, `TotalH` or `cohomologyZMod2`.  That is the
test `sp-coeff` §0b warns against: a file inherits the coefficient through a **name**, and
`ProjectiveSpaceInputs` speaks only `HasCPCohomology`, `ProjectiveSpaceRingEntry` only
`eq_zero_or_eq_of_line`.  The reliable test is the import closure — does it reach
`CohomologyBasic` — and it gives **13 zero-edit files against 115 needing work, 12,367
lines**.  The 13 are pure point-set topology plus `ChernRelation` and `LerayHirschAlgebra`,
which already take an abstract ring: **the Chern-class algebra and the five lemma were
coefficient-free before this lane existed.**

**Only 24 files name `ZMod 2`**, and I confirm `sp-coeff`'s mechanism classification, with
one mechanism they did not name (see §5b).

### 0.1 Ten `cup_comm` sites, every one even

`cup_comm` is applied ten times in my layer; the eleventh, `ChernTotalRing:94`, is
`sp-coeff`'s `mul_comm` field, which quantifies over all degrees, is genuinely false at odd
`p`, and is dropped over `K`.  **In all ten of mine, one side has degree `2` or `2*d`** — a
hyperplane class, a tautological Euler class, or a `cpTop`.  Five want the even class on the
left, five on the right; five have the degree as the literal `2`.  So `sp-cupone`'s
`cup_comm_of_even` covers the layer and the signed formula is consumed nowhere here.

**There is no unsigned `cup_comm` over `K` and there must not be.**  Every commutation in
this layer is an instance of `cup_comm_of_even`, available only because the class being
moved has even degree.  A future lane that wants to commute two odd classes here has found
a real obstruction, not a missing lemma.

### 0.2 The seam that reached into another lane's file: `MVSequence`'s five fields

`MVSequence` is declared in **my** `ProjectiveSpaceCohomology.lean` and constructed in
**`sp-coeff`'s** `MayerVietorisSequence.lean`, whose five fields read
`(mvResU U V hUV n).hom.toAddMonoidHom`.

The fields were `→+`, and the mod-2 file promoted them to linear with `toLinearZMod2` —
"over `F₂` every additive map is `F₂`-linear", by `decide`.  That is false over `K` and is
needed wherever a **line** is transported.  I tried the version that touches nobody, passing
scalar-compatibility as a hypothesis, and abandoned it: it wanted two hypotheses on
`hasCPCohomologyOf_succ`, two more on `exists_sum_eq_of_lines`, and one pair from every
future producer of `HasCPCohomology`.

The maps were linear all along — the constructor had to **strip** the linearity to fit the
fields, which is the tell.  So `MVSequenceOf K` has `→ₗ[K]` fields, the promotion is
deleted, and I made the five-token edit in `sp-coeff`'s file.  **Approved by the lead**;
`sp-coeff` informed, no revert.  Cost elsewhere, and it is the whole cost: seven
`.toAddMonoidHom` insertions in `LerayHirschInduction`'s five-lemma block, and two `rw`s
there rewritten as `Iff.trans` because `rw` cannot see past the coercion.  I grepped the
tree for every other site using these maps as hom *values* rather than applying them: there
are none, and `GysinPair` is byte-unchanged.

### 0.3 Two lanes declared the same lemma, and nothing could see it

`sp-coeff`'s `CoeffLine.lean` and my `ProjectiveSpaceRing.lean` **both declared
`GroupApproximation.CharClass.lineGen`, with the same body `e.symm 1`**, five days apart,
and both declared a `lineGen_ne_zero` with the same proof.  No duplicate scan and no probe
could see it: both are correct, neither file was red, and the ambiguity exists only in the
future tree where one first imports the other.  Resolution under the standing rule — the
landed name wins: `ProjectiveSpaceRing` drops its copy and imports `CoeffLine`, keeping only
the `F₂`-only consequences (`eq_lineGen_of_ne_zero`, `lineGen_eq`, `eq_zero_or_eq_of_line`),
now proved from `sp-coeff`'s `eq_of_line_of_ne_zero_zmod2`.  I am `CoeffLine`'s first
importer, so it is no longer an orphan.

## 1. The recipe

`sp-coeff` §0c is binding: `K` implicit where an argument determines it, explicit and first
otherwise, `F₂` spellings kept as reducible `abbrev`s.  Applied here the split is small.

* **`K` implicit, name unchanged, every call site byte-identical** — everything whose
  signature mentions a class: `cupPowE`, `cupRightE`, `GysinSequence`, `MVFacts`, `lhMap`,
  `lhSum`, `lhTerm`, `LerayHirschGraded`, `gamma`, and the great majority of the layer.
* **`K` explicit and first, `Of` suffix, `F₂` name kept as an `abbrev`** — the handful whose
  arguments are only spaces and degrees: `MVSequenceOf`, `HasPointCohomologyOf`,
  `HasSphereCohomologyOf`, `HasCPCohomologyOf`, `lhDomainOf`.  `HasSphereCohomology` is the
  one that matters: **seven files outside my layer** consume it.
* **`K` implicit but pinned at partial applications** — `colPullOf`, `lhExtend`,
  `HasLowSurj`.  `Function.Bijective (colPull f r n)` has nothing to infer from.

**41 files outside my layer import mine**, all belonging to other lanes, so the `abbrev`
discipline at the seam is not optional.

## 2. Where the coefficient parameter stops

The abstract machinery ports; the concrete space does not.  Generic over `K` after today:
`MVSequenceOf K` and its three uses; the three shape predicates and their transports;
`hasCPCohomologyOf_succ`; `exists_sum_eq_of_lines` over a field; cup powers and the Gysin
sequence; `lhDomainOf` and the column; `MVPulls`, `MVLadder`, the four restriction squares,
the connecting square, and the three column-exactness statements; `lhMap`,
`LerayHirschGraded`, `lhCoeff`, `pull_injective` and the Chern classes `gamma` read off
`ξ^r`.

What does **not** port is `hasCPCohomology_CP`.  It rests on `CohomologyShapes`, hence on the
Kronecker / universal-coefficients layer where `kroneckerEquiv` takes **no coefficient
parameter** — `sp-coeff`'s mechanism (d).

### 2b. How much mechanism (d) gates: 80 files of 128

Computed, not estimated.  Taking the import closure of every file in my prefixes and asking
which contain `ProjectiveSpaceComputation`:

| | files |
|---|---|
| reachable **without** the concrete `ℂP^d` computation | 48 |
| behind it, i.e. behind mechanism (d) | **80** |

So the Kronecker port does not merely gate "Chern classes over `F_p`" as a headline.  It
gates **five eighths of this directory by file count**: the entire `CohomologyChart*` tower
above `CohomologyChartTop`, every `Projective*Ring*` file, the whole
`ChernEuler*`/`ChernSplit*`/`ChernGamma*` layer, and the `LerayHirschChart*`/`Col*`/`Free*`
chain that produces the `LerayHirschGraded` data the Gysin lane consumes.

Of the 48 reachable files, 23 are ported, 13 need no edit, one is `sp-coeff`'s, and the rest
wait on `TotalHOf` or on `sp-coeff`'s `mvSequence`/`cohZeroEquiv` over `K`.  **Checked, not
assumed, at 16:05:** `MayerVietorisElement` still states `mvExactW` at `Hmod2`, so
`mvSequence` is `F₂`-only and `LerayHirschMV` is blocked there; and `cohZeroEquiv` is
declared in `CohomologyContractible` and `CohomologySphere`, both still at `Hmod2`, so
`LerayHirschPoint` and `LerayHirschBase` are blocked behind mechanism (d) as well.  Neither
is a file I own, and this lane cannot route around either.  **That is this
lane's runway**: the abstract machinery is essentially finished and everything after it
waits on two of `sp-coeff`'s files and on the Kronecker port.

## 3. Design decisions

**The Mayer–Vietoris maps are `K`-linear** (§0.2).  Approved by the lead.

**`exact_W` keeps its `+`, and that is not a mod-2 residue.**  The classical middle map is
the difference; `exact_W` quantifies existentially over `b`, and negation is a bijection of
`H^n(V)`, so the two forms are the same statement over any ring.  The characteristic-two
step is in the *construction* (`MayerVietorisElement.mvExactW`), not in the structure.

**`colExactSum` is stated as the equality** `colResWU a = colResWV b`, matching
`exact_sum`'s own shape and sign-free.  `colExactSum_add` is the `F₂` "sum vanishes"
spelling that the five lemma used to consume.

**The ladder's middle map is `coprod f (-g)`.**  `AddMonoidHom.coprod f g` is
`(a,b) ↦ f a + g b`; the Mayer–Vietoris middle map is the difference.  One bridge lemma,
`coprod_neg_apply`, lets a square stated with `−` be applied to it.  Mathlib names checked
at the pin `81a5d257`: `AddMonoidHom.coprod_apply` is a `@[simp]` `rfl` lemma
(`Algebra/Group/Prod.lean:464`) and `AddMonoidHom.neg_apply` is the `to_additive` of
`MonoidHom.inv_apply` (`Algebra/Group/Hom/Basic.lean:274`).  "The lemma exists" and "the
lemma exists here" are different claims.

## 4. Mechanism (b): the dual tautological class

Both mechanism-(b) sites read, not grepped.

`ChernGammaBridge:78` proves `∀ w, w + w = 0` and uses it once, to move `ξ^r` across the
relation; over `K` that step is `eq_neg_of_add_eq_zero`.

`ChernSplitRelation:69` is the real one.  It proves the Grothendieck factor
`tautEulerOf p + π^*(lineEulerOf q)` restricts to zero on the locus where the tautological
line **is** `q`, and it does so because there the two Euler classes are **equal**, so their
sum is `x + x`.  Over `K` a sum of two equal classes is not zero.

**The fix is the dual tautological class**, `ξ = e(O(1))` rather than `e(O(−1))`.  Then
`c_r(π^*E ⊗ O(1)) = ∏(ξ + a_i) = 0` over any ring with the **honest** Chern roots, and on the
locus `O(1) = L_i⁻¹`, so the factor is `−a_i + a_i` and dies by `neg_add_cancel`.

**Ruled by the lead, 15:50** (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5, "Ruling on the
roots", on `sp-evenside`'s confirmation): with `ξ = e(O(1))` and `∏(ξ + y_l) = 0` the `y_l`
**are** the classical Chern roots, so `γ_k = e_k(y) = c_k` with no sign.  My own morning
formulation — that the roots are the negatives of the usual ones — is **retired**; it
described the old relation, the one written with `e(taut)`.  The ruling is stated in the
programme note and **pointed at** from `ChernRelation`'s `Conventions` block, not restated
there or anywhere else.  I checked that nothing in my prefixes restates it.
`ChernRelation` stays byte-unchanged, `γ_k = e_k(a)` is sign-free, and `sp-evenside`'s
Frobenius step is untouched.  Verified independently by `sp-coeff` and by `sp-design`.
**Approved provisionally by the lead.**

*Cost, corrected.*  I first wrote that this is free at `F₂` because `−x = x`.  That
equality is **propositional**, so an `F₂` call site naming `tautEulerOf` needs one rewrite
to meet a generic statement phrased with the dual.  Published accordingly, in
`LerayHirschChartClassGen.lean`:

```lean
def tautEulerDual (p : Bundle X ι) : Hmod2 (TopCat.of (Proj p)) 2 := -tautEulerOf p
theorem tautEulerDual_eq (p : Bundle X ι) : tautEulerDual p = tautEulerOf p
```

`sp-thom` read their four consumer sites rather than counting them: only **two** are
sensitive, the two that pass the class as the Leray–Hirsch generator inside a structure
application, where a propositional identification is the wrong shape because `rw` will not
cross a plain `def` under `LerayHirschGraded`.  The other two transfer for free, since
`pull` is additive and both a vanishing statement and a naturality equation survive negation
on both sides.  So no duals of the comap or vanishing lemmas are needed.

### 4b. The convention paragraph, and a correction to how I framed it

`sp-design` ruled: either Chern-root convention works, keep the mod-2 one, and **fix it in
exactly one place** — `ChernRelation.lean`'s `Conventions` block, which used to read "Over
`ZMod 2` — the only coefficient ring this project ever uses — signs are invisible anyway".

**I framed the rewrite wrongly and `sp-design` corrected it.**  I wrote the `φ` paragraph as
a counterfactual, "the opposite convention would have worked too".  It is not.  The tree
today uses `e(taut)`, so its roots are `y = −a`; I am proposing `y = a`; **that is the
change and `φ` is the change**.  So "does this break anything downstream" is live, and `φ`'s
two clauses are its answer, each licensing a different half of the tree.  I had the
mathematics right and its epistemic status wrong, which is worse in the file that is now the
single authority.

The block now reads in their order: (1) the choice is free, and *why the old sentence was
there* — it was true, because of two choices that have both since changed; (2) this file
fixes the convention and nothing else may; (3) `φ` as licence — at `p = 2` it is the
identity, so the `F₂` layer stays green without re-proof, which is why the switch is safe to
make now; at odd `p`, `p − 1` being even makes every weight component of `E_j` scale by the
same `(−1)^j`, so the Wu relations, the Frobenius step and the conclusion are covariant.
The paragraph closes by saying `φ` does **not** commute with `P` at `p = 2` for the odd-`p`
reason, and that folding the two together gives a sentence false for any non-identity
automorphism.

That closing sentence exists because `sp-coeff` independently asked me to check the exact
wording, having verified symbolically that `φ` commutes with `P` precisely when
`(−1)^p = −1`.  **Two lanes arrived at the same worry about one paragraph from different
directions on the same afternoon** — the strongest available signal that a sentence needs
writing carefully rather than merely correctly.

**Then a third pass changed it again, and the change is the interesting one.**
`sp-design` pointed out that `sp-coeff`'s condition, read in `F_p` rather than in `ℤ`, is
**uniform**: `(−1)^p = −1` holds at *every* prime, at odd `p` because `p` is odd and at
`p = 2` because `−1 = 1`; and so does the second step's `(−1)^{i(p−1)} = 1`.  So the
paragraph now states those two sign identities as **the thing being verified** — the
checkable form of the claim — and keeps the two reasons as its proof.  It does **not**
collapse to the uniform sentence, and `sp-design`'s reason is the sharpest thing anyone said
today: *"every sign is `+1` in `F_p`" is one sentence away from "signs are invisible over
`ZMod 2`", and it is more dangerous than the original because it is true.*

The paragraph also carries a provenance note, which is not decoration.  `sp-coeff` reached
the identity symbolically and did not see that it needs two reasons; `sp-design` reached the
two reasons from the failure at `p = 2` and did not see that they collapse to one identity.
Neither had it whole.  Without that sentence a future reader who finds only the identity
will take the two-reason structure for pedantry and tidy it away.

`sp-design` also caught a scope ambiguity in my closing sentence: "φ does not commute with
`P` at `p = 2` for the odd-`p` reason" parses as "(does not commute) for the odd-`p`
reason", which is false.  It now reads "at `p = 2` the odd-`p` reason does not apply, since
`p − 1` is odd there; `φ` commutes with `P` for the other reason."  In a file that is the
single authority, after a day whose whole problem was sentences true at one prime and false
at another, that is worth two extra words.

**A fourth pass, and `sp-coeff` retracted the caution that started it.**  Their symbolic
check had been performed in `ℤ`, where the two sides genuinely disagree at `p = 2`, rather
than in `F_p`, where the classes live and where they agree.  So the sentence I first wrote
on their authority — that `φ` does not commute with `P` at `p = 2` in that form — **would
have been false in the ring the statement lives in**.  It never reached the file, and it
never reached it because `sp-design` objected to it on grounds of *ambiguity*, not of truth.

**I first recorded that as "the pedantic reading caught a false claim it was not aimed at",
and `sp-design` corrected the credit.**  What they wrote was that the sentence reads two
ways, that I meant the second, and that the first is false — so they *did* identify a false
reading, and then attributed the true one to me, when the source I was transcribing had the
false one.  Had I meant the other reading, their message would have read as a wording quibble
and the false sentence would have shipped.  It was caught **by luck**, not by pedantry.  That
is the less comfortable moral and it is the true one, and I am recording it because the
comfortable version would license relying on a review process that did not actually do the
work here.

`sp-design` also supplied the clause the paragraph was missing: **which identity does which
job, and why there are exactly two**.  `φ` acts on a weight-`w` element by `(−1)^w`, one
sign per generator, so `(−1)^p = −1` is what makes `φ` commute with the **total** `P` on the
degree-two generators, while `(−1)^{i(p−1)} = 1` is what makes it commute with each **graded
piece** `P^i` — and the latter is the same computation that makes every weight component of
`E_j` scale by the same `(−1)^j`, so it is the identity the **Wu covariance actually
consumes**.  Two identities because two levels, generators and grading.  The block carries
their warning as a standalone sentence: do not delete the second as redundant, because a
reader who meets two identities with one job between them will drop one, and it will be the
second.  A caveat kept inside the thing it protects is the first casualty of a prose tidy.

The provenance note now records that the two halves were found by different **methods**, not
merely by different people — symbolic identity against failure at a specific prime — because
that is what tells the next reader which method to reach for at the next sign.  It closes on
the transferable line: **a check performed in the wrong setting reads exactly like a check**,
and that one erred toward extra caution, which is the kind nobody pushes back on.

*Scheduling cost, recorded because it is `sp-coeff`'s trap met from my side.*
`ChernRelation` was a named target of the gate now running, so fixing that sentence takes it
out of that gate under the content-based landing rule and it lands one cycle later.  I judged
an ambiguous sentence in the single authority to be worse than a one-gate delay.  The general
shape is that the content rule makes every edit a **scheduling** decision as well as a
correctness one, and the cost is invisible unless you are holding the batch.

`sp-design` also supplied a stronger argument than mine for why `sp-evenside` is untouched:
not "they inherit `γ_k = e_k(y)` either way", but that their `PowerData` takes the roots
**abstractly** and never fixes which they are, evidenced by their grep that `p − 1` occurs
in no statement or proof across their six green files.  That is structural and survives the
next landing; mine was a claim about signs cancelling and would not have.

**Their leak check, run twice.**  If the `K`-generic Chern files mention `(p−1)` or a degree
parity outside that one docstring, the convention has leaked.  Two hits across 128 files:
`ChernRelation.lean` itself, and `LerayHirschChart.lean:49`'s `isZero_odd_CP (hk : Odd k)`,
a parity of a degree that is a statement about the *space* and holds under either
convention.  `sp-design` agrees that is the hit the rule should let through.  Re-run per
batch.

## 5. Mechanism (a), and a third mechanism nobody had named

**In the chart tower it is `sub_eq_zero`, not a sign on a map.**  `CohomologyChartInduction:221`,
`CohomologyChartLowDegree:85`, `CohomologyChartRankTwo:62` and
`CohomologyChartRankTwoInterface:77` are one idiom: a class and an explicit model class are
shown to have the same restriction, and the mod-2 file forms their **sum** and calls it zero.
Over `K` one forms the difference and the step is `sub_self`.  Each is a two-token edit.

### 5b. The third mechanism: an identity in `+` that is false outside characteristic two

`LerayHirschShift`'s `add_cancel_pair` reads `w + x + (y + x) = w + y`.  It contains **no
characteristic-two token at all** — the token is one call away, in `LH.add_self` — so a
`ZMod 2` grep misses it entirely, and so does a search for `two_mul`, `2 = 0` or
`neg_one_pow`.

Over `K` the fix is not a sign on a map: the change of basis shifts the first coordinate by
`−cup b u` where the mod-2 file shifted by `+cup b u`, the same element at `F₂` and the
wrong one over `K`, after which the lemma dissolves into `abel` and is deleted.

**The reliable scan for mechanism (a) is over the *consumers* of the `F₂` service lemmas** —
`LH.add_self`, `LH.add_eq_zero_iff_eq`, `MayerVietorisBiproduct.add_self_eq_zero_two` and its
three corollaries — not over arithmetic tokens.  That sweep found exactly three sites in my
layer and all three are now cleared.

## 6. Order of work

Bottom-up by import, which is **not** the order in the launch message: `Projective*` and part
of `CohomologyChart*` sit *below* `LerayHirsch*`.  The lead has confirmed keeping it.

| batch | modules | state |
|---|---|---|
| 1 | `ProjectiveSpaceCohomology`, `ProjectiveSpaceRing`, `LerayHirschColumn`, `LerayHirschDegree`, `LerayHirschSquares`, `ProjectiveSpaceComputation` | authored |
| 2 | `LerayHirschInduction` over `K` | authored |
| 3 | `LerayHirschBridge`, `LerayHirschTransport`, `LerayHirschGradedIso`, `LerayHirschNatural`, `LerayHirschNaturalCoeff`, `LerayHirschHomotopy`, `LerayHirschCover`, `LerayHirschRankTwo`, `LerayHirschPeel`, `LerayHirschShift` | authored |
| 4 | `LerayHirschShiftTerm`, `LerayHirschTowerBridge` | authored (unblocked by `sp-cupone`) |
| 5 | `ChernClasses` and the `Wu.HasSplitting` producers | **waits on `TotalHOf`** |
| 6 | `ChernSplitRelation`, `ChernGammaBridge`, `ChernGammaComponent` | mechanism (b), waits on batch 5 |
| 7 | the chart tower and everything naming `CPtop d` over `F_p` | **waits on mechanism (d)** |

## GREEN (with job counts)

- nothing yet.  **No claim of green until there is a `Built` line per module.**

### The first gate failed, and what it cost

The clone was genuinely cold: zero `GroupApproximation` oleans, `purged 0 ... of 0 oleans`,
and the vendored `ThirdParty` singular-cohomology chain is largely serial, so the first pass
took forty-five minutes to reach my files.  It then aborted at the **first** of them:

```
error: ProjectiveSpaceCohomology.lean:170:47: unexpected token 'namespace'; expected 'lemma'
```

A `/-- … -/` doc comment immediately before `namespace MVSequence`.  A doc comment must
attach to a declaration; before a `namespace` it must be `/-! … -/`.  Three things worth
keeping:

* **The message names neither the cause nor a nearby token.**  It points at the `namespace`
  line, two below the `/--` that caused it, and asks for `lemma`, a keyword appearing
  nowhere near.
* **Read-verification cannot catch it.**  I re-read that file three times hunting for
  elaboration errors and never questioned a comment.  A mechanical sweep catches it: for
  every `namespace`/`section`, check whether the previous non-blank line ends `-/` and its
  block opens `/--`.  Run across all 128 files; exactly one site, now fixed.
* **On a cold clone the ordering of a gate is not a detail.**  `lake` aborts the whole build
  when any named target fails, so a syntax error in the module with the *smallest* closure
  costs the entire cycle and reports nothing about anything else.

The failed run built 43 modules with zero errors before aborting, including `CohomologyBasic`
and `CoeffCohomology`, so the second gate starts warm.

### A red in a peer's gate that was not mine, and the defect it exposed

`sp-tower`'s `cs-stages` gate reported **twelve errors in my `ProjectiveSpaceComputation`**.
They are a **torn build**, and chasing them found a defect in the shared probe helper.

The decisive evidence is two `ls -la`:

| module | olean built | its source |
|---|---|---|
| `ProjectiveSpaceCohomology` | 14:19 | 14:43 |
| `ProjectiveSpaceRing` | 14:23 | 14:36 |

**Both oleans predate their own sources.**  That clone compiled those two from the pre-edit
sources early in the run, my edits landed afterwards, and lake then reached the consumer —
whose source *had* been replaced — and elaborated the new consumer against the old imports.
Every error follows: `lineGen` reported with parameters `M` and `e` and no `K` is the **old**
`ProjectiveSpaceRing.lineGen`, which I deleted; `MVSequenceOf` unknown is the old
`ProjectiveSpaceCohomology`; `Line` and `exists_smul_of_line` unknown is the old
`ProjectiveSpaceRing`, which did not import `CoeffLine`.

**I verified my own sources rather than assuming**, because "stale olean" is the comfortable
answer and I have already been wrong that way today.  All five hold: `ProjectiveSpaceRing`
imports `CoeffLine` and declares no `lineGen`; `ProjectiveSpaceCohomology` declares
`MVSequenceOf` at line 90; `CoeffLine` declares `Line`, `exists_smul_of_line` and a `lineGen`
whose `K` is a named implicit; `ProjectiveSpaceComputation` imports `ProjectiveSpaceRing`.

**The cause: `laneprobe.sh`'s rsync is outside its own `flock`.**  The two rsync calls run
unlocked at the top; only the remote command takes the lock, and it wraps `purge_stale` and
`lake` only.  So a second probe launched into a clone that is still building does not queue —
it queues for the *build*, and its rsync overwrites the sources immediately.  `purge_stale`
runs once, at the start, under the lock, and is blind to a later overwrite.

Two tells distinguish this from a real missing import, and both are cheap:

* an **olean older than its own `.lean`** means the module was compiled from a version of the
  source that no longer exists on disk;
* **names from different upstream files resolving inconsistently in one error list** — here
  `Hmod K` resolved while `MVSequenceOf` did not — which no single missing import can produce.

The signature is what makes it dangerous: it reddens whichever file the build reaches after
the overwrite, normally the most recently edited one, so it reads as a genuine defect by the
author who most recently changed something.  Two readers took it that way.

**I did this three times today in my own clone** before I understood it, so anything my
overlapping runs reported after the second launch is uncitable, and I will not launch into
`stw-fix` again until the queued gate finishes.  Reported to the lead with the one-line fix
and a protocol fallback; the helper is shared and I do not own it.

### The gate now running

Twenty-nine targets: the twenty-three files I have edited, plus six unedited consumers, one
per seam — `MayerVietorisSequence` (the linear fields), `GysinPair` and `CohomologyShapes`
(other lanes, testing the `abbrev`s), `ProjectiveSpaceStable`, `ProjectiveSpaceRingEntry`,
and `LerayHirschPeelCP`/`LerayHirschPeelClosed` (the two `HasLowSurj` pins).
`LerayHirschChartClassGen` is named explicitly because `tautEulerDual` is a new declaration
already published to another lane, and a closure gate is blind to what nothing imports yet.

**What it certifies, checked rather than assumed.**  It synced at 15:25.  Listing every
`.lean` newer than that in the working tree gives fifteen files, of which **exactly one is
mine** — `ChernRelation`, edited at 15:34 to carry the lead's ruling and `sp-design`'s
refinement.  So this gate certifies 22 of my 23 files and `ChernRelation` lands a cycle
later, which I accepted when I chose an unambiguous sentence over a one-gate delay.  The
other fourteen are peers' and their absence is a feature: the gate builds them as of 15:25
rather than mid-edit.

The gate is itself valid despite having been launched under a running build.  Its rsync tore
the **earlier** run, not itself; its own build has not started, no further sync will land in
`stw-fix` because I am launching nothing else there, and `purge_stale` runs at its start.

The lead has confirmed the diagnosis, withdrawn both readings, and is replacing the helper
with `laneprobe2.sh`, which stages unlocked, then applies, purges and builds **under** the
lock, and writes an md5 snapshot of every source as built.  The snapshot is the half I would
keep even if the locking were free: today I had to reconstruct what my gate certifies by
comparing mtimes against a launch time, which is inference.  A snapshot turns "does this log
certify these bytes" into a diff, which is exactly the check the content-based landing rule
needs, and it makes the torn-build tell mechanical rather than something someone has to
notice.

## AUTHORED, UNVERIFIED

Twenty-three files, all mine except the one approved cross-lane edit.

| file | what changed |
|---|---|
| `ProjectiveSpaceCohomology` | `MVSequenceOf K` with `→ₗ[K]` fields; `MVSequence` as its `ZMod 2` `abbrev`; the three shape predicates as `…Of K` with `abbrev`s and `F₂` namespace aliases; `hasCPCohomologyOf_succ`; `toLinearZMod2` and `linearEquivOfBijective` deleted |
| `ProjectiveSpaceRing` | cup powers, the Gysin sequence and `cupPowE_ne_zero` generic; `exists_smul_cupPowE` over a field; the duplicate `lineGen` deleted |
| `ProjectiveSpaceComputation` | `exists_sum_eq_of_lines` generic over a field |
| `LerayHirschColumn` | `lhDomainOf K` + `lhDomain` `abbrev`; `MVFacts` and the five column maps |
| `LerayHirschDegree` | the whole file, including `gamma` |
| `LerayHirschSquares` | the whole file; `colPullOf`; `colExactSum` sign-free; `colExactSum_add`; `pull_sub` added beside `pull_sum` |
| `LerayHirschInduction` | the ladder's middle map is `coprod f (−g)`; `coprod_neg_apply`; `lhSum_pair` carries the difference |
| `LerayHirschBridge` | generic; `bijective_lhExtend` pinned.  **`bijective_lhSum_of_graded` is `sp-thom`'s highest-marginal item, delivered** |
| `LerayHirschTransport` | generic; needed a `variable {K}` of its own, the file having had no `variable` line |
| `LerayHirschGradedIso` | generic; its `#audit_axioms` is the plain form, which accepts a leading coefficient argument |
| `LerayHirschNatural`, `LerayHirschNaturalCoeff`, `LerayHirschTowerBridge`, `LerayHirschCover` | pure substitution |
| `LerayHirschHomotopy` | generic; three `colPullOf (K := K)` pins |
| `LerayHirschRankTwo`, `LerayHirschPeel` | substitution plus `pull (K := K)` |
| `LerayHirschShift` | mechanism (a); `add_cancel_pair` deleted, the shift carries `−` |
| `LerayHirschShiftTerm` | the one `cup_comm ξ` becomes `cup_comm_of_even_left even_two ξ` |
| `LerayHirschPeelCP`, `LerayHirschPeelClosed` | one `HasLowSurj (K := ZMod 2)` pin each |
| `LerayHirschChartClassGen` | `tautEulerDual` and `tautEulerDual_eq` published |
| `ChernRelation` | docstring only: the `Conventions` block |
| `ChernEulerBundle` | one `lineGen (K := ZMod 2)` pin |
| `MayerVietorisSequence` (sp-coeff's) | five `.toAddMonoidHom` deleted; approved by the lead |

A consumer sweep confirms self-consistency: every user of the coefficient-implicit
definitions is itself ported or carries a pin, and the `colPull` `abbrev` now has no
consumer outside its own file, the expected end state for a compatibility spelling once its
readers move over.

## NEEDS

**All answered.  Nothing blocks the reachable part of this lane.**

* `sp-cupone` landed `cup_comm_of_even_left` / `_right` in `CharClass/CupOneComm.lean`,
  green, hypothesis `Even p`, conclusion byte-identical to the `F₂` `cup_comm` with **no
  scalar**.  Batch 4 unblocked and done.
* `sp-coeff` fixed the names: **`TotalHOf K X`** and **`TotalPieceOf K X n`**, `K` explicit
  and first, operations in namespace `TotalHOf`, `ChernTotalRing.lean` with `F₂` `abbrev`s
  at the bottom.  It is *not* `TotalH K X` — that name is load-bearing in `sp-steenrod`'s
  `SteenrodTotal.lean`.  All three of us wrote `TotalH K X` naturally; none of us may.  The
  generic graded structure is `DirectSum.GRing`, and the `F₂` `GCommRing` is built **from**
  it rather than independently, to avoid a data-valued diamond.
* `CoeffLine` is green, names final, binder `[Field K]`.
* Mechanism (d) is now `sp-cupone`'s immediate task, assigned by the lead after I reported
  it; step 1 of 4 is green as `KroneckerClassifier`.

**One correction I owe `sp-coeff`, who refused a claim of mine and was right.**  I wrote
that `sp-evenside`'s Frobenius step "reads the same either way" under the two conventions.
That is a mod-2 habit: at odd `p`, `(−c)^p = −c^p`, so `∏(1 + y_i^p)` and `∏(1 + c_i^p)`
differ term by term.  Checking it produced a better answer than a correction would have —
the premise was false too, and the dual class removes the question (§4).

## TRAPS

- **A `/-- … -/` doc comment before `namespace` is a parse error**, and the message points at
  the `namespace` two lines below and asks for `lemma`.  Cost a whole cold-clone cycle.  Use
  `/-! … -/`.  Read-verification does not catch it; a mechanical sweep does.
- **`rw` cannot see past `LinearMap.toAddMonoidHom`.**  Generalising a structure field from
  `→+` to `→ₗ[K]` turns `rw [mv.exact_W m x]` into "did not find pattern" at a goal that
  prints as if it matched.  `refine Iff.trans (mv.exact_W m x) ?_` crosses it by defeq.
- **Two lanes declared `lineGen` independently, same namespace, same body.**  Invisible to
  every scan, because both are correct and neither file is red; the clash exists only in the
  future tree where one first imports the other.  Grep for the name of any small
  general-purpose lemma you put in a new leaf file, and grep two files against each other
  before adding an import between them.
- **A file inherits the coefficient through a NAME**, so a token census over-counts the
  zero-edit set by two and a half.  Classify by import closure.  `sp-coeff` §0b says this
  and I reproduced the mistake anyway: the token test *feels* like a measurement and is a
  guess.
- **Characteristic two hides in a `decide`, and in an identity written with only `+`.**
  `toLinearZMod2` is `∀ z : ZMod 2, z = 0 ∨ z = 1` by `decide`; `add_cancel_pair` is
  `w + x + (y + x) = w + y`.  Neither contains an arithmetic token.  Scan for the consumers
  of the `F₂` service lemmas.  Second tell: **a constructor that STRIPS structure to fit a
  field** is telling you the field is declared too weak, and the weakness gets paid for by a
  hypothesis somewhere downstream.
- **Shadowing a section `variable (K : Type)` with an explicit binder of the same name** may
  well be legal, and finding out costs a whole cold build.  Where a type-former genuinely
  needs an explicit coefficient, give it its own `section`; where every use applies the
  definition to something, make the coefficient implicit and the question disappears.
- **`purged 0 … of 0 oleans` does not mean clean**, it means the clone has no artifacts at
  all.  `lake`'s output is block-buffered into the probe log, so `grep -c Built` reading 0
  for half an hour is not evidence of no progress; count oleans on the node.
- **Not a Lean trap, and the most expensive one today.**  A `str.replace(old, new)` where
  `new` contains `old` and `old` occurs more than once grows the file geometrically.  I did
  this to this report and turned it into 168 MB of one duplicated section, with no git copy
  to restore because it was untracked.  Editing prose with slice-and-replace scripts is fine
  for one-shot substitutions and wrong for structural edits; for a structural edit, rewrite
  the section with `Write`.  And an untracked deliverable has no undo.
