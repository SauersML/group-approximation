# Lane `sp-thom` — the coefficient parameter `K` in the Thom / Gysin / Bundle / Slice layers

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5.  Clone: `ring-b-alg` (cores 12–17,
node `acn112`).  Owns `GroupApproximation/CharClass/{Thom,Gysin,Bundle,Slice}*` and the
`RelativeSupport` namespace where it is not inside a `LIX*` file.  Reads `sp-coeff.md` as binding
for the naming convention (§0c there) and for the base layer.

## 0. The census (2026-09-10, hour 1)

**111 files** carry the four prefixes: `Bundle*` 38, `Thom*` 44, `Gysin*` 10, `Slice*` 14 (plus
`ThomRelativeCokernel`, counted under `Thom*`).  Two independent classifications, both computed
rather than eyeballed, and they cut the job down twice.

**The whole lane accounts for as 57 + 11 + 43.**  57 files need no edit at all (already generic
over an abstract ring, or pure topology with no cohomology in them); 11 are authored over `K`
today; 43 wait on an upstream declaration, none of them on mathematics this lane owes.

### 0.1 How many files name the coefficient at all

| class | count | what it means |
|---|---|---|
| **already coefficient-free** | 57 | never writes `ZMod 2`, `Hmod2` or `cohomologyZMod2` anywhere in the file |
| **coefficient-pinned** | 54 | writes at least one of them |

The 57 are not "downstream-only" in sp-coeff's sense — they are *stronger* than that.  Most of
`Bundle*` (37 of 38) is **pure topology with no cohomology in it at all**: bundle spaces, charts,
frames, flags, local trivialisations, zero sections, block inclusions, pushforwards.  And the
core of the Thom development is already generic **over an abstract commutative ring**:
`ThomFreeModule.lean` opens `variable {R : Type*} [CommRing R]` and its docstring says in as many
words "this is *linear algebra over `R := H^*(X; F₂)`*, with no topology in sight".
`ThomClassChain`, `ThomFreeDegreewise`, `ThomChernBasis` inherit that.

So **the Thom class itself — its existence, uniqueness, and the freeness of `H^*(pair)` of rank
one on it — is already coefficient-generic and needs no port.**  That is the single most
load-bearing fact in this census and it was designed in, not lucky: `cc-thom` stated the whole
Leray–Hirsch input as hypotheses.

### 0.2 How many of the 111 are reachable now

Two upstream layers gate this lane, and they cut in different directions.

**(a) `Relative*` over `K`** (sp-coeff's next deliverable, plus relative homotopy invariance from
`sp-relhomotopy`).  **35 of the 111** have a `CharClass/Relative*` module in their transitive
import closure; **76 do not**.  The 35 are every `ThomBridge*`, every `ThomStepC*`,
`ThomChartSquare`, `ThomChartTautZero`, `ThomCoordinates`, `ThomDataFromLH`, `ThomFibreRestriction`,
`ThomHabs`, `ThomHyperplaneLH`, `ThomHyperSquare`, `ThomJmNatural`, `ThomRestrictSquare`,
`ThomSectionDetect`, `ThomSphereSubspace`, `ThomBundlePair`, `ThomChainHne`,
`ThomRelativeCokernel`, and six `Slice*`.

**(b) foreign-lane layers over `K`** — `LerayHirsch*`, `Projective*`, `Chern*`, `CohomologyChart*`,
`Steenrod*` — which this lane must not touch.  sp-coeff's own bottom-up order (§2 item 5 of their
report) puts `Thom*`/`Gysin*`/`Bundle*`/`Slice*` **last**, after `LerayHirsch*`, `Projective*` and
`Chern*`, so this lane sits at the top of the stack and its reachable set is whatever the layers
below have already made generic.

**That set moved twice during this lane's first hour, and the corrected version is below.**  When I
took the census, `cupPowE` and `cupRightE` (`ProjectiveSpaceRing.lean`) and `lhTerm`, `lhSum`,
`LerayHirschGraded` (`LerayHirschSquares`, `LerayHirschDegree`) were all still at `Hmod2`, and I
recorded them as this lane's blocking dependency.  Within the hour a peer landed all of them over
`K`, in exactly the convention below, and the Gysin layer became reachable.  The lesson is the
tree's own: **a blocker list computed from the working tree is a measurement, not a fact**, and in
a fleet sharing one tree it has to be re-measured before it is acted on, not quoted from an
earlier read.

The **measured** frontier, recomputed at 15:00, is one module deep and it is not where I expected:

| foreign module still at `Hmod2` | how many of this lane's 54 pinned files it blocks |
|---|---|
| `CohomologyBridge` | 42 |
| `CohomologyContractible`, `CohomologySphere` | 39 |
| `MayerVietorisBiproduct`, `MayerVietorisElement` | 37 |
| `CohomologyKunnethSphere`, `CohomologyProductCover`, `CohomologySphereZero` | 33 |
| `RelativeCochains`, `RelativeLES` | 31 |

**I first read that table as a leverage ranking and it is not one — corrected at 15:40.**
"42 of my files reach `CohomologyBridge`" is a count of closure MEMBERSHIP, and what matters is
the MARGINAL unlock: how many of my files become buildable if that module, and nothing else, goes
generic.  Measured greedily, the answer is brutal and it is the honest shape of this lane:

| ported next | frees | leaving blocked |
|---|---|---|
| `CohomologyBridge` | 1 (`BundleTotalPiCohIso`) | 43 |
| `CohomologyContractible` | 0 | 43 |
| `CohomologySphere` | 1 (`GysinSphere`) | 42 |
| `MayerVietorisBiproduct` | 0 | 42 |
| `MayerVietorisElement` | 1 (`GysinPairTaut`) | 41 |
| `CohomologyProductCover` | 1 (`ThomKunnethSphere`) | 40 |
| `MayerVietorisVanishing` | 3 | 37 |

**Nine upstream modules free seven of my files.**  This lane sits on top of a broad stack, not a
deep one, and there is no cheap high-leverage single item in it.  The practical consequence for
the lead's sequencing: do not reorder sp-coeff's bottom-up plan on my account — the cohomology
API has to go generic roughly as a block, and my layer follows it almost for free once it does.

**A caveat that cuts the other way, and both are in the same table.**  That scan calls
`Relative{Cochains,Dual,LES,SmallChains}` blockers, and per §0.2's own lesson they are not: those
files already take `(R : Type) [CommRing R]` everywhere, and what actually pins `ThomBridgeChart`
and `ThomBundlePair` is exactly two declarations, `excisionIso` and `relCohomologyCongr`.  So the
module-level scan has false positives in one direction and false leverage in the other; it ranks
candidates, and only reading the file decides.  Everything in the NEEDS section below is stated
at declaration level for that reason.

### 0.3 The naming recipe, instantiated for this lane

sp-coeff's §0c is binding and it decides every name here mechanically.

* **`K` implicit, name unchanged** wherever an argument has type `Hmod K …`.  `GysinData X P e`
  with `e : Hmod K X 2`, `topClass_eq_of_naturality`, everything in `ThomFreeModule`.  Every
  existing `F₂` call site is byte-unchanged because `Hmod2` is a reducible `abbrev`.
* **`K` explicit and first, `Of` suffix, `F₂` name kept as a reducible `abbrev`** wherever nothing
  determines it.  `PuncturedAcyclicOf K Z d z`, `CohomologyToolkitOf K`, `KunnethFactorOf K Y d`,
  with `abbrev PuncturedAcyclic := PuncturedAcyclicOf (ZMod 2)` and so on.  This is forced:
  `PuncturedAcyclic`, `KunnethFactor` and `CohomologyToolkit` are named by fourteen `LIX*` files
  (sp-oddside's `LIXKStepC*` and `LIXKGen*` among them), all of which must stay byte-unchanged.
* Classes: `[CommRing K]` everywhere in this lane except the two places a nonzero scalar is
  inverted (§0.4 (c)), which take `[Field K]`.

### 0.4 Where characteristic two is actually used in this lane

One file, and one line of one other.  Re-reading rather than grepping:

* `ThomFieldTwo.lean` — its `ZMod 2` occurrences are **all in docstrings**; the code is already
  `variable {R : Type*} [Ring R] [Finite R]`.  It survives verbatim at `K = ZMod p`.  What it does
  *not* survive is an abstract `[Field K]`, because `Finite K` is then unavailable — so this lane
  adds the field twin (`injective_of_surjective_of_line`), which needs no finiteness: a surjection
  between two lines over a field is injective because it is multiplication by a nonzero scalar.
  This is sp-coeff's mechanism (c) in this lane, and it is the whole of it.
* `GysinFromLerayHirsch.lean:118` and `GysinRanged.lean:84` write
  `rw [← neg_one_smul (ZMod 2) b', …]` to turn a subtraction into the mod-2 sum idiom.  Over `K`
  the same two lines read `neg_one_smul K`, which is true over any ring — the `ZMod 2` there is a
  type ascription, not an appeal to `1 = -1`.

**No file in this lane needs `1 = -1`, and no proof in it commutes two cup products.**  Chern
classes have even degree and the Thom development multiplies only in the abstract `R`-module
structure, so `sp-cupone`'s signed `cup_comm` is a dependency of my *imports*, never of my *proofs*.

## 1. Plan, in landing order

**Batch A (now, nothing upstream needed).**  Deliverables:
1. `ThomEulerNaturality` — `{HrelE HE HX HrelX : ModuleCat.{0} (ZMod 2)}` → `ModuleCat.{0} R`
   under the file's existing `[Ring R]`.  Pure substitution; its one consumer `LIXKStepC` is
   byte-unchanged because `R` is inferred from the morphisms.
2. `ThomFieldTwo` — add the `[Field K]` twin without `[Finite K]`; keep every existing declaration.
3. `ThomPuncturedRecursion`, `ThomPuncturedPi` — `cohomologyZMod2 X n` → `Hmod K X n`;
   `PuncturedAcyclicOf`/`CohomologyToolkitOf`/`KunnethFactorOf` with the `F₂` abbrevs.
   `ThomPuncturedCover` and `ThomPuncturedSphere` are pure topology and need no edit.
   `ThomKunnethNatural` and `ThomKunnethSphere` stay at `F₂`: they are the *instances*
   (`knPrY`, the sphere computation), not the machine, and they wait on `CohomologyKunneth*`.
4. **The Gysin layer**, which the peers' `ProjectiveSpaceRing`/`ProjectiveSpaceCohomology` port
   unblocked mid-hour: `GysinPair` (`MVSequenceOf K`), `GysinFromLerayHirsch` (`GysinData` with `K`
   implicit, determined by the Euler class), `GysinRanged`.  `GysinFromGraded` is one module short —
   it waits on `LerayHirschBridge` and `LerayHirschInduction`.
5. `ThomFreeModule`, `ThomClassChain`, `ThomFreeDegreewise`, `ThomChernBasis` — verified generic,
   no edit; recorded here so nobody ports them twice.  `ThomFreeModule.lean:45` reads
   `variable {R : Type*} [CommRing R]` and every declaration below it is over that `R`.

**Batch B (after sp-coeff's `Relative*`/excision over `K` and sp-relhomotopy's invariance).**
The remaining `Relative`-reaching files.  The site-by-site substitution map is prepared in
`scratchpad/sp-thom-batchB.md`; regenerate it before acting on it.

**One Batch B decision that is design, not substitution, and it should be made now.**
`ThomStepCEuler.lean:59` is this lane's only genuine appeal to characteristic two:

```lean
have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
```

used to prove `eq_localGenerator_of_ne_zero` — *a nonzero element of the local line **is** the
generator*.  That statement is **false over any other field**, so it must not be ported; over `K`
a nonzero element is a **unit multiple** of the generator (sp-coeff's
`CoeffLine.exists_ne_zero_smul_of_line`).  The right move is not to carry the unit around.  Look
at what the file exports: `hsu_of_ne_zero` and `ne_zero_of_hsu` are already an iff between
"`su ≠ 0`" and "`su` maps to the generator", and every consumer downstream of them —
`topChernClass_ne_zero_of_su_ne_zero`, and Step C itself — concludes `gamma ≠ 0`.  **So over `K`
the generator identification is dropped and only the `≠ 0` side is kept**: `hsu_of_ne_zero`
becomes `(exc ≪≫ chartIso).hom.hom su ≠ 0`, which is what the iso gives for free, and
`ne_zero_of_hsu` becomes redundant.  The `F₂` pair stays where it is, unported, with the
`decide` and a docstring saying it is special to mod-2 — which its own docstring already
half-says.  Net effect: the mod-`p` Step C carries no unit and no scalar bookkeeping at all.

**And the assembly is already in that shape, which is the part worth telling the odd side.**
`EulerLocalAssembly.topChernClass_ne_zero_of_chain` takes `hsu : (exc ≪≫ chartIso).hom.hom su = g`
together with `hg : g ≠ 0` — an *arbitrary* `g` with an explicit nonvanishing hypothesis.
`ThomStepCLocal` is the only thing that specialises `g` to `localGenerator r` and discharges `hg`
with `localGenerator_ne_zero`.  So over `K` that instantiation becomes `g := (exc ≪≫
chartIso).hom.hom su`, `hsu := rfl`, and `hg` is the hypothesis the caller already has.  **No
lemma has to be reproved and no unit is ever named** — the only mod-2 step in this lane's Step C
chain disappears by choosing a different instantiation of a theorem that is already generic.

**Batch C (after the rest of `LerayHirsch*` and `Chern*` over `K`).**  `GysinFromGraded`
(`LerayHirschBridge`, `LerayHirschInduction`), `ThomChernDegreewise` (`CohomologyLHDegreewise`'s
`LHCast`), `ThomHabs`, `ThomJmNatural`, `ThomHyperplaneLH`, `ThomRestrictSquare`, and the `Slice*`
files that compute with `chernClass`, `TotalH`, `eulerOfBundle` or `lineEulerOf`.  Nothing in
Batch C is mathematics; it is substitution waiting on names that do not exist yet.

## GREEN (with job counts)

- Nothing claimed green yet.  The baseline warming probe of the layer's 13 maximal modules ran
  on the cold `ring-b-alg` clone and its purge line is worth recording as evidence for the fleet
  rule rather than as a lane fact:

  ```
  purged 2693 stale artifact sets (source-newer=150, import-newer=2543) of 4466 oleans
  ```

  **Sixty percent of the clone was stale, and 94% of that was import-newer, not source-newer** —
  i.e. invisible to the first version of the purge criterion and invisible in the build log.  A
  green obtained in this clone before the transitive purge existed would have meant nothing.

- Under the fleet rule, this lane's own artifacts are cleared and the gate re-run before anything
  is cited (`scratchpad/sp-thom-clear.sh`, then `scratchpad/sp-thom-gateA.sh`, chained so the
  clear cannot run while a probe holds the clone).

- **How to read that baseline when it lands, and it is less than it looks.**  Its `rsync` was at
  14:29, before any of this lane's edits, so a green from it attests to the shared tree *at 14:29*
  and to nothing about my work.  Eighty minutes later that is not a tree state anyone can act on.
  I considered killing it to free the clone lock sooner and checked the remote process list first:
  it is six `lean` processes wide on `LerayHirschPoint`, `SteenrodCupOne`,
  `ProjectiveSpaceTwoCover`, `BundleLineTriv`, `BundleProjOver` and the vendored
  `SphereModTwoTopGeneratorData` — i.e. exactly the tower that phase 2 has to build anyway.
  Killing it would have discarded 45 minutes of work rather than saving any, so it runs.  The
  lesson generalises: a stale baseline is worthless as *evidence* and still valuable as *warming*,
  and those two are worth separating before reaching for `kill`.

  **Two hours later I revisited that and tried to kill it, and both the attempt and the premise
  were wrong.**  The premise: by then peers had landed enough that much of what the baseline was
  rebuilding from a 14:29 source had changed under it, so its warming value looked eroded.  The
  attempt: `pkill -u sauer354 -f 'cc_clones/ring-b-alg.*bin/lean'` matched nothing, because the
  real command line puts `bin/lean` *before* the clone path — and `pkill` says nothing when it
  matches nothing, so it looks exactly like success.  `ps` afterwards showed the workers alive and
  new ones spawning.  Checking again then showed the premise had also gone stale: the jobs then in
  flight were `MayerVietorisVanishing`, `ProjectiveSpaceIterate` and `EulerLocalChart`, all inside
  my own gate's closure.  So the baseline runs, no damage was done (zero errors, zero signal
  traces in the log), and the honest account is that I was wrong twice and the check caught it
  both times.

- **What a red in phase 2 will and will not mean.**  Phase 2 rsyncs at its own start, which by now
  is well after sp-coeff's eight additive declarations and whatever sp-lh lands next.  A red there
  on a file I do not own is a tree-state observation, not a lane failure, and it is why phase 1
  exists: phase 1 builds only my thirteen, so it is the load-bearing evidence for this lane's own
  code, and phase 2 is the batch-level question that is inherently a moving target in a shared
  tree.

## AUTHORED, UNVERIFIED

Thirteen modules, three coherent layers, all `[CommRing K]` (or `[Ring K]` where no
multiplication of classes occurs), no `sorry`, nothing outside this lane's prefixes.

**(i) The punctured-product recursion over `K`** — and this layer had the second red of the day,
found the same way as the first, by grepping every peer clone's newest log for my own file names
rather than waiting for my cycle.  `spare2` reported
`Invalid field notation: Function 'KunnethFactorOf.mono' does not have a usable parameter of type
'KunnethFactor …'` at `ThomKunnethSphere:51`, on `(kunnethFactor_of_contractible _).mono`.
**The `export` aliases I added for compatibility are what broke it.**  Dot notation takes the head
constant of the type as written, `KunnethFactor`, finds `KunnethFactor.mono` (my alias), and then
requires a parameter headed by `KunnethFactor` — the aliased declaration's parameter is headed by
`KunnethFactorOf`.  Without any alias it would have worked, because Lean whnf's the reducible
`abbrev` and finds `KunnethFactorOf.mono` by itself.  So the aliases are gone and the three names
that are actually used by *qualified* spelling — `PuncturedAcyclic.prod`, `.congr`, `.congr'` —
are real wrapper theorems whose binders are spelled with the `F₂` `abbrev`s, which makes both
notations work.  `X.f` and `Namespace.f x` resolve by different rules; an alias helps the second
and destroys the first, and they have to be audited separately.

The layer itself: — `ThomPuncturedRecursion`, `ThomPuncturedPi`.
`CohomologyToolkitOf K`, `KunnethFactorOf K`, `PuncturedAcyclicOf K`; the recursion
(`PuncturedAcyclicOf.prod`), both base cases, `mono`, `kunnethFactor_of_prodEquiv`, and the two
transport lemmas `congr`/`congr'`.  `K` is implicit throughout — the toolkit, the Künneth factor
or the acyclicity datum always determines it — and the `F₂` spellings are reducible `abbrev`s
plus `export` aliases, so the **fourteen** `LIX*` files that name one of the three, both
`LemmaTwoStepC` files and `EulerLocalNonvanishing` are byte-unchanged.  (I wrote "eight" first,
from a grep run an hour earlier; sp-oddside has added `LIXKGenSphere` and `LIXKGenPunctured`
since.  Counted again before claiming it.)  This is what Step C over `F_p` will consume.

**(ii) The Gysin step over `K`** — `GysinPair` (over `MVSequenceOf K`), `GysinFromLerayHirsch`
(`GysinData` with `K` implicit, determined by the Euler class), `GysinRanged`.  Unblocked
mid-hour by the peers' `ProjectiveSpaceRing`/`ProjectiveSpaceCohomology` port.  The only place
that looked like characteristic two — `neg_one_smul (ZMod 2)`, turning a difference into the
mod-2 sum idiom — is true over any ring.

**(iii) Relative-pullback naturality over `K`** — `ThomBridgeNaturalHyper`,
`ThomBridgeNaturalSquare`, `ThomHyperSquare`, `ThomFibreRestriction`, plus one pinned token
each in `ThomChartSquare` and `ThomBridgeChartHom`.

> **This layer was red and is fixed; the diagnosis is the reusable part.**  sp-tower's gate on
> `cs-stages` synced the shared tree at 15:06, built my `ThomHyperSquare` edit an hour before my
> own cold clone could reach it, and reported `59:2 Type mismatch` with a second, spurious
> `sorryAx` audit error from the failed elaboration.  The message read
> `has type relPullback (ZMod 2) … but is expected to have type relPullback K …`, which looks
> like the caller naming the wrong coefficient and is not.  `relPullback_id_comm` had `{K}`
> **implicit** while its explicit arguments are a map, four map-of-pairs proofs and a degree —
> **nothing that mentions `K`** — so `?K` was still unassigned when the `[CommRing ?K]` goal was
> discharged and instance search picked `ZMod 2` for it.  This is sp-coeff's implicit-coefficient
> trap in a nastier form: theirs reports "typeclass instance problem is stuck", mine silently
> committed.  §0c already had the rule and I broke it in all four of these theorems; the fix is
> `(K : Type) [CommRing K]` in the `variable` line, exactly as `relPullback` itself takes
> `(R : Type)` explicitly, plus `(ZMod 2)` at the two `F₂` call sites.  I audited the other nine
> modules for the same shape — a theorem mentioning `K` with no class among its arguments — and
> there are none: everywhere else the toolkit, the Künneth factor, the acyclicity datum, the
> Mayer–Vietoris sequence, the Euler class or a linear equivalence determines it.  These were in my
"blocked on `Relative*`" column and should not have been: what they use is `relPullback (R)`,
`relPullback_comp (R)` and `relPullback_eq_of_eq (R)`, all of which already carry
`(R : Type) [CommRing R]`.  The token `ZMod 2` in them was never anything but the coefficient
*argument*.  Same lesson as §0.2, one level down: a module in the closure that still names
`ZMod 2` does not mean the declaration you use from it does.

**(iv) Verified generic, no edit needed** — `ThomFreeModule`, `ThomClassChain`,
`ThomFreeDegreewise`, `ThomChernBasis`, `ThomPuncturedCover`, `ThomPuncturedSphere`, and 37 of
the 38 `Bundle*` files.  Recorded so nobody ports them twice.

**Gate, in two phases.**  Phase 2 is the real one: the 17 maximal importers of the thirteen,
covering all 277 modules that reach them, with `Manuscript.NinetyNineProblems.ProblemLIX` inside
the gate — so it checks the verified mod-2 answer, not just my own directory.  The thirteen are
named on the same command so the log carries a `Built` line for each.

Phase 1 builds only the thirteen.  sp-coeff's rule "do not put a cheap new leaf in the same probe
as the expensive tops" is usually read as protecting the tops from the leaf; it protects the
author from the tops just as much.  Phase 2 rebuilds 266 downstream modules, so a mistake of mine
would surface an hour after I made it; phase 1 surfaces it in minutes, and phase 2 runs only if
phase 1 is green — a red phase 1 means the expensive run would have aborted on my file anyway.

## NEEDS

- **From sp-coeff: `CohomologyBridge` over `K`**, which they have now read declaration by
  declaration and answered.  It is `[CommRing K]` throughout with **no field binder**, and the one
  step that could have been expensive is not: the vendored
  `SingularCohomologyHomotopyInvariance.lean` is generic in `(R : Type) [CommRing R]` all the way
  through, and its `ZMod 2` forms are one-line specialisations.  Six names take an explicit `K`
  because none of them has a class argument, and I will call them by these spellings:
  `pullEquivOfHomotopyEquivOf`, `pullEquivOfHomeomorphOf`, `pullEquivOfIsoOf`,
  `cohProdContractibleOf`, `cohProdUnitIntervalOf`, `cohProdEuclideanOf`.  `pullMap` and
  `restrictTo` keep their names and gain an implicit `K`, because the class is their last
  argument.  `BundleTotalPiCohIso` is the only file of mine it frees on its own; it is named here
  because it is the *first* thing every other blocked file of mine also needs, not because it is
  high leverage by itself.
- From sp-coeff, in their own bottom-up order and not reordered on my account:
  `CohomologyContractible`, `CohomologySphere`, `MayerVietoris{Biproduct,Element,Vanishing}`,
  `CohomologyProductCover`, `CohomologySphereZero`, `CohomologyKunnethSphere`.
- ~~`excisionIso` and `relCohomologyCongr` over `K`~~ — **landed by sp-coeff at ~15:50 as
  `excisionIsoOf K` (`RelativeExcision.lean:295`), `relCohomologyCongrOf K`
  (`RelativeLocal.lean:61`) and `absToSub_eq_cohPullbackOf K` (`RelativeLES.lean:49`), with the
  `ZMod 2` originals kept.**  `ThomBridgeChart` and `ThomBundlePair` are now ready and are the
  first two files of Batch A2.  I am deliberately **not** adding them to the batch currently at
  the gate: those three declarations are minutes old and unprobed, so building on them would make
  a red in my phase 1 mean a peer's file rather than mine, and the landing rule is that a batch
  must be green as a tree state.  They go in the next batch, after sp-coeff's Relative layer has
  its own green.  The patch is written and waiting in `scratchpad/sp-thom-batchA2.md`, with one
  decision in it worth stating here because it is not the obvious one: **the generic forms go in
  ADDITIVELY, beside the `F₂` originals, not as `abbrev`s over them.**  `excisionIso` and
  `excisionIsoOf (ZMod 2)` are separate declarations going through different instance terms
  (`isIso_excision` versus `isIso_excisionOf`), so they are not definitionally equal, and an
  `abbrev` bridging them would silently change what `bridgeChart` unfolds to —
  `ThomBridgeChartHom` proves `(bridgeChart p n).hom = relPullback (ZMod 2) …` by `show`/`rw`,
  which is exactly the proof shape that breaks on a changed unfolding.  This is sp-coeff's own
  discipline one layer up: an additive declaration cannot redden a consumer, a rewrite of a live
  definition can, which is why their eight were safe to land unprobed and their `ChernTotalRing`
  rewrite was not.
- **A design consequence of that landing, worth knowing before the Thom bridge is ported:**
  `excisionIsoOf` asks for `[Field K]`, not `[CommRing K]`.  I had guessed this was a porting
  artefact; sp-coeff corrected me and the correction is structural.  Excision rests on
  `isIso_excisionOf`, which rests on the acyclicity of the small-annihilator complex, which is the
  dual of a quasi-isomorphism being a quasi-isomorphism, which holds because the coefficient is
  injective as a module over itself.  Over a general commutative ring the dualizing functor is not
  exact and the statement is **false**, so no amount of work removes the binder.  The same
  dependency sits inside `RelativeDual`, `RelativeSmallChains` and `CohomologyMayerVietoris`
  without any of them naming a field — it enters through a single instance argument, which is
  worth knowing as a pattern: a file can look coefficient-clean and still rest on injectivity.  So the Thom bridge over `K` carries
  `[Field K]` from `ThomBridgeChart` upward, while the punctured layer, the Gysin step and the
  naturality squares landed today stay at `[CommRing K]`.  That is the right boundary to keep: a
  hypothesis used once is an over-ask, and only the excision step uses it.
- Not needed after all: `Relative{Cochains,Functorial,LES}` over `K`.  I had these in the
  blocking column; in fact `relPullback`, `relPullback_comp`, `relPullback_eq_of_eq` and
  `relCohomology` all already carry `(R : Type) [CommRing R]`, and the `ZMod 2` left in those
  files is a docstring line and one `rfl` bridge.  Four of this lane's files moved from Batch B
  to Batch A on that reading.
- From sp-relhomotopy: relative homotopy invariance over `K` (Batch B).
- **Retracted:** `cupPowE`/`cupRightE`/`lhTerm`/`LerayHirschGraded` over `K`, which I asked the lead
  for at 14:40.  They had already landed; see §0.2.

## Upstream names this lane must write against, as confirmed by their owners

Collected because three name assumptions of mine were already settled differently in the tree, and
each wrong guess is a probe cycle.  **These are the spellings, not the shapes.**

| what I would naturally write | what it is called | owner |
|---|---|---|
| `TotalH K X`, `TotalPiece K X n` | **`TotalHOf K X`, `TotalPieceOf K X n`**, operations in namespace `TotalHOf` | sp-coeff |
| `HasSphereCohomology` over `K` | **`HasSphereCohomologyOf K X m`**, `.of_linearEquiv` on it | sp-lh |
| `pullEquivOfHomotopyEquiv` over `K` | **`pullEquivOfHomotopyEquivOf K e n`**, likewise `…HomeomorphOf`, `…IsoOf`, `cohProdContractibleOf`, `cohProdUnitIntervalOf`, `cohProdEuclideanOf` | sp-coeff |
| `pullMap` over `K` | **unchanged**, `K` implicit — the class is its last argument.  Same for `restrictTo` | sp-coeff |
| `excisionIso` over `K` | **`excisionIsoOf K`, and it takes `[Field K]`** | sp-coeff |
| `lhDomain` over `K` | **`lhDomainOf K`**, and `colPullOf` | sp-lh |
| the dual tautological class | **`tautEulerDual p`**, bridge **`tautEulerDual_eq`**, both in `LerayHirschChartClassGen.lean` beside `tautEulerOf`, same section variables | sp-lh |

The graded total ring over `K` is `DirectSum.GRing`, **not** `GCommRing`: `mul_comm` quantifies
over all degrees and is false at odd `p`.

**And one shape change that is not a rename.**  sp-lh reports that over `K` the Grothendieck
relation needs the **dual** tautological class `ξ = e(O(1))`, not `e(O(-1))`: the mod-2 split
relation vanishes because two equal Euler classes sum to zero, which is false over `K`, and with
the dual class the factor vanishes by `neg_add_cancel`.  At `F₂` the two agree, but only
*propositionally*.  I read my four `tautEulerOf` sites rather than counting them, and only **two**
are sensitive: `ThomBridgeTotal` and `ThomHyperplaneLH` pass the class as the Leray–Hirsch
generator, where it sits inside a `LerayHirschGraded` application in a *statement* and cannot be
rewritten under.  `ThomChartTautZero`'s two vanishing lemmas and `ThomJmNatural`'s `comap`
naturality transfer for free, because `pull` is additive and both a vanishing statement and an
equation survive negating both sides.  So the ask to sp-lh is one `def` plus one `F₂` bridge, not
a dual of every lemma.  They have landed exactly that and are not writing duals of the `comap` or
vanishing lemmas.  **Both are at `Hmod2` today, not over `K`** — `tautEulerOf` sits at in-layer
closure 75 and its whole euler-class chain is still `F₂` — so what exists now is the *spelling*,
which is the part that matters, because it will not move under me.  The generic phrasing, with
`LerayHirschGraded` data over `K` stated with the dual directly rather than through a bridge I
would have to rewrite under, arrives with their batches 4 and 5.  They offered to reorder toward
that chain if I needed it sooner and I declined: `ThomBridgeTotal` and `ThomHyperplaneLH` are
blocked on much more than this, so a reorder would buy nothing and cost their bottom-up order.

## What three reds cost, and what found them

None of the three was found by my own probe, which after two hours had still not reached any of
them.  All three came from peers' gates on warm clones, and the way I looked for them got
progressively less wrong.

| red | where | found by |
|---|---|---|
| `ThomHyperSquare:59` type mismatch | my file | sp-tower's gate, relayed by the lead |
| `ThomKunnethSphere:51` invalid field notation | my file | my grep of every clone's newest log, filtered to my four prefixes |
| `EulerLocalNonvanishing:90` invalid field notation | **a file I do not own, untouched since 09-05** | sp-oddside told me; my filter was blind to it |

**The third is the one worth keeping.**  When you re-shape a widely consumed declaration the reds
land in *consumers*, which by definition are other people's files, so filtering peers' logs by
your own filenames is exactly the wrong filter — and it is the natural one to reach for.  Grep
`^error:` with no filename filter and read the whole list.  A red in a file nobody has touched in
five days is the signature of your own landing, not of theirs.

Two of the three had the same root cause and it was my compatibility layer, not my mathematics.
The generic port itself was right in all thirteen files; what broke was the `F₂` bridge.

## TRAPS

- The `RelativeSupport` **namespace** is not a `RelativeSupport` **file**: there is no
  `CharClass/RelativeSupport.lean`.  Its declarations are spread over `RelativeSubspaceIso`,
  `RelativeProdContractible`, `RelativeSubspaceIso`, `LIXStepCOddRelative`, `LIXHsqNeighbourhood`
  and others — i.e. across two other lanes' file prefixes.  Anyone told they "own RelativeSupport"
  owns a namespace with no file of its own and must resolve ownership by file, not by namespace.
- **A dependency census is perishable in a shared tree.**  Mine was 40 minutes old and two of its
  three named blockers had been retired in the meantime, by a peer, in the same convention I was
  about to ask for.  I had already sent the lead a request for one of them.  The cheap guard is to
  re-run the closure scan immediately before acting on it and immediately before reporting it, and
  to report the frontier as a measurement with a timestamp rather than as a fact about the tree.
- **The blocking test is per-declaration, not per-module**, and getting it wrong keeps shippable
  work in the queue.  Classifying by "the closure contains a module that still names `ZMod 2`" put
  every `ThomBridge*` file behind `Relative*`; reading them instead showed that what they use from
  there is `relCohomology`, `relPullback`, `relPullback_comp` and `relPullback_eq_of_eq`, all of
  which already carry `(R : Type) [CommRing R]`.  Four files moved from Batch B to Batch A on that
  reading.  Use the closure scan to rank candidates, then read the file to decide — and when you
  report a blocker, name the **declaration** (`relCohomologyCongr`, `RelativeLocal.lean:61`), never
  the module: a module-level blocker is usually two definitions wide and someone can retire it in a
  minute.
- Three names this lane exports are structures that eight `LIX*` files use.  Turning
  `PuncturedAcyclic` into an `abbrev` for `PuncturedAcyclicOf (ZMod 2)` keeps every *type*
  ascription and every anonymous constructor working, but it does **not** by itself keep the
  qualified spellings `PuncturedAcyclic.congr'`, `KunnethFactor.mono` and so on working, because
  the theorems moved to the `…Of` namespace.  `export …Of (names)` inside `namespace …` restores
  them as aliases, and it is the piece that is easy to forget: the type-level compatibility is
  what you check, and the term-level one is what breaks.
- Counting a lane's work by "files that name `ZMod 2`" **overcounts** here and undercounts
  elsewhere.  37 of my files name the token; 54 are coefficient-pinned (the extra 17 speak only
  `Hmod2`); and of the 37, `ThomFieldTwo`'s 3 occurrences are all in docstrings over code that is
  already generic.  Grep the token, then read the file: the token is neither necessary nor
  sufficient for work.
