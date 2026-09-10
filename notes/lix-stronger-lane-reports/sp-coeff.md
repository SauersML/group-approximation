# Lane `sp-coeff` — the coefficient parameter in `GroupApproximation/CharClass/`

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5 (first bullet).
Clone: `cs-endpoint`.  Owns: `GroupApproximation/CharClass/` except
`Steenrod*`, `Cartan*`, `Parity*`, `Wu*`, `Sq*`, `Acyclic*`, `LIX*`.

## 0. The census (2026-09-10, hour 1)

`CharClass/` has **546** files, **340** in this lane's scope and **206** out of it
(`Steenrod|Cartan|Parity|Wu|Sq|Acyclic|LIX` prefixes).  Of the 230 files that name
`ZMod 2`, **96 are in scope** and 134 are out of scope.  So the coefficient
parameter touches at most 96 files, not 230.

The decisive fact, and the one that makes this lane far smaller than the file
count suggests: **the layers under `CharClass` are already generic in the
coefficient ring, and most `CharClass` files simply instantiate them at
`ZMod 2`.**  `relCohomology (R)`, `relPullback (R)`, `relToAbs (R)`,
`absToSub (R)`, `subChainComplex (R)`, `smallAnnComplex (R)`, `dualFunctor (R)`,
`mvLeftChainMap (R)`, `mvInclU_small (R)`, `cochainCx (R)` and the whole vendored
`CupProduct.lean` all take `(R : Type) [CommRing R]`.  In those files the port is
the substitution `(ZMod 2) ↦ K`, nothing more.

Classification of the 340 in-scope files:

| class | count | what it means |
|---|---|---|
| **downstream-only** | 234 | never names `ZMod 2` in code; speaks `Hmod2`/`cup`/`pull` only, and follows for free once `Hmod2` is `Hmod (ZMod 2)` |
| **formal** | ~86 | names `ZMod 2` only as a coefficient argument to an already-generic function, a `ModuleCat`/`→ₗ[·]`/`Module` ascription, or a `≃ₗ[ZMod 2] ZMod 2` "this group is a line" hypothesis.  Mechanical substitution. |
| **uses characteristic 2** | 25 | four distinct mechanisms; see §0 and the correction in §0b |

The 20 files that genuinely use characteristic 2, grouped by mechanism:

**(a) the Mayer–Vietoris sign convention — 13 files.**  `MayerVietorisBiproduct`
proves `add_self_eq_zero_two : x + x = 0` from `(1 : ZMod 2) + 1 = 0` (l.58-60,
`decide`) and three corollaries, and the MV difference map is written as a *sum*
`a|_ + b|_` rather than `a|_ − b|_`.  Consumers:
`MayerVietorisPull` (l.114), `MayerVietorisElement` (l.205),
`CohomologyKunnethSurj` (l.93-114), `CohomologyKunnethSurjZero` (l.170-210),
`CohomologyKunnethDecomp` (l.78,86), `CohomologyChartInduction` (l.221-253),
`CohomologyChartLowDegree` (l.85,88), `CohomologyChartRankTwo` (l.62,65),
`CohomologyChartRankTwoInterface` (l.77-128), `CohomologyDeltaChain` (l.56),
`LerayHirschInduction` (l.142), `LerayHirschShift` (l.40).
Over `K` the map carries the sign and every `add_self_eq_zero_two` becomes
`sub_self`.  The vendored chain-level SES already has the signed maps, so this is
a wrapper change, not a mathematical one.

**(b) `2 = 0` inside a relation — 3 files.**  `ChernGammaBridge` (l.78),
`ChernSplitRelation` (l.69) and `LerayHirschSquares` (l.68) all read
`rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0, zero_smul]` to delete a term.
Over `K` the term stays and the relation carries the sign.  `LerayHirschSquares`
also proves `a + a = 0` and `-b = b` on `Hmod2` (l.67-73) and uses them at l.518.

**(c) "`F₂` has exactly one nonzero element" — 5 files.**
`ProjectiveSpaceCohomology` (l.56, `∀ z : ZMod 2, z = 0 ∨ z = 1`),
`ProjectiveSpaceRing` (l.58-59, same, and `lineGen`),
`RelativeLineHomotopy` (l.72, `x ≠ 0 → y ≠ 0 → x = y`),
`ThomStepCEuler` (l.59, `c ≠ 0 → c = 1`),
`CohomologyKunnethInjective` (l.65, `x ≠ 0 → x = 1`).
Over a field `K` these become "nonzero implies a **unit** multiple of the
generator".  This is the only place `[Field K]` is genuinely needed, and it is
where `LemmaTwoStepCEuler`'s own docstring already warns "**This is special to
mod-2 coefficients.**"  Two further files, `CohomologyMayerVietoris` and
`RelativeDual`, need `Module.Injective K K`, which a field has.

**The real blocker is below `CharClass`, in the vendored layer**, and it is one
theorem:

* `ThirdParty/.../CupProduct.lean` — **generic in `R`** (`singularCochainGroup (R) [CommRing R]`,
  `cochainCup`, `cochainEval`, `cochainCast`, `cochainOne`, `cochainPullback`,
  `cochainPow`, bilinearity, naturality, `cochainCup_one`).  Nothing to do.
* `ThirdParty/.../AlexanderWhitneyChainMap.lean` — `cochainCoboundary (R) [CommRing R]`
  and its evaluation formula `(δφ)(σ) = Σ_i (-1)^i φ(d_i σ)` are **generic in `R`**, and
  so are all the simplex-level face identities.  But the **Leibniz identity
  `aw_cochain_leibniz_zmod2` is proved only at `ZMod 2` and genuinely uses
  `(-1)^k = 1`** (`neg_one_pow_zmod2`, l.258, and `sum_split_char2`, l.226, which
  needs `∀ x, x + x = 0`).  This is the single mathematical obstruction in the
  whole stack.
* `ThirdParty/.../CochainCupLeibniz.lean` and `ThirdParty/.../CohomologyCupProduct.lean`
  (653 lines: `cocycleClass`, `cupHomologyLeft/Right`, `cupZMod2`, `cohPullback`,
  `oneZMod2`, `cupPowZMod2`) are **pinned at `ZMod 2` but coefficient-agnostic**:
  `ZMod 2` occurs there only as a type ascription and through the Leibniz
  consequences.  Nothing in those 653 lines uses `1 = -1`.

So the port is: prove the **signed** Leibniz rule
`δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p (φ ⌣ δψ)` over any `[CommRing R]`, then replay the
653-line descent over `K`.  The sign never escapes: every *consequence* of Leibniz
used downstream ("cup of cocycles is a cocycle", "cup with a coboundary is a
coboundary") is stated sign-free over `K`, because in the right-hand variable one
absorbs `(-1)^p` into the cochain being differentiated
(`δ((-1)^p • (η ⌣ ζ)) = cast (η ⌣ δζ)` when `δη = 0`, since `(-1)^{2p} = 1`).

## 0b. Census correction (after `sp-steenrod`'s warning, same day)

`sp-steenrod` pointed out that classifying files by whether they *name* `ZMod 2`
misses a file that inherits characteristic two through a **lemma name**.  That is
right, and re-running the census as a one-hop use analysis — collect every
declaration whose code (not docstring) is false outside characteristic two, then
find its callers — corrects two things.

**Five in-scope files were missing from the list of 20.**  The char-2 count in
scope is **25**, not 20:

| file | inherits | via |
|---|---|---|
| `ChernGammaComponent` | mechanism (b) | `ChernGammaBridge.chern_relation_lhFun` |
| `SplitRelationRange` | mechanism (b) | `ChernSplitRelation.pull_factor_eq_zero` |
| `ProjectiveSpaceComputation` | mechanism (c) | `ProjectiveSpaceRing.eq_zero_or_eq_of_line` |
| `ProjectiveSpaceRingEntry` | mechanism (c) | same |
| `LerayHirschPoint` | mechanism (c) | same |

**A fourth mechanism exists, in the vendored layer.**  Of the 367 vendored
declarations whose code mentions `ZMod 2`, exactly **19** are reachable from an
in-scope `CharClass` file.  Sixteen are coefficient *instantiations*
(`cohomologyZMod2`, `cocycleClass`, `cochainCxZMod2`, …) and carry no char-2
content.  The remaining three are real, and they are mechanism **(d)**:

* `sphere_top_cohomology_finrank_one_direct` (`SphereTopCohomologyRankOne`),
  `sphereCohomology` (`InducedOnRPCohomology`) and `homologyZMod2`
  (`H1ClassifierZMod2`) — the mod-2 sphere computation.  Consumers in scope:
  `CohomologySphere`, `CohomologyContractible`.

  **I first recorded this as "the one piece of genuine mathematics the
  coefficient parameter needs beyond the Leibniz rule".  That was wrong, and
  checking it is what corrected it.**  The chain is
  `sphere_top_homology_finrank_one_direct` ← `construct_SphereModTwoTopGeneratorData`
  ← `sphereModTwoTop_iso` ← `sphereModTwoSuspension` (the Mayer–Vietoris
  suspension tower) ← `sphereModTwo_one_iso` (`H₁(S¹; F₂) ≅ F₂`), and *every* link
  is a generic construction instantiated at `ZMod 2`: the base case is built from
  `subChainComplex (ZMod 2)`, `mvShortComplex (ZMod 2)`, `H0Gen.H0aug (ZMod 2)`
  and `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`, all of which take
  `(R : Type) [CommRing R]`.  Grepping the whole chain
  (`SphereModTwoTopGeneratorData`, `SphereModTwoOneBase`, `SphereHomologyS1BaseMV`,
  `SphereSuspensionTowerFromMV`) for a char-2 step returns one `simp +decide`
  inside a `fin_cases` over a finite index type — nothing about `ZMod 2`
  arithmetic.  So (d) is a **port, not a reproof**: bigger than most because the
  chain is long and lives in the vendored tree, but it needs no new mathematics.
  The only step that wants `[Field K]` rather than `[CommRing K]` is
  `Subspace.dual_finrank_eq`, used to pass from homology to cohomology.

  **Conclusion: the signed Leibniz rule is the only mathematical content the whole
  coefficient parameter needs.  Everything else is substitution.**
* `singularCohomologyZMod2_map_eq_of_homotopic` — homotopy invariance, consumed by
  `CohomologyBridge`; the underlying chain homotopy upstream is generic, so this
  is a restatement, not a reproof.

`moduleInjective_ZMod2` (consumed by `CohomologyMayerVietoris` and
`RelativeDual`) looks like a char-2 fact and is not: it says `K` is injective as
a module over itself, which every field satisfies.

**On the specific example.**  `CartanSingular.lean` is *not* invisible to a
`ZMod 2` grep — its char-2 kernel `ModuleCatZMod2.hom_add_self` is proved by
`rw [← two_smul (ZMod 2) …, show (2 : ZMod 2) = 0 from by decide, zero_smul]`, so
the token is on the line.  `CartanSimplexExact.lean` does depend on the sign
collapse, but not on `CartanSingular`, which it does not import: it depends on the
vendored **`singular_d_ι`** (`CoveringTransferBoundary.lean` l.106), the *unsigned*
mod-2 boundary formula.  That declaration is the one my token list genuinely
missed — it encodes characteristic two in the *shape* of its statement, with no
char-2 token in the proof.  No in-scope file uses it; `CartanSimplexExact` is its
only `CharClass` consumer, and it is out of scope.

## 1. The parametrisation

```lean
abbrev Hmod  (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} K   -- new
abbrev Hmod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) := Hmod (ZMod 2) X n
```

`Hmod K X n` is `(cochainCx K X).homology n` where `cochainCx K X` is the vendored
`singularCochainComplexFunctor K (ModuleCat.of K K) |>.obj (op X)`.  Because
`cochainCxZMod2` and `cohomologyZMod2` are themselves `abbrev`s at that very
expression, `Hmod2 X n`, `Hmod (ZMod 2) X n` and `cohomologyZMod2 X n` are all
**reducibly equal**, so the 21 in-scope files that write `cohomologyZMod2 X n`
directly need no edit at all.

`cup`, `one`, `pull`, `cohCast`, `cupBilin`, `pullLinear` become generic in `K`
with `K` implicit, inferred from the argument type; every existing call site
elaborates unchanged because `Hmod2` is reducible.

**Class discipline** (a hypothesis used once is an over-ask): `[CommRing K]` at the
basic/assoc/cup/pull/MV/relative/Thom/Gysin layers, which never divide.
`[Field K]` only where a nonzero scalar must be inverted — the "nonzero ⟹ unit
multiple of the generator" files in the table above, `LerayHirsch*` freeness, and
`Kunneth*` rank arguments.  Chern classes need no commutativity of `⌣` (even
degree), so graded commutativity is not assumed anywhere.

**Compatibility rule, binding for this lane:** the vendored ZMod-2 names
(`cocycleClass`, `cupZMod2`, `cohPullback`, `oneZMod2`, `classRepr`,
`cupHomologyLeft/Right`) are **never edited and never removed**.  The generic
layer adds `…K` twins that are *definitionally equal* to them at `K = ZMod 2`
(`cocycleClassK (ZMod 2) X n φ hφ = cocycleClass X n φ hφ := rfl`), so both
vocabularies coexist and the out-of-scope `Cartan*`/`Steenrod*` files, which use
`cocycleClass` in 18 places, keep compiling untouched.

## 2. Bottom-up order

0. `CharClass/CoeffLeibniz.lean` — `sum_split_cancel` (the sign-tracked
   replacement for `sum_split_char2`) and `aw_cochain_leibniz` over `[CommRing R]`,
   plus the sign-free descent consequences.  **New file, imports the vendored layer,
   edits nothing.**
1. `CharClass/CoeffCohomology.lean` — the 653-line descent over `K`:
   `cohK`, `cocycleClassK`, `cupHomologyLeftK/RightK`, `cupK`, `oneK`,
   `cohPullbackK`, `cupPowK`, naturality; plus the `rfl` bridges to the vendored
   ZMod-2 names.  **New file.**
2. `CohomologyBasic.lean` — `Hmod K`, `Hmod2` as its `ZMod 2` instance, `cup`,
   `one`, `pull`, `cohCast` generic; every existing lemma keeps its exact
   statement (they are the `K = ZMod 2` instances, closed by the bridges).
3. `CohomologyAssoc.lean` — `cohCast_cocycleClass`, `cup_assoc`, `one_cup`
   generic (`cochainCup_assoc` and `cochainCup_one_left` there are already
   `{R} [CommRing R]`).
4. Direct consumers, probed as one closure: `CohomologyClassOf`,
   `CohomologyDegreeZero`, `CohomologyShapes`, `CohomologyContractible`,
   `CohomologyBridge`, `CupVanishCochain`.
5. Then, in order: `CohomologyMayerVietoris` + `MayerVietoris*` (the sign goes
   into the biproduct map), `Relative*`/excision, `Kunneth*`, `LerayHirsch*`,
   `Projective*`, `Chern*`, `Thom*`, `Gysin*`, `Bundle*`, `Slice*`, `ChernTotalRing`.

## 2b. What the Mayer–Vietoris step will actually be (read before starting it)

`CharClass/CohomologyMayerVietoris.lean` builds nothing of its own: it is the
`Hom(-, F₂)` dual of the **already generic** vendored chain-level Mayer–Vietoris.
Every input it names takes `(R : Type) [CommRing R]` —
`twoOpenCoverSmallChains`, `subChainComplex`, `mvRightChainMap`, `mvLeftChainMap`,
`mvShortComplex`, `mvSplitting`, `mvEvalIso`, and the exactness theorems in
`ThirdParty/.../MayerVietoris.lean` and `MayerVietorisSES.lean`, both of which
open with `variable (R : Type) [CommRing R]`.  The chain-level MV map is already
`biprod.lift ι (-ι')`, **with the minus sign**.

So the mod-2 dependence is entirely in the *wrapper*, and it is one design choice:
`MayerVietorisBiproduct.lean` absorbs that minus sign with `neg_eq_self_two`
(l.65) rather than carrying it, and then exports `add_self_eq_zero_two` (l.58),
`eq_of_add_eq_zero_two` (l.72) and `add_eq_zero_two` (l.79) as the idiom its 13
consumers use.  Over `K` those four lemmas are replaced by `sub_self`,
`sub_eq_zero`, and `eq_of_sub_eq_zero`, and each consumer's `a + b` becomes
`a - b`.  No new mathematics, and the sign is already proved upstream.

## 3. Keeping `F₂` green

After each landing, probe **the direct consumers of the changed files, not the
tree**: `laneprobe.sh cs-endpoint <changed module> <each module that imports it>`.
The import graph of `CharClass` is wide and shallow at the bottom
(`CohomologyBasic` has 6 direct consumers), so the closure stays small until the
`LerayHirsch`/`Thom` layers.  The `F₂` instance is green iff those consumers are
green, since `Hmod2` is reducibly the old `cohomologyZMod2`.

## Touched outside my lane

`SqDataInstance.lean:94` (prefix `Sq*`, owner `sp-steenrod`).  One line, four
tokens, approved by the lead 2026-09-10:

```
-    (h : ∀ n : ℕ, Function.Injective (pull f n)) :
+    (h : ∀ n : ℕ, Function.Injective (pull (K := ZMod 2) f n)) :
```

It is one of the 36 partial-application sites that the implicit coefficient
argument makes ambiguous.  Semantics unchanged; the alternative was a red tree.
Nothing else under `Steenrod*`, `Cartan*`, `Parity*`, `Wu*`, `Sq*`, `Acyclic*` or
`LIX*` is touched.

## Probe hygiene (fleet rule of 2026-09-10)

Every module this lane edited shows `Built`, never `Replayed`:
`CoeffLeibniz` (2031 jobs), `CoeffCohomology` (2055), `CohomologyBasic` (2056/2057),
`CohomologyAssoc` (2057), and each of the 25 ambiguity-patched files in the wide
probe.  Three `CharClass` modules *were* replayed in the wide probe —
`ThomBridgeNatural`, `ThomBridgeNaturalHyper`, `ThomBridgeNaturalSquare` — and
that is legitimate: none of the three imports `CohomologyBasic`, even
transitively (their closures are 18, 95 and 96 modules of `Bundle*`/`Relative*`,
all below the cohomology API), so their inputs really did not change.

**A second hygiene check the fleet rule does not name, and should.**  "Probe the
modules nothing else imports" is not the same as "probe everything", because a
module can be imported only from *outside* the directory you scanned.  I computed
the `CharClass` tops from `CharClass`-internal imports only, then verified the
result the other way round: take the transitive import closure of the 20 probed
tops and subtract it from the 553 `CharClass` modules.  The answer is 5, all
accounted for — my own two intentional leaf files (`CoeffAxiomCheck`, `CoeffLine`)
and `sp-steenrod`'s three new `OddP*` files.  Do the subtraction; do not trust the
top computation on its own.

## GREEN (with job counts)

Clone `cs-endpoint`, probes of 2026-09-10.

| module | jobs | note |
|---|---|---|
| `CharClass.CoeffLeibniz` | 2031 | signed AW Leibniz over `[CommRing R]`, first probe green |
| `CharClass.CoeffCohomology` | 2055 | the whole 653-line descent over `K`; the three `rfl` bridges to the vendored `ZMod 2` names typecheck, which is the machine-checked proof that the generic layer **is** the `F₂` layer |
| `CharClass.CohomologyBasic` | 2057 | `Hmod K`, `Hmod2` as its `ZMod 2` instance; `cup`, `pull`, `cohCast`, `one`, `cupBilin`, `pullLinear` generic |
| `CharClass.CohomologyAssoc` | 2057 | `cup_assoc`, `one_cup`, `cohCast_cocycleClassOf` generic |

Wide probe of the whole `CharClass` tree (the 20 modules nothing else imports,
covering all 548 files): running / see below.

## AUTHORED, UNVERIFIED

- nothing; every file listed above is probe-green.

## NEEDS

- Nothing from another lane.  Note for whoever takes the Mayer–Vietoris step: the
  **vendored** MV layer is already generic — `MayerVietorisSES.lean` and
  `MayerVietoris.lean` open with `variable (R : Type) [CommRing R]`, so the chain-level
  short exact sequence, its signs, and homology exactness need no work.  The `ZMod 2`
  pinning in `CharClass/CohomologyMayerVietoris.lean` is only in the dualization
  abbrevs (`cohDualFunctor`, `dualCxFunctor`, `dualCx2`, `dualMap2`), and the char-2
  dependence in `MayerVietorisBiproduct.lean` is only the four shortcut lemmas
  `add_self_eq_zero_two` / `neg_eq_self_two` / `eq_of_add_eq_zero_two` /
  `add_eq_zero_two`, which over `K` become the ordinary `sub`-versions.

## TRAPS

- The vendored `sum_split_char2` (`AlexanderWhitneyChainMap.lean` l.226) hides the
  Leibniz sign in a hypothesis `∀ x : M, x + x = 0`; the generic replacement
  replaces `hend : A last = B 0` by `hend : A last + B 0 = 0`, and the rest of the
  proof is unchanged.  Anyone who reads the mod-2 Leibniz statement and concludes
  "the cochain layer is generic in `R`" is wrong: `CupProduct.lean` is, the
  Leibniz rule is not.
- The Leibniz sign never reaches a cohomology-level statement: for the right-hand
  variable, differentiate `(-1)^p • (φ ⌣ η)` instead of `φ ⌣ η` and the two signs
  square to 1.  So `cochainCup_coboundary_left'` and `cochainCup_coboundary_right'`
  keep the exact mod-2 shape over any `CommRing`.
- `-DwarningAsError=true` makes `linter.unusedSimpArgs` fatal: a `simp only [a,b,c]`
  where only `a` fires is five build errors from one line.
- `Fin.sum_univ_two` does not fire on `∑ x : Fin (0 + 2), f x` — the index type must
  be the literal `Fin 2`.  `show` it first.
- **Making the coefficient ring implicit breaks the partial-application idiom.**
  `Function.Injective (pull f n)` has no argument left to infer `K` from.  There
  were 36 such sites in `CharClass/`; each now reads `pull (K := ZMod 2) f n`.
  This edit is forced whether or not the file is later made generic, since a
  generic file has exactly the same ambiguity with `K` a section variable.
- **One edit outside this lane.**  `SqDataInstance.lean:94` (owner `sp-steenrod`,
  `Sq*` prefix) is one of the 36 sites; it now reads
  `(h : ∀ n : ℕ, Function.Injective (pull (K := ZMod 2) f n))`.  That is the whole
  diff, semantics unchanged, and the alternative was to leave the tree red.
