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

## 0c. The naming convention (binding for `sp-steenrod` and `sp-oddside`)

**The coefficient argument is implicit when some argument determines it, and
explicit otherwise.**  That is the whole rule, and it is forced, not stylistic.

* Implicit: `cup a b`, `pull f n a`, `cohCast h a`, `one`, `cupBilin`,
  `pullLinear`, `cocycleClassK`, `cupK` — each has a class argument whose type
  is `Hmod K …`, so `K` is inferred and every existing `F₂` call site is
  unchanged.
* Explicit, as the **first** argument: `mvCoSCOf K U V hUV`, `mvDeltaOf`,
  `mvConnectingIsoOf`, `dualCxOf`, `cohDualFunctorOf`, `moduleInjective_of_field`,
  and everything else whose arguments are spaces, opens or degrees.  `mvCoSC U V hUV`
  mentions only two opens; there is nothing for `K` to be inferred from.

The `F₂` spellings stay as **`abbrev`s** at `K = ZMod 2` in both cases, so they
are reducible and the generic instances fire on them without being restated.

Two consequences worth knowing before you author:

1. Even with an implicit coefficient, a *partial* application has nothing to
   infer from — `Function.Injective (pull f n)` needs `pull (K := ZMod 2) f n`,
   and in a generic file it needs `pull (K := K) f n` with `K` the section
   variable.  There were 39 such sites in `CharClass/`.
2. A leaf file that mentions `ZMod p` needs `import Mathlib.Data.ZMod.Basic`
   explicitly.  `autoImplicit` reports the missing import as
   `Function expected at ZMod`, pointing at the application rather than the import.

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

## 2c. Two facts the Mayer–Vietoris step needs that are not obvious from the plan

**The lead's ordering has a hidden prerequisite, and it is harmless.**
`CohomologyMayerVietoris` imports `CohomologyContractible`, which imports
`CohomologySphere` — so "Mayer–Vietoris and Contractible" sits *above* the sphere
computation, which is mechanism (d) and the longest port in the lane.  It does
not block: `CohomologyMayerVietoris` never uses a sphere fact, the import is a
chain artefact, and the compatibility rule keeps every `F₂` sphere name in place.
So MV can be made generic in `K` while `CohomologySphere` stays at `ZMod 2`, and
the sphere port can happen later without redoing MV.

**One genuinely missing lemma.**  The dual short exact sequence needs the
coefficient module to be injective.  At `F₂` this is
`moduleInjective_ZMod2` (`H1ClassifierZMod2.lean` l.313), proved by Baer's
criterion with a `fin_cases a` that enumerates the two elements of `ZMod 2`.
Mathlib at the pin has **no** instance "every module over a field is injective" —
`Mathlib/Algebra/Module/Injective.lean` offers `Module.Baer.injective` and a `pi`
instance and nothing else — so the port is a real, if small, lemma:

```lean
theorem moduleInjective_field (K M : Type) [Field K] [AddCommGroup M] [Module K M] :
    Module.Injective K M
```

by Baer, replacing `fin_cases a` with "a nonzero element of a field is a unit, so
the ideal is `⊤`" (`Ideal.eq_top_of_isUnit_mem`).  Consumers:
`CohomologyMayerVietoris` and `RelativeDual`.

## 3. Keeping `F₂` green

After each landing, probe **the direct consumers of the changed files, not the
tree**: `laneprobe.sh cs-endpoint <changed module> <each module that imports it>`.
The import graph of `CharClass` is wide and shallow at the bottom
(`CohomologyBasic` has 6 direct consumers), so the closure stays small until the
`LerayHirsch`/`Thom` layers.  The `F₂` instance is green iff those consumers are
green, since `Hmod2` is reducibly the old `cohomologyZMod2`.

## Deliverable 2: Mayer–Vietoris (authored) and why Contractible is not its peer

`CohomologyMayerVietoris.lean` is rewritten generic in `K` and awaiting its probe.
The shape is `mvCoSCOf K U V hUV`, `mvDeltaOf`, `mvConnectingIsoOf`, … with the
coefficient an **explicit first argument** — unlike `cup`/`pull`, none of these
has an argument that would determine it (`mvCoSC U V hUV` mentions only two
opens), so an implicit coefficient would be ambiguous at every call site.  The
existing `F₂` names are `abbrev`s at `K = ZMod 2`, hence reducible, so all 16
consumers of `mvDelta`, all 11 of `mvCoSC` and the rest are byte-unchanged, and
the generic instances fire on the `F₂` spellings without being restated.
`[CommRing K]` carries the dualizing functor and the dual complex; `[Field K]` is
asked for only where injectivity of the coefficient is used
(`cohDualFunctorOf_preservesEpimorphisms`) and downstream of it.

**`CohomologyContractible` is not a peer of Mayer–Vietoris and cannot be done
next.**  Its three vanishing theorems go through `kroneckerEquiv` and
`homologyDualZMod2_isZero_of_homology_isZero`, and `cohZeroEquivOfContractible`
goes through `cohZeroEquiv`.  `kroneckerEquiv X n` (`KroneckerNaturality.lean`
l.214) takes **no coefficient parameter**: the whole universal-coefficient /
Kronecker layer, together with `H1ClassifierZMod2.lean`, is a genuinely
`ZMod 2`-only vendored development.  That layer *is* mechanism (d), it is what
`CohomologySphere` also rests on, and porting it is the prerequisite for
Contractible — not the other way round.  The good news is that its one hard
input is exactly `moduleInjective_of_field`, which is now written
(`CoeffField.lean`), so the port is bounded.

Mayer–Vietoris does not need any of this: it imports `CohomologyContractible`
only through the chain, never uses a fact from it, and stays green with the `F₂`
Contractible in place.

**And `MayerVietorisBiproduct.lean` is smaller than §0 mechanism (a) suggests.**
Reading it rather than grepping it: its actual development — `mvDualMap_add/zero`,
`mvCx`, the four maps `mvCxProjU/ProjV/InclU/InclV`, `mvCx_total`, their homology
versions, `mvH_decompose` and `mvH_eq_zero_iff` (l.100-234) — is **entirely
coefficient-independent**.  It is `biprod.total` carried through an additive
functor and then through `homologyMap`; not one line of it uses characteristic
two.  The four char-2 lemmas (`add_self_eq_zero_two` and its three corollaries,
l.58-81) sit in §1 of that file and are used **only by each other** — they are a
service exported to the consumers listed under mechanism (a), not part of the
biproduct argument.  So the file generalises as a plain substitution, with the
four `F₂` lemmas simply left in place beside generic `sub`-based analogues, and
the sign work is confined to the consumers that use `a + b = 0` to mean `a = b`.

## Deliverable 3 (design, not yet authored): relative homotopy invariance over any `R`

Lead's addition of 2026-09-10, on the odd side's critical path.  Written here at
lemma precision first, per §3 of the program note; no Lean until it is probeable.

**The premise checks out.**  `TopCat.Homotopy.singularChainComplexFunctorObjMap H R`
gives the chain homotopy itself, generic in the coefficient object `R`, so
`RelativeLineHomotopy`'s `F₂` trick is replaceable.  And the components are not
opaque: `SimplicialObject.Homotopy.ToChainHomotopy.hom_eq` is a `@[simp]` lemma
saying

```text
hom H p (p+1) = -∑ k : Fin (p+1), (-1)^k • H.h k
```

so the chain homotopy is an alternating sum of the *simplicial* homotopy's own
structure maps.  Restriction to a subspace is therefore naturality in the space,
not a computation with prism decompositions.

**The shape of the target.**  `relPullback R f hf n` is already generic
(`RelativeFunctorial.lean` l.118), and the relative cochain complex is the
**annihilator subcomplex** `relCochainSubmodule R Y B` of `C^*(Y)`, not a
quotient.  So what has to be shown is that the dual prism carries
"cochains vanishing on `B`-chains" into "cochains vanishing on `A`-chains", which
is the transpose of: the prism carries `A`-chains into `B`-chains.

**The lemma list.**

1. `relHomotopyCorestrict` — from `H : TopCat.Homotopy f g` with
   `∀ t x, x ∈ A → H (t, x) ∈ B`, build `H_A : TopCat.Homotopy f_A g_A` for the
   corestricted maps `f_A g_A : TopCat.of A ⟶ TopCat.of B`.  Elementary; the
   underlying map is `H ∘ (id × i)` corestricted to `B`.
2. `toSSet_homotopy_naturality` — for the inclusions `i : A ⟶ X`, `j : B ⟶ Y`,
   `(toSSet.map i) ≫ H.toSSet.h k = H_A.toSSet.h k ≫ (toSSet.map j)` for every
   `k`.  `TopCat.Homotopy.toSSet` builds its `h` field as
   `(whiskering) ≫ (lax monoidal μ) ≫ TopCat.toSSet.map H.h`, and the only
   space-dependent factor is the last, so this is functoriality of `toSSet` plus
   naturality of `μ`, applied to `H.h ∘ (i × id) = j ∘ H_A.h` — which is exactly
   hypothesis (1) made precise.
3. `chainHomotopy_naturality` — `C(i) ≫ P = P_A ≫ C(j)` in each degree, where
   `P := (H.singularChainComplexFunctorObjMap R).hom`.  By `hom_eq` this is (2)
   summed over `k` with signs.  **Mathlib has no naturality lemma for
   `toChainHomotopy`, so this one is ours**; it is the only real work in the
   deliverable.
4. `prism_mapsTo_subChain` — `P` maps `subChainSubmodule R X A p` into
   `subChainSubmodule R Y B (p+1)`.  From (3): the submodule is the image of
   `C(i)`, so `P (im C(i)) = im (C(i) ≫ P) = im (P_A ≫ C(j)) ⊆ im C(j)`.
5. `relCochainHomotopy` — transpose (4): the dual of `P` carries
   `relCochainSubmodule R Y B` into `relCochainSubmodule R X A`, giving a
   `Homotopy (relCochainMap R f hf) (relCochainMap R g hg)`.
6. `relPullback_eq_of_homotopy (R) [CommRing R] {f g} (hf hg) (H) (hH) (n) :
   relPullback R f hf n = relPullback R g hg n` — `Homotopy.homologyMap_eq`.

**Mathlib names, verified at the pin `81a5d257` so the authoring is mechanical:**

| what | name |
|---|---|
| homotopy in `TopCat` | `TopCat.Homotopy f g` — an `abbrev` for `ContinuousMap.Homotopy f.hom g.hom`, applied as `H (t, x)` with `t : I` **first** |
| its `TopCat` morphism | `TopCat.Homotopy.h : X ⊗ I ⟶ Y`, with `@[simp] h_hom_apply : F.h p = F (I.homeomorph p.2, p.1)` — note the swap |
| chain homotopy, generic in `R` | `TopCat.Homotopy.singularChainComplexFunctorObjMap H R` |
| its components | `SimplicialObject.Homotopy.ToChainHomotopy.hom_eq`, `@[simp]` |
| simplicial homotopy field | `SimplicialObject.Homotopy.h {n} (i : Fin (n+1)) : X _⦋n⦌ ⟶ Y _⦋n+1⦌` |
| the simplicial homotopy of a topological one | `TopCat.Homotopy.toSSet`, whose `h` is `(whiskering) ≫ μ ≫ TopCat.toSSet.map H.h` |

So the hypothesis is `hH : ∀ (t : I) (x : X), x ∈ A → H (t, x) ∈ B`, and
`H.h p ∈ B` for `p.1 ∈ A` follows by `h_hom_apply`.

**Stated risk, flagged early as the lead asked.**  Step (2) leans on naturality
of the lax monoidal structure map of `TopCat.toSSet`.  If that is awkward at the
pin, the fallback is to prove (3) directly from the concrete description of
`SSet.chainComplexMap` on generators rather than through `μ`.  I will say so
rather than fight it.

## Deliverable 2b (assessment): the Relative layer is mostly already generic

Read-only survey of all 14 `Relative*.lean` files, 2091 lines.  **Five of them
(`RelativeBundleNonempty`, `RelativeCochains` 320 lines, `RelativeFunctorial` 255
lines, `RelativeLES`, `RelativeRangeKer`, `RelativeLocal`, `RelativeProdContractible`)
never name `ZMod 2` in a way that is not already an argument to a generic
function** — `relCohomology (R)`, `relPullback (R)`, `relToAbs (R)`, `absToSub (R)`,
`relDelta (R)`, `relDeltaIso (R)`, `excisionShortExact (R)`, `absToSub_naturality (R)`,
`relLES_exact_abs (R)`, `dualMap (R)` and the rest all carry `(R : Type) [CommRing R]`
already.  So most of this layer is the substitution `(ZMod 2) ↦ K`.

Exactly three files carry real work:

| file | what | status |
|---|---|---|
| `RelativeDual` | `moduleInjective_ZMod2` | **already solved** — `moduleInjective_of_field` is written and probe-green |
| `RelativeLineHomotopy` | `∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y` (l.72) and the line hypotheses | `CoeffLine.exists_ne_zero_smul_of_line` for the algebra; the real replacement is deliverable 3, relative homotopy invariance |
| `RelativeLocalModel` | `≃ₗ[ZMod 2] ZMod 2` hypotheses | formal — becomes `Line K` |

So the Relative deliverable is: substitution across eleven files, one lemma
already in hand, and deliverable 3 (relative homotopy invariance over any `R`)
as the only new mathematics.

## Naming, fixed (binding for `sp-cupone` and `sp-evenside`)

The lead delegated this; there was already a divergence, so it is settled here.
`sp-evenside` asked for `mul_comm_of_isEven`, the lead wrote `mul_comm_of_even`.
**Both names exist and they are different statements.**  Do not merge them.

| name | about | on | owner |
|---|---|---|---|
| `cup_comm_of_even` | the **degrees**: `p` or `q` even | `Hmod K X n` | `sp-cupone` |
| `TotalH.mul_comm_of_isEven` | the **predicate** `IsEven` | `TotalH K X` | `sp-cupone`, against my type |

Lean's convention derives the suffix from the hypothesis, so a lemma whose
hypothesis is `IsEven a` is `_of_isEven` and one whose hypothesis is `Even p` is
`_of_even`.  Keeping them distinct also stops the two being confused: the first
is a statement about two classes in fixed degrees, the second about two arbitrary
elements of the total ring, and the second is proved *from* the first by
decomposing into components.

**Split, approved by the lead 2026-09-10.**  Mine: `TotalH` over `K` as a graded
ring (`DirectSum.GRing`, `mul_comm` dropped), `TotalH.of`, `component`,
`of_eq_zero_iff`, `map`, the `IsEven` predicate, the criterion
`isEven_of_odd_component_eq_zero`, and the closure lemmas
(`isEven_of`, `IsEven.zero/one/add/neg/map`).  All unblocked today.

**`IsEven.mul` is dropped, deliberately.**  `sp-evenside` offered to withdraw it
once I corrected its cost, and no consumer survives the check: they need `IsEven`
for `z` (a single `of`-term, so `isEven_of`), for `ι r` (from `IsEven.map` plus
`Y`'s even-concentration), and `mul_comm_of_isEven` to move one past the other —
they never multiply two even elements and then need the result even.
`sp-cupone`'s `mul_comm_of_isEven` does not need it either: that proof expands
both factors over their supports and applies `cup_comm_of_even` pairwise, which
is the same machinery but not this lemma.  And `CommRing (TotalH K Y)` follows
from `mul_comm_of_isEven` alone once every element is even.  So it is an unused
abstraction and it is not being written; if a consumer appears it is 30–50 lines
via `sum_support_of`, `Finset.sum_mul_sum`, `of_mul_of`, `of_eq_of_ne`.
`sp-cupone`'s: the signed cup-1 coboundary formula, signed `cup_comm`,
`cup_comm_of_even`, and `TotalH.mul_comm_of_isEven`.  That is exactly one blocked
declaration, which is the property `sp-evenside` asked for.

**Mathlib has no component-of-product lemma for a graded semiring** at this pin —
`DirectSum/Ring.lean` gives `mulHom`, `mulHom_of_of` and `of_mul_of` and stops.
So "the degree-`m` component of a product is a sum over `i + j = m`" is true
mathematics with nothing to cite, and must not appear in a docstring: it sends a
reader into a search that terminates in nothing, and a zero-hit search is
indistinguishable from the fact being false.

`isEven_of_odd_component_eq_zero` **stays a named lemma even though it is
definitional**, and this is a standing decision, not an oversight to optimise away
later.  `sp-evenside` obtains `IsEven` for an arbitrary element of `TotalH K Y`
from `Y`'s even-concentration, never from how the element was built, so every use
site would otherwise carry a definitional unfolding — and those rot.

## Even-concentration is ring-free (verified)

`CohomologyProjectiveParity.noOddCohomology_prod_CP` — a product of projective
spaces has no odd cohomology — has a 53-module transitive closure that **never
reaches `SteenrodCupOne`**.  So even-concentration comes with the Mayer–Vietoris
and chart layer, not with the commutativity theorem.  Consequence for
`sp-evenside`'s `R`: once `TotalH.mul_comm_of_isEven` exists, `TotalH K Y` for `Y`
a product of projective spaces is commutative **outright**, because every element
of it is even.  No even subring, and no dependence on `ProjectiveSpaceRing`, whose
route to commutativity is circular (it reaches `cup_comm` through
`ProjectiveSpaceGenHyp`).

## Deliverable 4 (design): signed graded commutativity over `K`

Assigned by the lead 2026-09-10 after `sp-evenside` flagged it.  This is **not** a
convenience: `cup_comm` is consumed by **twelve in-scope files** — `ChernRelation`,
`ChernTotalRing`, `CohomologyChartFreeness`, `CohomologyChartGenBridge`,
`CohomologyChartInduction`, `CohomologyChartRankTwoInterface`,
`CohomologyChartTower`, `CohomologyChartTowerTop`, `CohomologyLHRingComponent`,
`LerayHirschAlgebra`, `LerayHirschShiftTerm`, `ProjectiveSpaceGenHyp` — and
`LerayHirschAlgebra.lean:107` records that the projective-bundle structure itself
waits on it.  So `LerayHirsch*`, `Chern*` and `Projective*` over `K` are all
downstream of one formula.

**The good news, and it halves the job.**  `cochainCupI` is **already generic**:
`SteenrodCochain.lean:210` is `def cochainCupI {R : Type} [CommRing R] …`, and its
evaluation is a plain sum over `cutIndex` with no coefficient assumption.  The
`F₂` pinning is entirely in the **coboundary formula**,
`SteenrodCoboundary.lean:198`, and char 2 enters there in exactly two lines:
`h2 : ∀ x : ZMod 2, x + x = 0` (l.208) cancelling duplicated terms, and
`neg_one_pow_zmod2` (l.216) stripping the coboundary sign.  The other ~300 lines
are `cutIndex` combinatorics indifferent to the ring.  Same idiom `sp-steenrod`
described: prove it signed, collapse at the end.

**Why the even case is not cheaper than the general one.**  The Alexander–Whitney
product is non-commutative at cochain level in every characteristic, so
even-degree classes do not commute for free — they commute because `(-1)^{pq}` is
`+1` once you have the signed theorem.  And the escape in §1.5 of the program
note ("classes from different factors commute by naturality") does **not** hold:
on a simplex, `p₁^*a ⌣ p₂^*b` is `a(front(p₁σ))·b(back(p₂σ))` while the reverse is
`b(front(p₂σ))·a(back(p₁σ))`.  Different cochains; still needs a homotopy.

**Lemma list.**

1. `cochainCupI_coboundary_signed {R} [CommRing R] (i a b n) (α β)` — the signed
   2-fold formula.  Owner to be settled with `sp-steenrod`: if their tuple model
   yields it `p`-fold, I consume theirs; otherwise I prove it in a new file under
   my prefix, reusing their generic `cochainCupI` and `cutIndex` lemmas and
   touching none of their files.
2. `cup_comm_signed {K} [CommRing K] (a : Hmod K X p) (b : Hmod K X q) :
   cup a b = (-1 : K)^(p*q) • cohCast (Nat.add_comm q p) (cup b a)` — from (1) at
   `i = 0` with both classes cocycles, exactly as the `F₂` proof descends.
3. `cup_comm_of_even` — the corollary when `p` or `q` is even; this is all the
   program consumes.
4. `TotalH` vocabulary for `sp-evenside`: `TotalH.IsEven` (all odd components
   vanish), `TotalH.mul_comm_of_isEven`, and `IsEven` closed under `+`, `*`,
   `TotalH.of` at even degree, and `TotalH.map`.

**Convention.**  Must agree with `sp-steenrod`'s tuple model; `OddPSource.lean:25`
fixes the Koszul convention on the tensor half as
`d(e_i ⊗ σ) = d_W e_i ⊗ σ + (-1)^i (e_i ⊗ ∂σ)`.  Asked them to confirm the
two-variable placement before I author, so the two formulas cannot differ by a
sign nobody can find later.

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

## A pattern worth naming, from `sp-steenrod`

`sp-steenrod` checked the `singular_d_ι` finding rather than accepting it, and
reports that the vendored proof **reaches the honest signed steps and then
discards the signs with a two-torsion lemma in its last line**.  That is exactly
the shape of `aw_cochain_leibniz_zmod2`, where `sum_split_char2` and
`neg_one_pow_zmod2` are applied at the very end of an otherwise generic argument.
So the vendored tree has a recurring idiom: *prove it signed, collapse the signs
at the end*.  The practical consequence is the good one — the generic statement
is almost always the same proof stopped one line earlier, not a new argument —
and it is why the Leibniz port went green on its first probe.  Expect the same
when the Kronecker/UCT layer is ported.

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

## Tree state for the landing batch (2026-09-10, 12:00 CDT)

`CharClass` is **frozen** in its current state until the lead has landed.  The
Relative layer goes into new files or the scratchpad; no existing `CharClass`
file will be touched.

Working tree: 28 modified `CharClass` files (4 layer rewrites, 24 carrying only
ambiguity pins) and 5 new `Coeff*.lean`.  All 5 are **untracked**, which matters
for anyone cloning: a git-based clone gets none of them and the modified files
without their dependencies.

`sp-tower`'s gate on a fresh clone reported three errors in my in-flight files.
One was real and is fixed: `CoeffField.lean` and `CoeffLine.lean` need
`import Mathlib.Algebra.Field.ZMod`, because `Mathlib.Data.ZMod.Basic` supplies
the type and its `CommRing` but **not** `Field (ZMod p)`.  The other two,
`CohomologyAssoc.lean:93` and `:103`, are the exact signature of a truncated
`CoeffCohomology.lean`: `autoImplicit` turns the undefined `cocycleClassK` into a
variable, its application reads as "Function expected", and the enclosing
`cohCast_cocycleClassOf` then reads as an unknown identifier eleven lines later.
I verified the rename is **not** half-applied by checking every `Of`/`K`-suffixed
identifier across my nine files against everything declared in `CharClass`;
nothing dangles.

**My guess at the cause was wrong, and `sp-tower` disproved it with evidence.**
I proposed a torn read from a non-atomic in-place rewrite.  In fact
`CoeffCohomology.lean` in their clone was byte-identical to mine and *built green
in that very run*.  The cause was a **fresh `.trace` over a five-day-old
`.olean`** for `CohomologyBasic`: lake trusts the trace, so the module appears in
the log neither as `Built` nor as `Replayed` but is simply **absent**, and every
importer is handed an environment predating `cocycleClassK`.  My causal chain
from the missing identifier to the two errors was right; only its first link was
wrong.

That matters for this lane's own greens: "Built, never Replayed" is necessary and
**not sufficient** — a silent module is the dangerous case, and a stale olean that
still elaborates yields a false green.  So the 12:12 run now clears every
`CharClass` build artifact in `cs-endpoint` (`.olean`, `.ilean`, `.trace`,
`.olean.hash`, `ir/*.c`) before probing.  The `.trace` is the one that must go.
Clearing the whole directory rather than just my 33 modules costs nothing here,
because rewriting `CohomologyMayerVietoris` forces a rebuild of nearly the whole
tree anyway.

Probes are queued for 12:13 CDT (wrapper cooldown): leaf files alone first, then
the 20 tops.  Expected consistent green ≈ 13:00 CDT.

## GREEN (with job counts)

Clone `cs-endpoint`, probes of 2026-09-10.

| module | jobs | note |
|---|---|---|
| `CharClass.CoeffLeibniz` | 2031 | signed AW Leibniz over `[CommRing R]`, first probe green |
| `CharClass.CoeffCohomology` | 2055 | the whole 653-line descent over `K`; the three `rfl` bridges to the vendored `ZMod 2` names typecheck, which is the machine-checked proof that the generic layer **is** the `F₂` layer |
| `CharClass.CohomologyBasic` | 2057 | `Hmod K`, `Hmod2` as its `ZMod 2` instance; `cup`, `pull`, `cohCast`, `one`, `cupBilin`, `pullLinear` generic |
| `CharClass.CohomologyAssoc` | 2057 | `cup_assoc`, `one_cup`, `cohCast_cocycleClassOf` generic |

Wide probe of the whole `CharClass` tree (the 20 modules nothing else imports,
covering 548 of the 553 files; the 5 uncovered are named under Probe hygiene):
**FAILED on the first run**, and its complete verdict is in: exactly two
failures, `ThomBridgeHyperplane.lean:104` and `ProjectiveSpaceStable.lean:105`,
with no third anywhere else in the tree.  Both are fixed.

The combined re-probe then **aborted at job 4406 of ~9300** on a one-line missing
import in `CoeffLine` and `CoeffField` (`ZMod` not in scope; `autoImplicit`
reports it as `Function expected at ZMod`).  Lake aborts the whole build when any
named target fails, so the Mayer–Vietoris verdict — the point of that run — was
never reached.  Lesson recorded in FLEET_TRAPS: probe new leaf files on their own
first, they cost seconds; never bundle them with the tops.

That run did produce two results worth keeping.  `CoeffAxiomCheck` built, so
every generic theorem reports exactly `[propext, Classical.choice, Quot.sound]`,
and its two `rfl` bridges typechecked: `cup` and `one` at `K = ZMod 2` are now
machine-checked to be definitionally the vendored `cupZMod2` and `oneZMod2`.  And
every generic declaration in `CoeffLine` and `CoeffField` compiled — only the
`F₂`-instance corollaries at the bottom of each file failed — so
`moduleInjective_of_field` by the complement route is sound.  Imports fixed;
re-probing.  The four base-layer modules above are unaffected — they are green on
their own probes and were `Built`, not `Replayed`.

The first run surfaced **two** failures, both ambiguity sites of kinds my
line-oriented grep could not see, and both now fixed:
`ThomBridgeHyperplane.lean:104` and `ProjectiveSpaceStable.lean:105`.

The first was a site of a kind my grep could not see:
`have hcomp : ∀ a, pull … (pull (subInclusion …) k a) = …` leaves `a` untyped, so
`K` is undetermined, reported as `typeclass instance problem is stuck: CommRing
?m.56` and then as a `sorryAx` in the enclosing `hyperplane_hsub`.  The second was an equation between two
partial applications, `pull (cpIncl d) 2 = (pull (cpInclP d) 2) ∘ (pull (punctIncl d) 2)`,
where nothing on either side is a class.

Re-sweeping on whitespace-normalised source with an argument COUNT rather than a
regex (flag every `pull` with fewer than three arguments, then keep only those
under `Injective`/`Surjective`/`Bijective`, under `∘`, or on both sides of an `=`)
cut 212 raw candidates to 31 and the 31 to exactly these plus two multi-line
`Function.Bijective\n  (pull …)` in `GysinPairRetract`.  All five are pinned now,
bringing the total to **41** sites — though the probe then built `GysinPairRetract`
green from the *un*pinned source, so those two pins were precautionary rather than
required: there the coefficient is fixed by the term on the right of `:=`.
Over-pinning is harmless; under-pinning costs a 40-minute cycle.

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
