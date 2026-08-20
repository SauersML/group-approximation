# Tikuisis–White–Winter, formalized at the theorem instead of at its corollary

**Authored 2026-08-19. UNCOMPILED and UNWIRED — see "Before anything is graded".**

## What changed

`INT.11` ("all amenable groups are MF, by quasidiagonality") and `CY.12c` (the
same sentence at the realized Clifford quotient) both cite Tikuisis–White–Winter,
*Quasidiagonality of nuclear C\*-algebras*, Ann. of Math. (2) **185** (2017),
229–284. Until this wave the repository typed that citation only at its far end,
as `QuasidiagonalMF.AmenableMFInput` — the bare group implication
`amenable ⟹ operator-MF`, with no inhabitant.

That is not the theorem. The theorem is a statement about C\*-algebras and
traces:

> every faithful trace on a separable nuclear C\*-algebra satisfying the UCT is
> quasidiagonal.

Four modules now state it there and walk the distance to the printed group
implication, so that a reader can see which steps are theorems and which are
citations.

| module | contents |
|---|---|
| `GroupApproximation/Analysis/QuasidiagonalTrace.lean` | `IsCompletelyPositiveOnMatrices` (form-sense CP for maps into `M_Y`), `QuasidiagonalTraceModel` / `IsQuasidiagonalTrace` (TWW's conclusion, field for field), `UCPSelfAdjointContractive` (the two automatic ucp facts, typed), `isMFTrace_of_isQuasidiagonalTrace` |
| `GroupApproximation/Analysis/MFTracePullback.lean` | `ShulmanTrace.MFTraceModel.congr`, `.comp` (MF traces pull back along any `⋆`-hom), `isMFTrace_canonicalMaximal_of_reducedTrace` |
| `GroupApproximation/Analysis/TikuisisWhiteWinter.lean` | `TikuisisWhiteWinterInput`, `AmenableNuclearInput` (Lance), `AmenableUCTInput` (Tu), `isOperatorMF_of_isQuasidiagonalCanonicalTrace` (**the reduction half, proved**), `isOperatorMF_of_isAmenable_of_tww` |
| `GroupApproximation/Sofic/TikuisisWhiteWinterSites.lean` | `CY.12c` over the real inputs; the marked group's canonical trace is **not** quasidiagonal; a second route to `RE.05`'s non-nuclearity |

## The route, and what is left

For a countable group `G`, with `τ_r` the canonical trace of `C*_r(G)` and
`q : C*(G) → C*_r(G)` the canonical map:

1. `C*_r(G)` separable — **proved** (`reducedGroupCStar_separableSpace`).
2. `τ_r` faithful tracial state — **proved** (`canonicalFaithfulTracialState`).
3. `C*_r(G)` nuclear for amenable `G` — **proved** since 2026-08-19,
   `CStarExactness.isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable`;
   `CStarExactness.amenableNuclearInput` inhabits `AmenableNuclearInput`.  The
   route is the Følner factorization through `B(ℂᵏ)`: Følner sets come from
   `Sofic/AmenableActionSofic.exists_folner`, complete positivity of both maps
   from the Choi map and the block-operator bridge, contractivity from
   Stinespring, and the passage from translations to arbitrary elements from
   `adjoin = span`.  See the "Lance, discharged" section of
   `metadata/LITERATURE_QUARANTINE.md`.
4. `C*_r(G)` satisfies the UCT — **input** (Tu).
5. hence `τ_r` quasidiagonal — **input** (TWW).
6. quasidiagonal trace ⟹ MF trace — **proved**, modulo `UCPSelfAdjointContractive`.
7. pull back along `q` — **proved**.
8. canonical maximal MF trace ⟹ `IsOperatorMF G` — **already in the tree**
   (`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`, the corona
   argument of `Sofic/MFTraceCoronaBridge.lean`).

So one opaque binder has become three named inputs plus five machine-checked
steps, of which the deepest is TWW itself.

**Steps 6–8 are the reduction half of `INT.11`, and it was outstanding.**
`Analysis/QuasidiagonalCompression.lean` records that half as needing
"matrix-coordinate bookkeeping against the corona's conventions"; the route
taken here avoids that entirely by going through the trace rather than through
a faithful representation, so the compression module's remaining work is no
longer on the critical path for this row.

**Hulanicki is not used.** Step 7 is the pullback of trace models along `q`,
which needs no identification of `C*(G)` with `C*_r(G)` and no amenability.

## Two things running the route backwards buys

* `markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace` — Theorem A's
  group has a **faithful non-quasidiagonal trace on a separable C\*-algebra**.
  Depends only on the ucp facts, not on TWW.
* `markedGroup_reducedGroupCStar_not_isNuclear_of_tww` — granting TWW and the
  UCT for that one algebra, `C*_r(E)` is **not nuclear**. This is `RE.05`'s
  conclusion by a route independent of the existing one
  (`NuclearityAmenability.reducedGroupCStar_not_isNuclearCStar_of_lance`,
  which uses Lance and the `min = max` nuclearity predicate); this one uses TWW
  and the CPAP predicate.

## Before anything is graded

* **Nothing here has been compiled.** No `lake build` has seen these files, and
  `grep sorry` returning nothing is not evidence of a proof.
* **The modules are deliberately not imported from `GroupApproximation.lean`.**
  Wiring an uncompiled module into the root closure has broken the tree before.
  Wire them in the same push that first turns them green, not earlier.
* **No ledger grade may move on this.** `INT.11` and `CY.12c` stay
  `MISSING`/`literature-input`: nothing here inhabits any input, and the route
  is conditional on three of them. What changes when this compiles is the
  *shape* of the note, not the grade.
* **No declaration concludes `QuasidiagonalMF.AmenableMFInput`**, deliberately:
  a producer of it from bare `∀`-premises would enter the discharge fixpoint of
  `scripts/check_non_mf_unconditional.py` and the input would stop being
  reported open. Every conclusion is stated group by group with head
  `IsOperatorMF`. After the first green build, check that
  `--audit-corpus` lists the four new input names
  (`TikuisisWhiteWinterInput`, `AmenableNuclearInput`, `AmenableUCTInput`,
  `UCPSelfAdjointContractive`) and still lists `AmenableMFInput`.

## Likely first-build repairs, in order of suspicion

1. `CStarAlgebra A → NonUnitalCStarAlgebra A` instance search inside
   `TikuisisWhiteWinterInput` / `AmenableNuclearInput`, where
   `CStarExactness.IsNuclearCStarAlgebra` is stated at the non-unital class.
   The predicate has no use site anywhere else in the tree, so this path is
   untested here.
2. `canonicalFaithfulTracialState_maximalGroupCStarToReduced`, proved by `rfl`:
   it composes the `CoeFun` of `FaithfulTracialState` with
   `ContinuousLinearMap.coe_coe` and the definitional
   `canonicalMaximalTrace_apply`.
3. `IsCompletelyPositiveOnMatrices.form_nonneg`, whose `simpa` has to collapse
   two `Fin 1` sums.
4. The `simp only` beta-reductions in `QuasidiagonalTraceModel.toMFTraceModel`
   and `MFTraceModel.comp` — the `MFTraceModel` fields are bare functions, so
   the goals arrive unbeta-reduced; `ShulmanTracePositiveControls` solves the
   same shape with an explicit `show`, which is the fallback.

## The one input that is dischargeable

`UCPSelfAdjointContractive` says a unital completely positive map into a matrix
algebra is `⋆`-preserving and contractive. The repository already has the
Stinespring dilation for completely positive maps into `B(H)`
(`Analysis/CStarStinespringDilation.lean` and the nine modules around it). What
is missing is (i) transporting the form-sense complete positivity of
`IsCompletelyPositiveOnMatrices` into `CStarExactness.IsCompletelyPositive` at
the target `B(ℂᵏ)`, and (ii) the star-algebra identification of `Matrix Y Y ℂ`
with `B(ℂᵏ)`. Closing it would leave TWW, Lance and Tu as the only inputs on
the route.

**Two of those three are gone (2026-08-19).** `UCPSelfAdjointContractive`'s
sibling `Quasidiagonal.UCPContractive` was retired by proof, and Lance is
proved outright (item 3 above). Tu is not proved but can be *eliminated*:
`TikuisisWhiteWinterInput` and `AmenableUCTInput` share the abstract
`UCT : Type u → Prop` parameter and the composite consumes both at the same
one, so instantiating it at "is `C⋆_r(H)` for amenable `H`" makes Tu's clause a
tautology while weakening TWW's clause to the amenable case
(`Analysis/TikuisisWhiteWinterAmenableClass`). What that leaves on the amenable
route is **one** citation, TWW itself — which is Rosenberg's conjecture and is
irreducible here.
