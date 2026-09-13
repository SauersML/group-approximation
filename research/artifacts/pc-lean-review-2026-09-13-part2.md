# Pestov 9.1 in Lean: adversarial review (lane pc-review), 2026-09-13, part 2

Part 2 covers the landed modules: hidden hypotheses, laundered Props, how the prose describes conditional results, and
axiom closures. Part 1 (`pc-lean-review-2026-09-13.md`) covers statement fidelity. The review covers main up to
fa206d585 / eb9eb62f8 (02:25 CDT).

## 4. Evidence standard

- **Closures.** Every closure below is read from a probe record carrying `# PROBE GREEN`, never from a commit
  message. The records are in `.../6dbfc571-.../scratchpad/fz/lanes/p91-*.green.*` (fz campaign) and
  `$PC/lanes/*.green.*`.
- **Bytes.** For each landed file I recomputed `git show <tip>:<path> | md5 -q` and compared it with the md5 line of
  the record. A match means the record certifies the landed bytes, built against the record's base.
- **Token scan.** I scanned every `GroupApproximation/Pestov91/*.lean` on main and `Palomar/Pestov91Solution.lean` for
  `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `ofReduceBool` and
  `trustCompiler`. There are no hits.
- **Build flags.** The `GroupApproximation` library builds with `-DwarningAsError=true` (`lakefile.toml`), so a
  `sorry` cannot survive a green probe of a development module. Declarations a driver does not print are covered by
  that and by the scan.
- **Root closure.** None of these modules is imported by `GroupApproximation.lean`. They are outside the root closure,
  so CI does not rebuild them; the probe records are the only build evidence. Wiring the roots is fz-integrate's
  job (fz RULES l.173).

## 5. Landed modules, records and closures

| File on main | Commit | fz lane | Record | md5 match | Printed closures |
|---|---|---|---|---|---|
| `Pestov91/Kazhdan.lean` | 8829513da | p91-kazhdan | 0913-011549-67162 | 1cde0115 ✓ | 8 decls, all [propext, Classical.choice, Quot.sound] |
| `Pestov91/KazhdanUnitary.lean` | 5f444f257 | p91-kazhdan | 0913-013033-80502 | 83bc2fa4 ✓ | 5 decls, all three axioms |
| `Pestov91/LEFHyperlinear.lean` | e3200c6c2 | p91-lef-hyperlinear | 0913-013243-89830 | ddeff60d ✓ | `isHyperlinear_of_isLEF`: three |
| `Pestov91/Centre.lean` | 03c0f1a39 | p91-infinite-centre | 0913-013453-2244 | 4ea9dd8c ✓ | 13 decls; `not_central_zero_or_one_zmod3`: [propext, Quot.sound]; others three |
| `Pestov91/CentreSkew.lean` | f3b198106 | p91-infinite-centre | 0913-015122-99396 | aca712d4 ✓ | 5 decls, three |
| `Pestov91/RingSimple.lean` | 89448ad3b | p91-ring-simple | 0913-015238-8742 | 328802c1 ✓ | 7 decls, three |
| `Pestov91/SplitSimplicity.lean` | d946a358a | p91-alt | 0913-020344-58235 | b015a339 ✓ | 9 decls; commutator lemmas [propext]; `central_unit_eq_one_of_central_zero_or_one` []; others three |
| `Pestov91/CrossedProduct.lean` | 21147debe | p91-ring-fg | 0913-021130-96995 | 6755e331 ✓ | 2 printed (`unit_zpow_mul_C`, `exists_sum_C_mul_unit_zpow`), three |
| `Pestov91/CrossedProductFG.lean` | 21147debe | p91-ring-fg | 0913-021130-96995 | 1c6958cc ✓ | 3 printed, three |
| `Pestov91/Assembly.lean` | b490bf08d, 8f4501419 | p91-palomar | 0913-020136-50440 | 4e61d99a ✓ | 4 decls, three |
| `Palomar/Pestov91Challenge.lean` | b490bf08d | p91-palomar | 0913-015019-93938 | ba2518e9 ✓ | (holes by design) |
| `Palomar/Pestov91Solution.lean` | 8f4501419 | p91-palomar | 0913-020136-50440 | c9d8247f ✓ | 11 decls, three |
| `wip/pestov91/fidelity/Pestov91ModelTests.lean` | 257b50a5d | p91-statement | 0913-021315-6428 | 238c0921 ✓ | 22 decls; `test_not_isSimpleGroup_punit` [propext, Quot.sound]; others three |

Every printed closure is a subset of `[propext, Classical.choice, Quot.sound]`. No record prints `sorryAx` or any
other axiom. pc-normal-a's consumption driver (`$PC/lanes/pc-normal-a.green.0913-021827-32723`) re-prints five of
these closures from main and agrees.

## 6. Per-module review

**6.1 `Kazhdan.lean`.**
- `elementary_hasKazhdanPropertyT {A : Type} [Ring A] (hA : IsFinitelyGeneratedRing A) (hn : 3 ≤ n) :
  HasKazhdanPropertyT.{0,0} EL_n(A)` is the Ershov–Jaikin-Zapirain statement. Its two binders are EJZ's own
  hypotheses.
- `IsFinitelyGeneratedRing A := ∃ s : Finset A, Subring.closure s = ⊤` (`PropertyT/FinitelyGeneratedRing.lean:66`) is
  the standard notion, calibrated at `ℤ`.
- No laundered Prop. `FinitelyGeneratedRingGeneralRankElementaryPropertyT` is established by the theorem
  `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` (l.486) and used as a term.
- (T) passes to quotients along a surjection. `HasKazhdanPropertyT.quotient` has no other declaration on main.
- **Prose (minor).** The module doc says "It carries no hypothesis". That is true of literature inputs. For the
  witness, however, `IsFinitelyGeneratedRing R` is still owed (blueprint G5), so the sentence should not be read as
  "(T) of the witness is proved".

**6.2 `KazhdanUnitary.lean`.** It transports each theorem through `hasKazhdanPropertyT_iff_complex`. It adds no
hypothesis.

**6.3 `LEFHyperlinear.lean`.**
- `isHyperlinear_of_isLEF := isHyperlinear_of_isSofic ∘ isSofic_of_isLEF`.
- The docstring claims the development bodies equal the Challenge bodies. The term-mode bridges in the Solution
  compiled in 0913-020136-50440, which confirms the claim.

**6.4 `Centre.lean`.**
- Central elements are scalars over central units. The theorem is general over rings and index types, with explicit
  hypotheses.
- The model tests are real: `𝔽₂` satisfies the trivial-centre hypothesis, `𝔽₃` fails it, and `EL₃(ℤ)/Z` is
  infinite.
- **Prose (minor).** "For the witness `Z(R) = 𝔽_q` … `S = EL₃(R)` for every lane" states a fact that no Lean
  declaration proves yet (blueprint G3). It is mathematically correct (A§1.4): freeness kills the coefficients at
  `j ≠ 0`, and minimality makes the coefficient at `0` constant.

**6.5 `CentreSkew.lean`.** `EL₃(LC(X,K) ⋊ ℤ)/Z` is infinite for every action, with no hypothesis beyond a nonempty `X`
and a nontrivial `K`. The proof uses the injectivity of `g ↦ single g b`, and the statement is sound as written.

**6.6 `RingSimple.lean`.**
- The theorems are abstract, with explicit hypotheses: `hconj`, `hspan`, `hkey` and `hfree`, `hmin`, compactness and
  total separation.
- `τ : ℤ → X → X` is not required to be an action. That is harmless, because the hypotheses are consumed as
  binders.
- Satisfiability for the witness: an infinite minimal subshift has no periodic point, which gives `hfree`. It is
  compact and totally separated. `hconj` and `hspan` are `unit_zpow_mul_C` and `exists_sum_C_mul_unit_zpow`.
- Credit: I did not verify the BCFS citation (arXiv:1204.3127).

**6.7 `SplitSimplicity.lean`, the simplicity core.**
- `isSimpleGroup_elementaryGroup_of_split` concludes `IsSimpleGroup EL_ι(R)` from four inputs:
  - `3 ≤ card ι`;
  - `[IsSimpleRing R]`;
  - `hcentral`: the only central unit is `1`;
  - `hsplit`: `∀ c d, d ≠ 0 → ∃ a b, b·c·a = 0 ∧ a·(d·b) ≠ 0`.
- `hsplit` fails in every commutative ring. At `c = d = 1` it forces `ab ≠ 0 = ba`. That is not a defect: it is
  derived for crossed products from `hkey` (`crossedProduct_split_annihilator`), and I checked the construction
  `a = u^r φ e`, `b = u^{-j₀} φ e` by hand at `c = d = 1`.
- **Missing model test.** No compiled instance of `isSimpleGroup_elementaryGroup_crossedProduct` on a concrete ring
  exists yet. Its hypothesis set has not been shown jointly satisfiable in Lean. The endpoint leaf G4 will be that
  instance. Until then the risk is a stalled proof, not a false one.

**6.8 `CrossedProduct.lean`, `CrossedProductFG.lean`.**
- `SkewMonoidAlgebra A (Multiplicative ℤ)` with the covariance relation and the normal form. The API is sound.
- `isFinitelyGeneratedRing_of_adjoin_translates` has an explicit hypothesis `hs`: the translates of a finite `s`
  generate `A` as a `K`-algebra. For `A = LC(X, 𝔽₂)` this holds only when `X` is expansive, that is a genuine subshift.
  For the odometer the algebra generated has bounded level, so `hs` fails there.
- Blueprint v3 (eb9eb62f8) pins `ToeplitzSpace` as Mathlib `Subshift Bool ℤ` orbit closure, which is expansive. The
  period-doubling point with `y₀ = bodd (padicValInt 2 0) = false` lies in the minimal Toeplitz subshift: shifts by
  `2^m`, with `m` even, reproduce every window. So the leaf is feasible.

**6.9 `Assembly.lean`.** All four theorems are conditional, with explicit binders:
- `hA`;
- `hsimple`;
- `hinfinite`, discharged in the crossed-product form;
- `hlef`.
The docstring says so. There is no laundered Prop.

**6.10 The Palomar pair and fz-integrate's gate.**
- The Challenge is reviewed in part 1 and is faithful.
- The Solution declares only `exists_infinite_simple_propertyT_{hyperlinear,sofic}_of`, each with the leading
  hypothesis `∃ E, Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0,0} E ∧ IsLEF E`.
- 764023101 lists `comparator-pestov91.json` as pending in `scripts/check_palomar_submission.py`.
- The drivers `scripts/PalomarPestov91{Axioms,ChallengeType,SolutionType}.lean` do two things:
  - they gate the `_of` closures, and fail if a name is missing;
  - they compare the transitive closures of the shared block, and print the unmatched statement types after a
    `pending-boundary:` line.
- Nothing presents the pair as submittable.

**6.11 `wip/pestov91/fidelity/Pestov91ModelTests.lean`.** This closes the gap of part 1 §2.1 with compiled negative
controls in the Challenge vocabulary:
- `test_not_hasPropertyT_int` and `test_not_isKazhdanPair_int`;
- `test_not_isSimpleGroup_punit`;
- `test_finite_simple_group_meets_all_but_infinite` and `test_int_meets_infinite_sofic_hyperlinear_not_propertyT`,
  which show every conjunct is load-bearing;
- `isSoficGroup_iff_isPestovSofic`, which is Theorem 3.5 (1)+(3);
- `test_identity_clause_is_implied`, which is 3.5(2);
- `isPestovHyperlinear_of_isHyperlinearGroup`, which is Theorem 3.6 (1)+(3) with `‖·‖₂ = √hsDistSq`. I checked the
  structure fields against p. 9.

Theorem 3.6(2) is not derived in Lean. It needs unitary left invariance of `hsDistSq`, which is a one-line trace
identity. The file is unwired, so its record is the only evidence.

## 7. Findings sent to lanes

No finding makes the endpoint false, vacuous or conditional, so none went to main.
- **F1, pc-el-center.** Draft `Center.lean` redeclares
  `GroupApproximation.Pestov91.center_elementaryGroup_eq_bot_of_central_zero_or_one` (landed in `Centre.lean`). This
  is a latent root break once both files are wired.
- **F2, pc-crossed-product.** Draft `instance locallyConstant_nontrivial` has the qualified name of `CentreSkew`'s
  theorem.
- **F3, pc-crossed-product and pc-architect.** The draft's path `Pestov91/CrossedProduct.lean` and its qualified names
  `CrossedProduct.C` and `C_apply` are occupied by fz's 21147debe. Blueprint v3 has since adopted the landed ring.
- **F4, pc-ring-lef.** `peer/Assembly.lean` (old fz bytes) and `peer/CrossedProduct.lean` (pc draft) shadow landed
  modules. A probe over them certifies an environment main does not have.
- **Resolved by the lanes themselves:**
  - pc-kazhdan retired its Kazhdan/LEF duplicate (41aa96770);
  - pc-ring-simple retired its RingSimple duplicate (abefd850d);
  - pc-ring-fg retired a stage-2 duplicate (1d5b85896).
- **Hygiene.** The fz commits carry `Claude-Session: …session_01Abcd4fUYaLXqZuLgyTuRf3`, as prescribed by fz RULES
  l.179. It is not this campaign's trailer.

## 8. State of the endpoint

- **No endpoint yet.** There is no binder-free `Pestov91.exists_infinite_simple_propertyT_{hyperlinear,sofic}` on
  main. Every assembly theorem is conditional, and it says so.
- **Remaining leaves (blueprint v3):**
  - subshift freeness, minimality and total separation;
  - `IsSimpleRing` of the witness ring;
  - centre `{0, 1}`;
  - simplicity of `EL₃` (the instance of 6.7);
  - finite generation (`hs` of 6.8);
  - local matrix models (LEF);
  - the endpoint and Palomar G8/G9.
- **Standing review obligations when the endpoint lands:**
  - it is binder-free;
  - its closure is read from a record;
  - the Solution's unsuffixed theorems match the Challenge types (fz-integrate's `ChallengeType`/`SolutionType`
    diff);
  - the witness type is in `Type`.
