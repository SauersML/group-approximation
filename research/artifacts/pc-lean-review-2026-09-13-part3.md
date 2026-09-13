# Pestov 9.1 in Lean: adversarial review (lane pc-review), 2026-09-13, part 3

Part 3: the fz surface, under the coordinator's scope change. It covers the bridges, the discharge tracker, new
landings, drafts still in flight, and gates and CI. Main is at 62f139b74 (02:40 CDT).

The coordinator asked for four checks on session 6dbfc571's fz swarm:
- (a) fidelity of the Challenge definitions, with model tests;
- (b) no hypotheses and no laundered Props in the final endpoint, tracking discharges until then;
- (c) axiom closures read from `fz/lanes/p91-*.green.*`;
- (d) the bridges between the Challenge and the repo definitions.

Part 1 covers (a). Part 2 covers (c) for the 13 files landed up to fa206d585. This part covers (b), (d) and what
landed afterwards. Findings stay here, since fz lanes cannot be messaged.

## 10. Bridges (d): correct

- **`HasPropertyT G ↔ HasKazhdanPropertyT.{0,0} G`** (`Palomar/Pestov91Solution.lean`).
  - `hasPropertyT_of_hasKazhdanPropertyTComplex` and its converse are the term `h` itself: the Challenge's
    `IsKazhdanPair` body is definitionally `IsKazhdanPairComplex.{0,0}`, and it compiled (record 0913-020136-50440).
  - The real/complex step `hasKazhdanPropertyT_iff_complex` (`Kazhdan/KazhdanComplex.lean:149`) keeps the same `Q`
    and `ε` in both directions. Realification: a complex Hilbert space with `Re⟨·,·⟩` has the same norm, and
    unitaries are orthogonal (`IsKazhdanPair.toComplex`, l.104). Complexification: `Complexification.mk x 0` has norm
    `‖x‖` (`IsKazhdanPairComplex.toReal`, l.114).
  - This is the standard equivalence, and I read the code of both directions.
- **`IsSoficGroup ↔ IsSofic`, `IsHyperlinearGroup ↔ IsHyperlinear`.** These repackage `FiniteCarrier` as
  `FiniteModel`. The fields (`nonempty`, `map`, `isUnitary`, `multiplicative`, `separated`) transfer verbatim, with
  identical bodies.
- **LEF ⇒ sofic.** `isSofic_of_isLEF (h : IsLEF G) : IsSofic G` (`Sofic/LEFSofic.lean:85`). I verified the statement
  and its closure (record 0913-013243-89830), not the proof. `IsLEF` is equivalent to textbook LEF by
  `isLEF_iff_textbook` (`Sofic/LEF.lean`).
- **Sofic ⇒ hyperlinear.** `isHyperlinear_of_isSofic` (`Sofic/Hyperlinear.lean:175`), proof read in full. It uses
  `σ ↦ (σ⁻¹).permMatrix ℂ`, a genuine homomorphism, and `hsDistSq = 2·hammingDistance` on permutation matrices, with
  tolerance `ε/2`. This matches Pestov's Theorem 3.3 computation.

## 11. New fz landing: `GroupApproximation/Pestov91/WitnessCentre.lean` (8443d297e, lane p91-palomar)

- **Record.** The landed md5 `fc7668f8…` equals record 0913-021857-34743, base 78041189e. All three printed closures
  are `[propext, Classical.choice, Quot.sound]`. The token scan is clean.
- **Statement.** `central_zero_or_one_of_free_minimal [TotallySeparatedSpace X] [Nonempty X] (τ) (hfree) (hmin)
  (hσ : (ofAdd j • f) x = f (τ j x)) (c) (hc : ∀ r, r * c = c * r) : c = 0 ∨ c = 1`.
  - This is exactly the hypothesis `hR` of `SplitSimplicity.isSimpleGroup_elementaryGroup_crossedProduct`, with
    freeness, minimality and the pullback form of the action as explicit binders.
- **Proof.** Freeness kills the coefficients at `j ≠ 0` through a clopen set separating `y` from `τ j y`. Commuting
  with `single t 1` makes the coefficient at `1` invariant, and minimality then makes it constant. That is A§1.4.

## 12. Discharge tracker (b): what the binder-free endpoint still needs

fz's own recorded route (report `p91-palomar.md`) is the `_of_elementary` form, with `A := WitnessRing` and
`EL₃(WitnessRing)` as the witness.

| Hypothesis | On main at 62f139b74 | Still owed or in flight (unlanded: not evidence) |
|---|---|---|
| `hA : IsFinitelyGeneratedRing A` | general reductions: `CrossedProductFG` (21147debe) and `RingFinitelyGenerated` (622570981, root-imported) | concrete `witnessRing_isFinitelyGeneratedRing`, binder-free, in fz `p91-ring-fg/WitnessRing.lean` (probe pending) |
| `hsimple : IsSimpleGroup EL₃(A)` | general: `SplitSimplicity` from `IsSimpleRing` (`RingSimple.isSimpleRing_of_minimal_free`), `hR` (`WitnessCentre`, §11) and `hkey` (`RingSimple.locallyConstant_cut_key`) | concrete dynamics: fz `p91-subshift` (Toeplitz, Subshift, SubshiftMinimal, SubshiftAlgebra; probe pending), giving freeness `shiftBy_ne_self`, density `dense_range_shiftBy` and compact T2 totally disconnected `X`. **No glue theorem instantiating SplitSimplicity on the witness exists yet**, so part 2 §6.7's missing model test is still open. An alternative route, `SimpleModCentre`, has been pending since 02:18. |
| `hinfinite : Infinite (EL₃(A)/Z)` | **discharged** for every action: `CentreSkew.elementaryModCentre_crossedProduct_infinite`, given `[Nonempty X]` | nothing further |
| `hlef : IsLEF EL₃(A)` | **nothing at a final path** | fz `p91-lef`: `IsLEFRing`, `IsLEFRing.isLEF_units`, `IsLEFRing.matrix`, `isLEF_elementaryGroup` (`LEF.lean`), and diagonal-times-shift-matrix models (`LEFCrossedProduct.lean`), plus the subshift's `exists_periodic_model`. **No probe record.** |
| (T), sofic, hyperlinear | derived from `hA` and `hlef` by `Kazhdan.lean`, `LEFHyperlinear.lean` and the Solution bridges | nothing further |
| Unsuffixed Solution theorems | absent; the configuration is pending | fz `p91-palomar`, after the leaves |

Until the `hlef` producer and the simplicity glue land, every endpoint on main stays conditional. The prose on main
says so.

## 13. Early notes on fz drafts in flight (read from `fz/src/`, not landed, not evidence)

- **Toeplitz point.** `toeplitz n = decide (ν₂(3n−1) % 2 = 1)`.
  - `3n − 1 ≠ 0` for integers, and `ν₂(3n−1) = ν₂(n − 1/3)` with `1/3 ∈ ℤ₂ \ ℤ`. So this is the period-doubling
    Toeplitz point at a non-integer odometer phase: every coordinate is determined, with no hole to fill.
  - The drafts prove aperiodicity (`toeplitz_exists_ne`) and uniform recurrence.
- **The subshift.** The carrier `{y | every window of y occurs in toeplitz}` is the language subshift, which equals
  the orbit closure of a uniformly recurrent point. The drafts give `Infinite X`, freeness, dense orbits and total
  separation (the driver checks it by `inferInstance`). `X` is expansive, as part 2 §6.8 requires.
- **Hygiene.** `abbrev X : Type := ↥subshiftCarrier` sits in namespace `GroupApproximation.Pestov91`. RingSimple,
  WitnessCentre and RingFinitelyGenerated bind their own `X`, which shadows it. A later declaration in that
  namespace that mentions `X` without binding it would silently specialize to the Toeplitz space.
- **The action.** `witnessAction`: `(ofAdd j • f) x = f (shiftBy (−j) x)`, so `τ j = shiftBy (−j)`. Freeness and
  density transfer under `j ↦ −j`.
- **The ring.** `WitnessRing : Type := SkewMonoidAlgebra (LocallyConstant X (ZMod 2)) (Multiplicative ℤ)`, in `Type`,
  as EJZ needs.
- **`IsLEFRing A`** asks, for each finite `t`, for a finite ring `F` and a map `φ : A → F` that is injective on `t`,
  sends `0 ↦ 0` and `1 ↦ 1`, and is additive and multiplicative on pairs from `t`. Mathematically it holds for the
  witness through the §3 periodic models.
- **Pending Palomar probe 0913-023600-15975.**
  - It changes docstrings only, identically inside both copies of the shared block. Definitions and the comparator
    json are unchanged.
  - The citations match the pages I read: Pestov Example 2.3 (p. 5), Example 2.7 and Definitions 3.1–3.2 (p. 6),
    Theorem 3.5 (p. 8), Theorem 3.6 and Remark 3.7 (p. 9).
  - Bekka–de la Harpe–Valette Definitions 1.1.1 and 1.1.3 are now verified at the source (part 1 §2.1): book
    pp. 32–33 of Bekka's hosted PDF, where §1.1 fixes complex Hilbert spaces and (T) asks for a compact Kazhdan set.
- **Advisory (raised by pc-palomar): statement strength.**
  - The Challenge states two separate existentials, one hyperlinear and one sofic. No compared theorem says that a
    single group is infinite, simple, (T), sofic and hyperlinear at once.
  - This is not a fidelity defect. The sofic existential answers both readings of 9.1, because sofic ⇒ hyperlinear is
    a theorem: the Solution's `isHyperlinearGroup_of_isSoficGroup`, and in Pestov, Theorem 3.3.
  - But that implication lives in the Solution's development, not in the Challenge environment. A conjunction
    `∃ G, Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧ IsSoficGroup G ∧ IsHyperlinearGroup G` would make the
    surface self-contained.

## 14. Gates and CI (verified)

- **B1, registry correction 8e8e38009: confirmed from the code.**
  - `scripts/PalomarPestov91ChallengeType.lean` seeds each target's closure walk from `info.type.getUsedConstants`
    (l.72), and walks values only for constants reached in the closure (l.79–81).
  - The shared definitions' types mention almost nothing, so the gated section before `pending-boundary:` compares no
    definition bodies.
  - Non-blocking while pending. `check_palomar_submission.py` gates textual byte identity of the block. Once the
    theorems are compared, their type closures reach the definitions and walk their values.
- **palomar-check CI on main.**
  - The last four runs concluded `failure` (`gh run list`; latest 34745087732 on 764023101).
  - fz-integrate's report attributes this to a tracked compiled file, `attic/gottschalk-swarm-2026-09-12/sweep/ugc.O`.
    That path is absent at 62f139b74, and no run on a later commit is listed.
  - Until a run passes, the MSI probe records are the only build evidence for the Palomar drivers.
- **Root wiring.**
  - fz-integrate's report describes a root landing of 10 imports, checked by a probe-only aggregator for name
    clashes. It is not on main at 62f139b74.
  - The only Pestov91 root import on main is `RingFinitelyGenerated` (622570981), which also brings `CrossedProduct`
    and `CrossedProductFG` into the root closure.

## 15. Blocking findings

None, so no message to main.
- Nothing on main makes the endpoint false or vacuous.
- No conditional result is described as unconditional, apart from the two minor prose overstatements of part 2 §6.1
  and §6.4.
- The Palomar configuration is correctly gated as pending.
