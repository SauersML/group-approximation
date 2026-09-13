# baseline-debt lane report

Lane `baseline-debt`, roster section `## baseline-debt`. The census findings are in
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`. Line numbers below point into that file
at origin/main 8f4475102. Census rows are in `metadata/nm-census-rows/baseline-debt.tsv`.

## Landed

- `95e6d09ca`: three new modules, landed unverified. The only change since is a one-name
  fix in `StrongConvergenceMFSubsingleton`.
- `296386753`: the four modules in the table, from probe 0913-021321-7359.
  - The probe reported `PROBE GREEN` and COMPILED all four overlay files.
  - `StrongConvergenceMFSubsingleton` was rebuilt. The other three were replayed with the
    same input hash, after being BUILT in probe 0913-020324-57087.
  - The `#audit_axioms` and `#audit_closed_axioms` lines show only `propext`,
    `Classical.choice` and `Quot.sound`.
  - The three new modules are queued for wiring.
- `bf625daf4`: this report and the census rows.
- `72599dad7`, probe 0913-025420-71482: the stale docstrings that audit-sec5 found
  in `RegularNonMFAlgebra` and `TorsionFreePrintedSentences`. No statement changed.
  - The printed corollary and proof are quoted as they now read (tex 1718-1736). The
    not-MF clause cites `prop:mf-residual-calculus`, not an embedding into the corona's
    unitary group.
  - "No vocabulary for hyperbolically embedded" is replaced, in four places, by the closed
    `exists_isNonDegenerate_isHypEmbedded` (`OsinTheorem12NonDegenerate`, Osin 1.2,
    `(AH₁) ⇒ (AH₄)`).
  - `DGOTheorem235Printed` and `GerasimovaOsinTheorem11Printed` are recorded as proved:
    `dgoTheorem235Printed` and `gerasimovaOsinTheorem11Printed`. Both carry
    `#audit_closed_axioms` and are imported by the root.
- `dd0412114`, probe 0913-034738-16893: `GGT/HullLemma35Printed.lean` (new, definitions
  only), the statements of Hull Lemma 3.5 and of `{G₁, G₂} ↪h G₁ ∗ G₂`.
- `87762b46c`, probe 0913-051219-87168 (both modules BUILT): `GGT/HullLemma35FreeFactors.lean`
  (new) proves `printedFreeFactorsHypEmbedded`. The module doc of `HullLemma35Printed` now
  records the proof. Queued for wiring.
- `72a023f67`: this report, after the free-factor proof.
- `be6e71f04`: `GGT/HullLemma35Transitive.lean` and `GGT/HullLemma35LocalFinite.lean` (both
  new), the witness structure of Hull Lemma 3.5 and its local finiteness.
  - Probe 0913-081320-10853 was `PROBE GREEN` and BUILT `HullLemma35LocalFinite`.
  - `HullLemma35Transitive` was BUILT in 0913-080412-2056 and replayed with the same source.
  - `#audit_axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.
  - Both modules are queued for wiring.

| module | declarations |
|---|---|
| `Manuscript/NonMFSentences/FullDefectPairLeavitt.lean` (new) | `fullDefectPair_aryLeavittAlgebra`, `fullDefectPair_aryLeavittAlgebra_zmodTwo` |
| `Sofic/StrongConvergenceMFSubsingleton.lean` (new) | `isStronglyOperatorMF_of_subsingleton`, `isStronglyOperatorMF_unit` |
| `Manuscript/NonMF/NaiveFreeProductPropertyOfAcylindricallyHyperbolic.lean` (new) | `naiveFreeProductProperty_of_isAcylindricallyHyperbolic`, `powersAveragingEstimate_of_isAcylindricallyHyperbolic` |
| `Manuscript/NonMF/TorsionFreePrintedSentences.lean` (edited) | `PrintedTheoremQuotientTrivial`, `manuscriptSentence_theoremQuotientTrivial : PrintedTheoremQuotientTrivial` |
| `GGT/HullLemma35Printed.lean` (new) | `IsHypEmbeddedFamily`, `PrintedHullLemma35`, `PrintedFreeFactorsHypEmbedded` |
| `GGT/HullLemma35FreeFactors.lean` (new) | `printedFreeFactorsHypEmbedded : PrintedFreeFactorsHypEmbedded`, `FreeFactorsHypEmbedded.factorsRelGenSet`, `FreeFactorsHypEmbedded.relBall_finite`, `FreeFactorsHypEmbedded.isFourPointHyperbolic_alphabet` |
| `GGT/HullLemma35Transitive.lean` (new) | `HullLemma35.transitiveRelGenSet`, `isSymmetricGeneratingSet_transitive`, `transitive_alphabet_subset` |
| `GGT/HullLemma35LocalFinite.lean` (new) | `HullLemma35.relBall_finite_transitive`, `exists_enlargedWord`, `relBall_subset_image` |

## Findings closed

The census merge at 63f147d7b removed all five findings as stale ("matches no finding").
Baseline lines 78, 97, 171, 238 and 298 are now `# REMOVED` comments.

- **(a) open-predicate `FullDefectCornerRemark.manuscriptSentence_cornerPassesUp`**
  (baseline 238, tex 1008).
  - The premise `FullDefectPair (Corner R p hp)` is the printed hypothesis of the sentence:
    "the ring pRp, with unit p, satisfies the hypothesis".
  - `FullDefectPair` has an honest producer. At `L_k(1,d)` with `d ≥ 2`, take `s = s₀` and
    `t = t₀`; then `t₁(1 - s₀t₀)s₁ = 1`. It is closed at `L_{𝔽₂}(1,2)`.
- **(b) inlined-statement `TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientTrivial`**
  (baseline 171, tex 1711-1716).
  - The theorem is now the closed endpoint `PrintedTheoremQuotientTrivial`, with no
    binders, proved from `manuscriptSentence_theoremHomsTrivial`.
- **(c) open-predicate `ReducedGroupCStarTrace.powersAveragingEstimate_of_naiveFreeProductProperty`**
  (baseline 298, tex 1725).
  - `NaiveFreeProductProperty G` is produced at countable acylindrically hyperbolic `G`
    with `HasTrivialFiniteRadical G`, from the closed `naiveFreeProductAtAcylindricallyHyperbolic`.
  - The classifier's least fixpoint admits this producer: its corpus premises have closed
    producers, `instIsAcylindricallyHyperbolicFreeGroupFinTwo` and
    `hasTrivialFiniteRadical_of_torsionFree` from `isPowerTorsionFree_multiplicative_int`.
    The census merge confirms it.
- **(d) carrier-data `IsStronglyOperatorMF` (baseline 78) and open-predicate
  `IsStronglyOperatorMF.isOperatorMF` (baseline 97)**, tex 99 (printed 102-105).
  - Verified: `not_isStronglyOperatorMF_of_not_isOperatorMF` is the printed contrapositive.
  - The carrier has an honest producer: a trivial group is strongly MF, closed at `Unit`.

## (e) carrier lines and (f) remaining findings: classification

Every active finding names its owner in its baseline note. None is an unowned non-wall
citation.

- Not walls, already owned:
  - 341, inlined-statement `LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial`:
    owner leavitt-units. The premise is `thm:full-defect-ring` at `L_k(1,d)`, proved inside
    the sibling carrier.
  - 362, buried-conditional `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`:
    owner cite-hull. The premise is Hull Lemma 5.8's printed hypothesis, not a citation.
- Walls only:
  - 381 `HullSC.hullCommonQuotientPrinted_of_oneStep`, from the Theorem 7.1 leaves: owners
    hull-respell, hull-bridge, sec5-sentences.
  - 393 `TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_closedCitations`, from
    FFF S2 through `KotowskiOllivierStatement` and `FinitelyPresentedInfiniteSimpleStatement`:
    owners simple-group, kh-hyperbolic, kh-torsion.
  - Every other active line is one of three kinds:
    - an `_of_leastAreaLeaves`, `_of_hullLeaves(_closedGO)`, `_of_fourLeaves`,
      `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`, `_of_leastAreaZipFold` or
      `kotowskiOllivier_of_leaves` wrapper, with its buried-conditional twin;
    - a carrier-data `Printed*` line produced only through those wrappers: 267, 321, 322,
      350-353, 363, 366, 377, 388, 391, 392;
    - the conditional-data 378 `fournierFacioParagraph_of_literatureInputs`.
    nm-endpoints owns the wrappers.

## Residual statements (exact)

1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`
3. `TheoremC.KotowskiOllivierStatement`
4. `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`

These walls are owned by other lanes: hull-*, kh-* / ko-closed, and simple-group. Wall 4 is
closed by `finitelyPresentedInfiniteSimple_closed` (47b31bef8, simple-group).

This lane's own open item is `GGT.PrintedHullLemma35.{u}` (below).

## Hull Lemma 3.5

Ruling of 09-13 08:30: this lane owns Hull Lemma 3.5, including the printed form. cite-hull
stands off it.

- Source checked against arXiv:1308.4345v2 (`pdftotext -layout`).
  - Lemma 3.5 is on p. 12 of §3. Hull prints it without a proof, as a "simplification of
    [DGO, Proposition 4.35]".
  - Definition 3.1 defines `{H_λ} ↪h G` as `↪h (G, X)` for some `X ⊆ G`.
  - The proof of Corollary 7.4 (§7) says "Since `{G₁, G₂} ↪h F`, Lemma 3.5 gives that
    `{⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩} ↪h F`".
  - Hull's Lemma 5.9 also "follows from Lemma 5.8 and Lemma 3.5".
- Statements, `GGT/HullLemma35Printed.lean` (`dd0412114`):
  - `IsHypEmbeddedFamily G H := ∃ D : RelGenSet G Λ, D.fam = H ∧ D.IsHyperbolicallyEmbedded`;
  - `PrintedHullLemma35.{u}`: all `n`, `H : Fin n → Subgroup G`, `m`, and
    `K : ∀ i, Fin (m i) → Subgroup (H i)`, with the family indexed by `Σ i, Fin (m i)`;
  - `PrintedFreeFactorsHypEmbedded.{u}`: `![inl.range, inr.range]` in
    `Monoid.Coprod G₁ G₂`, for all groups.
- **`PrintedFreeFactorsHypEmbedded`: closed.** `printedFreeFactorsHypEmbedded` in
  `GGT/HullLemma35FreeFactors.lean` (`87762b46c`) carries `#audit_closed_axioms`. The
  witness is `X = ∅`.
  - Local finiteness: every relative ball is `{1}`. The invariant "the partial product is
    `1` or its reduced word begins in the other factor" uses `RelHyp.headIdx_mul_of`.
  - Hyperbolicity: `isFourPointHyperbolic_unionCarrier` at the full factor alphabets
    (`δ = 1`), carried along `coprodIBoolEquiv` in every universe.
- **`PrintedHullLemma35`: open. Local finiteness is closed; hyperbolicity remains.**
  - The witness is `transitiveRelGenSet D E` (`be6e71f04`). Its base is `RelHyp.properBase D`
    together with the images of the bases of the `E i`, and its members are the `K_{ij}`.
    The letters of `D.base` that lie in some `H i` are dropped. Keeping them fails, because
    the inverse of such a letter may be a letter only of `H i`. Hull's base is existential,
    so dropping them costs nothing.
  - Local finiteness: `relBall_finite_transitive`. A path of length at most `n` is read
    through `H i`. Every excursion out of `H i`, and every letter of another member, becomes
    one letter of the finite set `excursionLetters D i n ⊆ D.relBall i n`. The bound is the
    Corollary 4.27 local half, `RelHyp.relBall_finite_adjoinBase'`.
  - Remaining: `Γ(G, transitive alphabet)` is hyperbolic. The plan is Bowditch's criterion
    (`OsinEnlargement.guessingGeodesics`) along a geodesic word of `D`, with each component
    letter expanded into a geodesic word of `E i`. This generalizes the `Uncone` chain from
    cyclic members to hyperbolic replacement graphs.
    - The step and short-path conditions come from local finiteness.
    - The thin-triangle condition comes from the triangle connectors (`Uncone.TriangleConnectors`,
      stated for any `D`), a quadrilateral and hexagon bound in `Γ(H i, Y_i ∪ K^i)`, and the
      corner walk.
- **Finding: `RelHyp.DGOProposition435PrintedStatement` is false as formalized.**
  - Counterexample: `G = Multiplicative (ZMod 5)` with generator `t`, `D.base = {t²}`,
    `fam = ⊤`, `M = PEmpty`, `E.base = {t, t⁻¹}`.
  - The statement forces the base `{t², t, t⁴}` with no members. That alphabet is not
    inversion-closed, so no `RelGenSet` has it.
  - Its `h435` consumers in `DGOProposition435Printed.lean` are vacuous. The finding was sent
    to the team lead. This lane's route does not use that statement.

## Next

- Wiring: `296386753` (three modules), `dd0412114`, `87762b46c` and `be6e71f04` (two
  modules) are queued.
- The team lead accepted (a) through (d) as closed; census registers them at its re-baseline.
- Hyperbolicity for `PrintedHullLemma35`, in new modules. First the expansion (guessed paths,
  step and short-path bounds), then the piece geometry, the letter and corner lemmas, and
  the thin-triangle assembly. Last, the endpoint `printedHullLemma35 : PrintedHullLemma35`
  with `#audit_closed_axioms`.
