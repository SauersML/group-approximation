# Review: GKP Question 4.2 and `commuting-sofic-actions-need-not-combine`

Lane `gkp-verify`, 2026-09-13, main tip `3ef510f85`. Under review: `research/commuting-sofic-actions-need-not-combine.md`
with its requires chain (section 2), and the Lean proof landed in `29e593abf` (section 4).

## Verdict: PASS

The node answers Question 4.2 as printed: no. Every step re-derives from GKP's printed definitions and results
(2.14, 2.15, 2.16, 3.6) together with Kun–Thom Theorems A and E. The Lean endpoint on main is a faithful negative answer
with a GREEN probe and axiom closure [propext, Classical.choice, Quot.sound]. It is not yet root-imported. No earlier
or independent answer turned up as of 2026-09-13. The journal copy could not be opened, so its numbering is unverified.

## 1. Sources and the exact question

Gao, Kunnawalkam Elayavalli, Patchell, *Soficity for group actions on sets and applications*, arXiv:2401.04945
(v1 10 Jan 2024, v2 20 Jan 2024, v3 27 Aug 2025, 16 pp.). v3 was read page by page (PDF not committed). Its comment
reads "Final version, published in Research in the Mathematical Sciences". Journal: *Res. Math. Sci.* 12 (2025), no. 3,
art. 48, DOI 10.1007/s40687-025-00526-6 (Crossref; CC BY 4.0). Springer URLs hit a login or bot check. Cite v3.

**Question 4.2** (v3 §4, "Concluding remarks and open questions", p. 14), exactly:

> Suppose we have actions α_i : G_i ↷ X which commute with each other and where i ranges over a countable
> index set. Then the actions naturally give rise to an action α : ⊕_iG_i ↷ X. α is sofic iff all α_i are
> sofic?

It is one of two permanence questions "which we are currently unable to answer"; 4.3 asks the same for free products.
p. 2 asks 4.2 as a stability question. p. 15 says the forward direction follows from Proposition 2.15(3), and by
2.15(4) two groups suffice. So a two-group counterexample to the converse answers the question.

**Definitions (v3, p. 3, Definition 2.1).** G is a countable discrete group, X a countable discrete set, α : G ↷ X,
A a finite set, φ : G → Sym(A) a map (not necessarily a homomorphism), and d the normalized Hamming distance.
(1) *Unital*: φ(1_G) = 1. (2) *(F,ε)-multiplicative* (F finite): d(φ(gh), φ(g)φ(h)) < ε for all g, h ∈ F.
(3) *(F,E,ε)-orbit approximation* of α (E finite): there are a finite set B, S ⊆ A with |S| > (1−ε)|A|, and injections
π_s : E ↪ B (s ∈ S) with π_{φ(g)s}(x) = π_s(α(g⁻¹)x) for s ∈ S, g ∈ F, x ∈ E whenever φ(g)s ∈ S and α(g⁻¹)x ∈ E.
(4) G is *sofic*: for all finite F and ε > 0, some unital (F,ε)-multiplicative φ has d(1, φ(g)) > 1−ε for g ∈ F∖{e}.
(5) "α is called sofic if for all finite subsets F ⊆ G, E ⊆ X, and ε > 0, there exists a finite set A and a map
φ : G → Sym(A) which is unital, (F,ε)-multiplicative, and an (F,E,ε)-orbit approximation of α."

**Commuting and combined actions.** GKP define neither outside the question. The reading is α_i(g)α_j(h) =
α_j(h)α_i(g) for i ≠ j, with α((g_i)_i) = ∏_i α_i(g_i). For two groups, α(g,k) = α_1(g)α_2(k). Conversely, every
G_1 × G_2-action is combined from its restrictions along inl and inr, and those restrictions commute.

**Results used (v3).** Theorem 2.14 (p. 7): G sofic, N ≤ G locally finite ⇒ G ↷ G/N sofic. Proposition 2.15
(pp. 7-8): soficity passes to (1) compositions with quotient maps, (2) restrictions to orbits, (3) restrictions to
subgroups, (4) increasing unions. Proposition 2.16 (p. 8): sofic on every orbit ⇒ sofic. Definition 3.1 (p. 9):
G ≀_α H = G^{⊕X} ⋊ H. Theorem 3.6 = Theorem A (pp. 11, 2): G, H sofic and α : H ↷ X sofic ⇒ G ≀_α H sofic.
All of this agrees with `research/artifacts/gkp-2401-04945-verified.md` (read from v3, 2026-08-17). That record took
2.1(5) from an HTML fetch, and v3 p. 3 confirms it verbatim.

## 2. Re-derivation

**Chain.** Route `commuting-counterexample-from-kun-thom-pair` requires `kun-thom-nonsofic-wreath`,
`nonsofic-orbit-forces-commuting-counterexample` (route `diagonal-coset-commuting-counterexample-proof`, requiring
`gkp-sofic-action-toolkit`) and `coordinate-action-not-sofic` (route `coordinate-action-not-sofic-proof`, requiring
`kun-thom-nonsofic-wreath` and `gkp-wreath-permanence-theorem`). `kun-thom-free-nonsofic-action` is not required.

**Pair** (Kun–Thom Theorem E). q is a prime power, r, d ≥ 3, and Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x_1^±1..x_d^±1])
⋊ SL_d(ℤ). Both are residually finite Kazhdan groups, and Γ is infranormal but not normal. G is countable and sofic.

**Step 1: G ↷ G/Γ is not sofic.** Otherwise GKP 3.6 with (ℤ/2ℤ, G, coset action) makes (ℤ/2ℤ) ≀_{G/Γ} G sofic.
By Definition 3.1 this is Kun–Thom's wreath product, which contradicts their Theorem A. Kun–Thom state this
consequence in the introduction of v1 and v3.

**Step 2: the coordinate actions are free, hence sofic.** Let X = (G × G)/ΔΓ with left multiplication, α_1(g) = (g,1)·
and α_2(k) = (1,k)·. They commute and combine to the G × G-action, and X is countable. (g,1)(a,b)ΔΓ = (a,b)ΔΓ gives
(a⁻¹ga, 1) ∈ ΔΓ, so g = 1, and likewise for α_2. So each orbit is G ↷ G, sofic by Theorem 2.14 at N = {1}, and
Proposition 2.16 glues the orbits. Γ plays no role.

**Step 3: the combined action is not sofic.** Otherwise 2.15(3) makes its restriction to ΔG ≅ G sofic, and then 2.15(2)
makes the ΔG-orbit of ΔΓ sofic. gΓ ↦ (g,g)ΔΓ is well defined, equivariant, onto that orbit, and injective, since
(g,g)ΔΓ = (h,h)ΔΓ iff g⁻¹h ∈ Γ. Definition 2.1(5) transports along equivariant bijections, so G ↷ G/Γ would be
sofic, contradicting Step 1. □ All hypotheses hold, and the route nodes carry the same steps. **No mathematical error found.**

## 3. Kun–Thom inputs (arXiv:2608.06222, v1 6 Aug 2026, v3 20 Aug 2026; unrefereed)

**Theorem A:** Γ infranormal and not normal in G, both with property (T) ⇒ (ℤ/2ℤ)≀_{G/Γ}G not sofic. v3 adds the
double G∗_Γ G under the same hypotheses; only the wreath half is used. **Theorem E:** the pair above. **Theorem 4.1**
(Lean's route to A): Γ infranormal in G, both (T), σ a sofic representation of G ⇒ σ(G) normalizes the centralizer
of σ(Γ). **Not used:** Theorem C, Corollary D, Corollary 3.2 (the result behind `kun-thom-free-nonsofic-action`).

## 4. Lean on main (tip 3ef510f85; GroupApproximation modules outside CommutingSoficActions/ are root-imported)

**Definitions.** `IsSoficAction` (Sofic/SoficAction.lean:89, via `SoficActionModel` l.59); `IsSofic`
(Sofic/Sofic.lean:183); Palomar `IsSoficGroup` (Palomar/BowenChapmanChallenge.lean:96) with bridges
`isSoficGroup_of_isSofic`, `isSofic_of_isSoficGroup`, `isSoficGroup_iff_isSofic` (Palomar/BowenChapmanSolution.lean:94, 102, 113).

**Fidelity to 2.1(5).** `act` with `act_one` is unital, `act_mul` bounds `permDist` by ε on F, and `good` with
(1−ε)|Site| ≤ |good| is S. The finite `Chart` is B, with `chart_inj` on good × E and `chart_equivariant` under the
printed side conditions. The differences are ≤ for <, `siteNonempty`, a total `chart`, and no countability hypothesis. None matters. A GKP
model is a Lean model (|S| > (1−ε)|A| forces A ≠ ∅; Chart := Option B), and a Lean model at ε/2 is a GKP model at ε.

**Kun–Thom side.** `BowenChapman.Ambient` (BowenChapman/LaurentPair.lean:189) = EL₃(F₂[ℤ³]) ⋊ EL₃(ℤ) and
`Peripheral` (l.197): Theorem E at q = 2, r = d = 3. Pair facts: `ambient_residuallyFinite`
(LaurentPairResiduallyFinite.lean:28; a theorem, use `haveI`), `ambient_countable` (LaurentPairGeneration.lean:94),
`peripheral_isInfranormal` (LaurentPairInfranormal.lean:338), `ambient_hasKazhdanPropertyT` and
`peripheral_hasKazhdanPropertyT` (LaurentPairKazhdan.lean:58, 63). Theorem 4.1:
`hasSequentialCentralizerNormalization_of_kazhdan_infranormal` (KunThom/CompressorNormalizationCore.lean:101).
Theorem A, wreath half, conditional: `cosetWreath_not_isSofic_of_sequentialNormalization`
(BowenChapman/WreathWitness.lean:51) on `CosetWreath` (l.35); its docstring still calls the hypothesis unproved (stale).
GKP 3.6: `GeneralizedWreath.isSofic_wreath` (Sofic/GeneralizedWreathSofic.lean:40), same `Wreath`
(Algebra/PermutationalWreath.lean:182). Group soficity: `isSofic_of_isLEF`, `isLEF_of_residuallyFinite`
(Sofic/LEFSofic.lean:85, 137), `isSofic_of_finite` (Sofic/SoficPositiveControl.lean:99).

**GKP toolkit side.** `IsSoficAction.compHom` (Sofic/SoficAction.lean:132) is 2.15(3) along a homomorphism, and
`IsSoficAction.of_equivariant_injective` (Sofic/SoficActionEmbedding.lean:47) is 2.15(2) plus transport.
`isSoficAction_quotient_of_separable` (Sofic/SoficActionChabauty.lean:134) with `isSoficAction_of_stabilizers`
(Sofic/SoficActionOrbits.lean:235) gives 2.14 at N = {1} plus 2.16, for residually finite G only. There is no general
`IsSofic G → IsSoficAction G G`, only the converse (Sofic/RegularActionSofic.lean:111), but residual finiteness suffices.
Diagonal cosets: `eq_one_of_fst_smul_fixed`, `eq_one_of_snd_smul_fixed`, `diagOrbitMap_injective`, `diagOrbitMap_smul`
(Algebra/DiagonalCosetAction.lean:56, 70, 115, 128).

**Landed assembly (`29e593abf`, 2026-09-13).** GroupApproximation/CommutingSoficActions/ has four modules. Their
blobs equal the gkp-lean sources this lane read, and they follow section 2 through the declarations above:
- **FreeActionSofic** (`isSoficAction_of_free`, `isSoficAction_diagonalCosets_inl`/`_inr`) is Step 2.
- **DiagonalRestriction** (`isSoficAction_quotient_of_isSoficAction_diagonalCosets`, `diagonalCosets_counterexample`) is Step 3.
- **KunThomCosetAction** (`ambient_isSofic`, `peripheral_hasSequentialCentralizerNormalization`,
  `not_isSoficAction_ambient_quotient_peripheral`) is Step 1.

The endpoint is Endpoint.lean:57, `exists_commuting_sofic_actions_not_sofic`: ∃ G X : Type, `MulAction (G × G) X`, Countable G ∧ Countable X ∧
IsSofic G ∧ (inl restriction sofic) ∧ (inr restriction sofic) ∧ ¬ IsSoficAction (G × G) X, witnessed by `Ambient`
and (Ambient × Ambient) ⧸ ΔPeripheral. By section 1 that is a faithful negative answer. The form with two commuting actions
and (g,k)·x := g·(k·x) is equivalent.

**Axiom gating.** fzprobe lane gkp-lean, tag 0913-024821-55537, base 9544c83e5: PROBE GREEN. A probe-only driver
(not landed) printed [propext, Classical.choice, Quot.sound] for the endpoint, `diagonalCosets_counterexample` and
`not_isSoficAction_ambient_quotient_peripheral`. Between 9544c83e5 and 3ef510f85, no file in the endpoint's 443-module
repo import closure changed, and neither did lean-toolchain, lakefile or lake-manifest. So the evidence covers the tip.
Nothing on main prints these closures. The root does not import the modules, and the Bowen–Chapman Comparator route
(BowenChapman/Endpoint.lean, EndpointOfNormalization.lean, NormalizationFromCriterionConsumer.lean) never mentions
`isSofic_wreath`, `CosetWreath` or `IsSoficAction`. Still to do: the root import, and a Palomar statement with its own Comparator run.

## 5. Priority and novelty, refreshed to 2026-09-13

Repo record: the root node, its route nodes and `research/artifacts/commuting-sofic-actions-note-2026-08-17.md` first
landed in `393a096b6` (2026-08-17), and `coordinate-action-not-sofic` in `354135299` (2026-08-14). Kun–Thom v1 and v3
print Step 1 in their introduction, but they never mention commuting actions or Question 4.2, and do not contain Steps 2-3.

Semantic Scholar lists 7 works citing GKP (Crossref and OpenAlex list no journal citations): arXiv:2608.06222, 2607.29571,
2601.18742, 2508.06731, 2506.18320, 2408.15470 and 2402.17150. None answers 4.2 or reports it settled. Also checked:
arXiv:2608.02025v2, 2604.19174, an arXiv "sofic action" search (entropy and mean dimension only), and web searches
on 4.2 with commuting actions or direct sums (only GKP and the works above). No earlier or independent answer found.
The search had limits: one author page returned 404, and journal-side citing records could not be opened.

## 6. Scope

Only the converse of 4.2 is answered; the forward direction is 2.15(3). Question 4.3 (free products) is untouched. The
witness's G∗G-action factors through G × G, and 2.15(1) only transfers soficity up from the quotient's action. By p. 15,
a positive 4.2 would settle 4.4 (the converse of 3.6) via the conjugation action. A negative 4.2 settles neither 4.4 nor
the conjugation case. Step 1 answers GKP's p. 8 remark "It is still open whether all actions by sofic groups are
sofic". That answer is Kun–Thom's, not this repo's.
