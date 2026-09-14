# audit-nm-4 (simple Kazhdan note): the host's unsolvable word problem, and SL₃(ℤ) in no G_X

This lane was the non-MF audit lane of session nonsofic-existence-49 (ledger `notes/nm-swarm/reports/audit-nm-4.md`).
New item from main (RESUME 08:4x): building the two paragraphs of "LEF groups" in `simple_kazhdan_sofic_group.tex` at
696c4b602 (md5 0648e5f876e467e21ebf475e08b8ee92) that follow the Osajda remark and the topological full group paragraph.
At that tip they are l.473–494; census aa6f988f4.

- (A) key f5bd2ed413cf, l.473–480: "Every group as in the last statement of Corollary cor:host has unsolvable word
  problem: …" [KMS Theorem 4.21; Rauzy].
- (B) keys 46e5c2778909 (l.482), b331730d171e (l.482–485), 409ad03cdd34 (l.485–488), 5d1cbe7da012 (l.488–491),
  7979576f24ab (l.491–493). 44329368f3d9 (l.493–494, CFKP) is attribution.

## CLAIM

CLAIM (B) SL₃(ℤ) lies in no G_X, in new modules under `GroupApproximation/Manuscript/SimpleKazhdanSofic/`:
`CrossedProductSiteAction.lean` (the faithful action of M_m(LC(X,F₂)⋊ℤ) on sites), `SiteDegreeFiniteOrder.lean`
(distorted elements with bounded u-degrees have finite order), and `SLThreeIntNoEmbedding.lean` (the Heisenberg identity
and the printed endpoint).
CLAIM (A) host unsolvable word problem: `HostUnsolvableWordProblem.lean`, plus a statement module for the printed
route's missing inputs.

Interfaces: skf-degrees' `wordProblemOracle` and `wordProblemOracle_comp_injective`; sk-lef-assembly's `IsLEFHost` and
`PrintedRecursivelyPresentedLEFHost`; `Setting.G`, `ClopenCrossedProduct`.

## Ruling (main, ~09:0x)

1. (B) along the printed route first.
2. Then (A) via a recursively presented f.g. LEF group K with unsolvable word problem, plus the landed
   `printedWordProblemReducesUnderEmbedding`. This gives a closed carrier; the row stays `partial` with note ROUTE-DIFF.
3. State the printed route's missing inputs as named Props (time-complexity layer, time hierarchy, KMS 4.21) without
   building them.
4. Model-test K's relation criterion before building.

## (B) route and carriers

- **`CrossedProductSiteAction`**, LANDED 2a7e2ea6a (probe 0914-091837-93828: BUILT, compiled, audit classical;
  wire-queued).
  - `rho T k`: an f ∈ LC(X,k) acts by δ_{x,t} ↦ f(Tᵗx)δ_{x,t} and u by δ_{x,t} ↦ δ_{x,t+1}, through `liftNCRingHom`.
    The covariance uses T⁻ʲ(T^{t+j}x) = Tᵗx.
  - `rho_injective`: read the coefficient at u^j at the point y from level j at the site (T⁻ʲy, 0).
  - `rhoMat`, via `endVecRingEquivMatrixEnd`, and `rhoMat_injective`.
  - The displacement calculus: `NearSite`, `HasDisplacement` (with `.mul` and `.pow`), `UDegreeLE`,
    `hasDisplacement_rhoMat` (entries involving only u^j with |j| ≤ w give displacement w), and `exists_hasDisplacement`.
  - Endpoint `printedSiteActionFaithful : PrintedSiteActionFaithful` (key b331730d171e), over every X, T and m.
- **`SiteDegreeFiniteOrder`**, LANDED 3e627e581 (probe 0914-092248-4234: BUILT, compiled; wire-queued).
  - `hasDisplacement_listProd`: a word of length L moves site vectors at most Lw levels.
  - `exists_large_N_of_tendsto`: L(n)/n → 0 leaves room for m(2D+1) < N with D = max_{n<N} L(n)w.
  - `exists_poly_kill`: pigeonhole over F₂. The 2^N subset sums Σ_{n∈A} Eⁿv agree on the window of m(2D+1)
    coordinates for two sets A ≠ B, so p = Σ_A Xⁿ − Σ_B Xⁿ is a nonzero polynomial of degree below N that kills v.
  - `killers N`: the finite set of such p. Their product is monic, and `aeval_killers_eq_zero` shows it kills E.
  - `isOfFinOrder_of_hasDisplacement`: E is integral over F₂, so F₂[E] is finite. Two powers of E agree, and
    faithfulness makes two powers of g agree.
  - Endpoints `printedSiteSpanFewerDimensions` (409ad03cdd34) and `printedKillingPolynomialsFiniteOrder` (5d1cbe7da012).
- **`SLThreeIntNoEmbedding`** (probing).
  - With a = e₁₂(1), b = e₂₃(1), c = e₁₃(1): aⁿbⁿ = c^{n²}bⁿaⁿ, so c = [a,b], c^{s²} = [a^s,b^s], and c has infinite
    order.
  - For φ: SL₃(ℤ) → GL_m(R_X), write n = s² + r with r ≤ 2s. Then φ(c)ⁿ moves site vectors at most 3sW levels, where W
    bounds the displacements of φ(a^{±1}) and φ(b^{±1}).
  - K = 6mW + m + 1 and N = K² give m(2·3KW + 1) < N, so φ(c) has finite order and φ is not injective.
  - Endpoints `printedSLThreeIntInNoGX` (46e5c2778909; every subshift's G_X and every GL_m(LC(X,F₂)⋊ℤ)) and
    `printedHeisenbergDistortion` (7979576f24ab).

## (A) model test of K's relation criterion (before building)

K_S = ⟨a, t | a², [a, tⁿat⁻ⁿ] (n ∈ S)⟩, for an r.e. non-recursive S ⊆ ℕ≥1 (for example, the halting set).

- **Criterion.** For n ≥ 1, [a, tⁿat⁻ⁿ] = 1 in K_S iff n ∈ S.
- **Test.** For n ∉ S, let H_n = ⟨t = shift, a = (0 n)⟩ ≤ Sym(ℤ).
  - Every relator holds: a² = 1, and for s ∈ S the transpositions (0 n) and (s s+n) are disjoint, since s ∉ {0, n, −n}.
  - [a, tⁿat⁻ⁿ] = ((0 n)(n 2n))² ≠ 1.
  - So the criterion holds, and no Coxeter retraction is needed: `PresentedGroup.toGroup` into Sym(ℤ) is the carrier.
- **Remaining difficulty for K_S.** LEF needs a description of which short words are trivial (the right-angled Coxeter
  normal form of W_Γ ⋊ ℤ), and that is heavy.
- **Alternative K.** G_Y for the effective subshift Y ⊆ {0,1}^ℤ forbidding 1 0ⁿ 1 for n ∈ S.
  - L(Y) is co-r.e. and not recursive: 1 0ⁿ 1 ∈ L(Y) iff n ∉ S.
  - Y satisfies the cycle condition: a word 0^p·core·0^q lies on the periodic point (core 0^g)^∞ for any g ∉ S with
    g ≥ max(p,q).
  - So G_Y is LEF by the landed `printedSubshiftCycleConditionLEF` and `Pestov91.isLEF_elementaryGroup`, finitely
    generated by `printedSubshiftRingFinitelyGenerated`, and WP(G_Y) ≥_T L(Y) by skf-degrees'
    `PrintedLanguageReducesToWordProblem` (any subshift).
  - Its recursive presentation needs an r.e. certificate of triviality. A word is trivial iff every length-ℓ window w
    satisfies w ∉ L(Y) (Σ₁ for this Y) or the table value is 0.
  - Decision for main when (B) lands: K_S or G_Y.

## Log

- 08:5x: claim landed at 65738082.
- 09:0x: main rules (ii) for (A), with named Props for the printed route.
- 09:1x: module 1 LANDED at 2a7e2ea6a.
- 09:2x: module 2 LANDED at 3e627e581. Module 3 probing, after linter fixes, the commutator import and
  `open SymbolicDynamics.FullShift`.
- Infra: the local `git fetch` in nmprobe fails intermittently (infra, not Lean). Probes run inside a retry loop.
