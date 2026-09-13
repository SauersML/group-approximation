# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 1 of 3

Lane `un-synthesis`, 2026-09-13, refresh 3 (main tip 6e4ef12930). This is the single readable account of the UN
swarm's theory. It proves nothing new. Every statement names its node and carries a status taken from the verifier
artifacts; no status is upgraded here.

- **Review landings used:**
  - `un-review-2026-09-13` part1 171f0f7525, part2 638d4941b5, part3 f15928d5c9, part4 d60f405998, part5 7c7fdace42,
    part6 c725d8a93f, part7 e6fc337462, part8 cf2fc07fe6 (subsumption correction e4a5be7585), part9 811353c0ef,
    part10 81d6f6e73b, part11 e07954d78e;
  - `un-review-measure` part1/2 10083fd646, part3 72ff092a72, part4 f4ffedeaea, part5 97bf4bc468;
  - `un-review3` part1 2ba472b59d, part2 fbaddd57b0, part3 560decb046, part4 1df28bd83f, part5 c341a29e49,
    part6 ef5760d6c3;
  - `un-review-open` part1 5c8c71e333, part2 d166da76b2.
- **Novelty verdicts used:** `un-novelty` part1/2, plus the SUBSUMED and PRIOR lines inside the review artifacts.

**Status tags.**
- **[PASS · sha]:** re-derived by an independent verifier; the sha is the review landing.
- **[unreviewed]:** established on main by a complete route, not yet re-derived.
- **[import]:** a literature theorem quoted verbatim.
- **[printed]:** a theorem of `non_mf_groups_exist.tex` (line given).
- **[OPEN]:** an open claim.
- **Novelty tags:** NEW (bounded), FOLKLORE, PRIOR, SUBSUMED.

Part 2: the two mechanisms, radicals, the MF spectrum, traces, coarse and unit-group faces. Part 3: complexity,
continua, characteristic dependence, families, examples, the open core, ledger, credits.

## 0. The thesis: the approximation type of a Kazhdan elementary group mirrors the type of its ring

**Root** `kazhdan-elementary-approximation-type-mirrors-ring-type` [OPEN]. Let `R` be a countable simple unital ring.
For finitely generated `R`, every `EL_N(R)` (`N ≥ 3`) is Kazhdan (EJZ [import]). Three rungs:

| rung | ring type | group type | ⇐ (ring ⇒ group) | ⇒ (group ⇒ ring) |
|---|---|---|---|---|
| (L) | exactly matricial: unital embedding in `∏_ω M_(d_k)(F_k)` | `EL_N(R)` LEF for all `N` | PASS · 2ba472b59d | PASS · 560decb046, f4ffedeaea (one rank `N ≥ 4` suffices) |
| (Σ) | unital rank model over `k` (centre `k`, `k` finite) | `EL_N(R)/scalars` `k`-linear sofic for all `N` | PASS · 2ba472b59d | **OPEN, famous-level** |
| (M) | stably finite ⟺ `[R]` not paradoxical in `V(R)` | `EL_N(R)` operator MF for all `N` | **OPEN** | PASS · 2ba472b59d + 638d4941b5 |

**Node names.**
- (L⇐) `exactly-matricial-rings-have-lef-general-linear-groups`.
- (L⇒) `lef-el-groups-force-exactly-matricial-simple-ring`, via `lef-elementary-groups-force-lef-rings` and
  `simple-lef-rings-are-exactly-matricial`. The hypothesis GAP noted at f4ffedeaea: the proof uses a countable exhausting
  sequence.
- (Σ⇐) `rank-modelled-simple-rings-give-linear-sofic-projective-el`; (Σ⇒) `linear-sofic-el-groups-force-rank-model`.
- (M⇒) `mf-elementary-groups-force-stably-finite-simple-rings` with `simple-ring-stably-finite-iff-unit-not-paradoxical`;
  (M⇐) `stably-finite-simple-rings-have-mf-elementary-groups`.

**Rung (L) is closed for simple rings** [PASS · 560decb046]. For countable simple `R` the following are equivalent:
- `EL_N(R)` is LEF for one `N ≥ 4`;
- `R` is a LEF ring;
- `R` embeds unitally in a matrix ultraproduct over finite fields;
- every `GL_M(R)` and `EL_M(R)` is LEF.

The (⇒) proof extracts a finite level ideal from the finitely presented Steinberg cover. Rank 3 alone is not covered.

### 0.1 The open core

**(Σ⇒)** [OPEN; un-sigma-converse 3fa78684f7].
- **Exact lift** [PASS · ef5760d6c3, `linear-sofic-projective-el-lifts-to-gl-rank-models`]. A projective `k`-linear sofic
  model of `S_N` lifts, through `Ad(A) = A ⊗ (A⁻¹)ᵀ`, to a homomorphism `EL_N(R) → ∏_ω GL/d_rank` whose kernel is exactly
  the scalars. So (Σ⇒) needs no stability input: it reduces to the algebraic ring-rigidity statement (RR_k) of the artifact.
- **What is missing is a frame.** The root images carry a group commutator, not a ring product. A ring structure appears
  only after idempotents `e_1, e_2, e_3` with the root images in `e_i M e_j`.
- **Famous-level firewall** [PASS wiring · ef5760d6c3, route `non-linear-sofic-via-sigma-converse-at-leavitt`; cannot fire].
  (Σ⇒) at `L_(F_2)(1,2)`, which has no unital rank model, produces a countable group that is not `F_2`-linear sofic. That
  is the root `non-linear-sofic-group`.

**(M⇐), in its correct form** [OPEN; Proposition R of un-m-converse 6afb261048, unreviewed; corrected node wording PASS ·
e07954d78e]. For countable simple unital rings:
- (M⇐) ⟺ every simple stably finite `R` has `mf(R) = ∞`;
- equivalently `rig(R) = ∞` **and** the middle regime is empty.

So it splits into a **rigidity half** (stable finiteness prevents rigidity) and a **lifting half** (no middle regime).
The earlier wording "empty middle regime", or "`mf = ∞` or `rig < ∞`", was not correct and has been withdrawn.
- **The lifting half is automatic over `F_2`** [PASS · e07954d78e, `f2-steinberg-elementary-groups-have-no-middle-mf-regime`,
  with a scope repair]. For minimal effective Hausdorff ample `𝒢` with compact infinite unit space and `R = A_(F_2)(𝒢)`,
  every `EL_N(R)` (`N ≥ 3`) is MF or MF-rigid. The mechanism is Theorem S [PASS, folklore in substance]: a simple-mod-centre
  `EL_N` with trivial centre is MF as soon as it has any nontrivial MF image.
- **The decider: the Labbé ring over `F_2`** [OPEN, `labbe-wang-shift-crossed-product-is-exactly-matricial`].
  `R = LC(Ω_U,F_2)⋊ℤ²` is simple, finitely generated and stably finite, with a rank model. If `R` is not exactly matricial,
  every `EL_N(R)` (`N ≥ 4`) is non-LEF by rung (L), and exactly one of these holds:
  - **MF, non-LEF:** a new object, a simple Kazhdan group that is MF but not LEF;
  - **MF-rigid:** a counterexample to (M⇐), which would be a new non-MF mechanism.

  See part 3 §16 for the torus criteria.

**The root stays OPEN** while (Σ⇒) and (M⇐) are open. A counterexample to either is itself a new object.

**What the root unifies.**
- Pestov 9.1 is (L⇐) at `LC(X,F_q)⋊ℤ`.
- The non-MF paper's Leavitt theorem (tex Cor l.1016) is (M⇒) at `L_k(1,2)`.
- Both rings are Steinberg algebras of minimal effective ample groupoids (§2), with uniformly simple elementary groups
  (§3). Only the ring type decides the approximation type.

## 1. The two calibrating results

- **Non-MF paper.**
  - **[printed l.918]** Let `R` be countable unital with `ts = 1` and `R(1−st)R = R`. Then for `n ≥ 2` every homomorphism
    from `EL_n(R)` to an MF group is trivial. **[printed l.1016]** This covers simple rings that are not directly finite.
  - **[printed l.1038]** `C*_r(EL_n R)` is stably finite and not MF.
  - **[printed l.1218]** For purely infinite simple `R`, `Rad_MF(GL_n R) = [GL_n R, GL_n R]`, with quotient `K_1(R)`.
  - **[printed l.1349]** Not MF ⇒ the canonical trace is not quasidiagonal.
- **Pestov 9.1** [PASS twice; Lean + Comparator]. For an infinite minimal subshift `X`, `LC(X,F_q)⋊ℤ` embeds in
  `∏_ω M_N(F_q)` by return-word towers, and `S = EL_3(LC(X,F_q)⋊ℤ)/Z` is infinite, simple, Kazhdan and LEF.

## 2. The dictionary

- **Leavitt algebras** [import, PASS · 2ba472b59d; `leavitt-path-algebras-are-steinberg-algebras`]. `L_k(1,2) = A_k(𝒢_2)`.
- **Crossed products** [PASS · 2ba472b59d; **PRIOR** Beuter–Gonçalves 2018; `crossed-products-are-transformation-steinberg-algebras`].
  `LC(X,k)⋊Γ = A_k(X⋊Γ)`.
- **Simplicity of the algebra** [imports, PASS · 171f0f7525, e6fc337462]. `A_k(𝒢)` is simple ⟺ `𝒢` is minimal and
  effective (Steinberg; Clark–Edie-Michell). In the non-Hausdorff case add "no nonzero singular element" (CEPSS).
- **The bridge `ι : S(𝒢) → V(A_k 𝒢)`** [PASS · f15928d5c9]. Groupoid paradox gives ring paradox over every field.
  - Whether `ι` reflects paradox: [OPEN] `type-semigroup-reflects-paradox-of-steinberg-algebra`, Kaplansky-hard.

## 3. Uniform simplicity

**Theorem S4** [PASS · 171f0f7525; `steinberg-elementary-groups-are-simple-mod-centre`]. Let `𝒢` be Hausdorff ample,
minimal and effective, with compact infinite unit space, `R = A_k(𝒢)` and `n ≥ 3`. Then:
- every normal subgroup of `EL_n(R)` is central or everything, and `Z ⊆ k^× I`;
- `EL_n(R)/Z` is infinite and simple;
- it is finitely generated and Kazhdan when `k` is finite and `R` is finitely generated.

**Supporting results.**
- The Lean criterion `Pestov91.isSimpleGroup_elementaryGroup_quotient_center` (local annihilation) carries the proof.
- **Theorem NH** [PASS · e6fc337462]: the same conclusion without Hausdorffness, when the algebra is simple.
- **Novelty:**
  - **PRIOR technique:** Stepanov 1997 Thm 4.4;
  - **PRIOR exchange-ring case:** arXiv:1912.11386;
  - **NEW (bounded):** the local-annihilation criterion as stated.
  - Before any "new criterion" framing, decide local annihilation versus Stepanov's condition (b).

## 4. The flagships: one dynamical dichotomy inside one family of Kazhdan groups

**Free groups** [PASS · 560decb046; `free-group-cantor-elementary-group-lef-iff-invariant-measure`, route landed 340b661d2f].
- **Setting:** `F_r` (`2 ≤ r < ∞`) acts minimally and topologically freely on the Cantor set, `R = LC(X,F_q)⋊F_r` is
  finitely generated, and `S_N = EL_N(R)/Z`, `N ≥ 3`.
- **Result:** every `S_N` is infinite, finitely generated, simple and Kazhdan, and:
  1. with an invariant probability measure, `S_N` is LEF for every `N`;
  2. otherwise there is `n` such that `S_N` has no nontrivial MF quotient for all `N ≥ 2n`.
- **Open:** the band `3 ≤ N < 2n`.
- **Inputs, all PASS:** simplicity; Kerr–Nowak (measure ⇒ residually finite); residually finite ⇒ matricial; the groupoid
  Tarski obstruction.
- **Novelty:** NEW (bounded) as a group-level dichotomy.

**Virtually free groups** [PASS · c341a29e49; `virtually-free-cantor-elementary-group-lef-iff-invariant-measure`]. The same
dichotomy holds, through `virtually-free-group-measure-actions-are-rf` [PASS · 97bf4bc468; credit Kerr–Nowak Lemma 5.1].
- **Firewall:** groups containing `ℤ²` have measure-carrying actions that are not residually finite
  (`z2-containing-groups-have-non-rf-measure-actions`, PASS · 97bf4bc468).
- **[OPEN]** `measure-rf-class-is-exactly-virtually-free-groups`.

**Why dynamics.** In characteristic `p`, "measure ⇒ matricial" contains Kaplansky stable finiteness (part 2 §8.2). For
virtually free groups, dynamics supplies the towers directly.

## 5. The two mirror objects

Same construction, `EL_N(LC(Y,F_q)⋊Γ)/Z`. Only the dynamics changes.

| | **Pestov's group** `S = EL_3(LC(X,F_q)⋊ℤ)/Z` | **the boundary group** `S_∂ = EL_N(LC(∂F_d,F_q)⋊F_d)/Z`, `d ≥ 2`, `N ≥ 3` |
|---|---|---|
| dynamics | invariant measure, return-word towers | paradoxical: `[∂F_d] = 2[∂F_d]` |
| infinite, f.g., simple, Kazhdan | PASS (Pestov reviews, S4, EJZ) | PASS · 171f0f7525, f15928d5c9 (finite `k` only, after scope repair) |
| LEF / MF | LEF, hence MF, sofic, hyperlinear | no nontrivial MF quotient [PASS · f15928d5c9] |
| soficity | sofic | **nonsofic** [PASS · c725d8a93f, fbaddd57b0] |
| permutation stability | unstable in every sense | **stable**, strictly and flexibly [PASS · fbaddd57b0] |
| `C*_r` | stably finite, unique trace; MF OPEN (as hard as `infinite-kazhdan-group-with-mf-reduced-cstar`) | separable, stably finite, unique trace, **not MF** [PASS · d166da76b2] |
| coarse geometry | not finitely presented, QI to no finitely presented group [PASS · 811353c0ef] | finite presentation OPEN |
| hyperlinear | yes | OPEN, famous either way |

**Nodes.**
- `boundary-action-elementary-simple-kazhdan-not-mf` and `boundary-action-simple-kazhdan-group-is-nonsofic`.
  - The nonsoficity rests on the explicit `d`-ary Leavitt family (`boundary-crossed-product-carries-leavitt-family`, PASS)
    and the axiom-clean Lean theorem `CompleteMatrixFamily.elementary_not_isSofic` (PASS · c725d8a93f).
  - It is subsumed by the older `halvable-corner-makes-projective-elementary-groups-nonsofic`.
- `purely-infinite-simple-projective-el-groups-stable-nonsofic`.
- `measure-free-steinberg-el-n-reduced-cstar-not-mf` (unique-trace justification extended to every countable `k` at review).

**Novelty.** `S_∂` is a **new example** (bounded), not the first nonsofic group. That was
`openai-leavitt-unit-nonsofic` (OpenAI, announced 2026-08-01). Credit Spielberg 1991 at C*-level.

**The stability face** [PASS · fbaddd57b0, likely folklore; `infinite-simple-group-permutation-stable-iff-nonsofic`]. For
infinite simple groups, permutation stability is equivalent to nonsoficity. So instability and soficity coincide at the
measure end, and stability and nonsoficity at the paradox end. Any stability-based nonsoficity argument needs a non-simple
input.

## 6. The sharpest one-line summary

Build `EL_N` over the Steinberg algebra of a minimal Cantor system:
- an invariant measure with towers gives an infinite simple Kazhdan LEF group;
- paradox gives an infinite simple Kazhdan group with no MF quotient;
- on the free group's boundary, that group is nonsofic and permutation stable.

For free and virtually free acting groups the two outcomes are exactly Tarski's alternative [PASS]. Rung (L) is closed
[PASS]. The open core is (Σ⇒), which is famous-level (non-linear-sofic groups), and (M⇐) in its correct form
(`mf = ∞` for simple stably finite rings). The Labbé ring over `F_2` is the concrete decider.
