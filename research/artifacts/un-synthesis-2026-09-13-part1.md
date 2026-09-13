# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 1 of 3

Lane `un-synthesis`, 2026-09-13, refresh 2 (main tip 938ae27b49). This is the single readable account of the UN
swarm's theory. It proves nothing new. Every statement names its node and carries a status taken from the verifier
artifacts; no status is upgraded here.

- **Review landings used:**
  - `un-review-2026-09-13` part1 171f0f7525, part2 638d4941b5, part3 f15928d5c9, part4 d60f405998, part5 7c7fdace42,
    part6 c725d8a93f, part7 e6fc337462;
  - `un-review-measure` part1/2 10083fd646, part3 72ff092a72;
  - `un-review3` part1 2ba472b59d, part2 fbaddd57b0, part3 560decb046.
- **Novelty verdicts used:** `un-novelty` part1/2 (514b76e752, cb71b181f6).

**Status tags.**
- **[PASS · sha]:** re-derived by an independent verifier; the sha is the review landing.
- **[unreviewed]:** established on main by a complete route, not yet re-derived.
- **[import]:** a literature theorem quoted verbatim.
- **[printed]:** a theorem of `non_mf_groups_exist.tex` (line given).
- **[OPEN]:** an open claim.
- **Novelty tags:** NEW (bounded), FOLKLORE, PRIOR.

Part 2: the two mechanisms, radicals, spectra, traces, coarse and unit-group faces. Part 3: complexity, continua,
characteristic dependence, families, examples, the open middle, ledger, credits.

## 0. The thesis: the approximation type of a Kazhdan elementary group mirrors the type of its ring

**Root** `kazhdan-elementary-approximation-type-mirrors-ring-type` [OPEN]. Let `R` be a countable simple unital ring.
For finitely generated `R`, every `EL_N(R)` (`N ≥ 3`) is Kazhdan (EJZ [import]). Three rungs:

| rung | ring type | group type | ⇐ (ring ⇒ group) | ⇒ (group ⇒ ring) |
|---|---|---|---|---|
| (L) | exactly matricial: unital embedding in `∏_ω M_(d_k)(F_k)` | `EL_N(R)` LEF for all `N` | PASS · 2ba472b59d | PASS · 560decb046 (ranks `N ≥ 4`) |
| (Σ) | unital rank model over `k` (centre `k`, `k` finite) | `EL_N(R)/scalars` `k`-linear sofic for all `N` | PASS · 2ba472b59d | OPEN |
| (M) | stably finite ⟺ `[R]` not paradoxical in `V(R)` | `EL_N(R)` operator MF for all `N` | ⇐ OPEN | ⇒ PASS · 2ba472b59d + 638d4941b5 |

- **Node names.**
  - (L⇐) `exactly-matricial-rings-have-lef-general-linear-groups`.
  - (L⇒) `lef-el-groups-force-exactly-matricial-simple-ring`, route `lef-el-groups-matricial-via-lef-ring`, owner
    un-lef-converse de117129bd.
  - (Σ⇐) `rank-modelled-simple-rings-give-linear-sofic-projective-el`; (Σ⇒) `linear-sofic-el-groups-force-rank-model`.
  - (M⇒) `mf-elementary-groups-force-stably-finite-simple-rings` with `simple-ring-stably-finite-iff-unit-not-paradoxical`;
    (M⇐) `stably-finite-simple-rings-have-mf-elementary-groups`.
- **Rung (L) is closed for simple rings** [PASS · 560decb046]. For countable simple `R`, the following are equivalent:
  - `EL_N(R)` is LEF for one `N ≥ 4`;
  - `R` is a LEF ring (`lef-elementary-groups-force-lef-rings`);
  - `R` embeds unitally in a matrix ultraproduct over finite fields (`simple-lef-rings-are-exactly-matricial`);
  - `GL_M(R)` and `EL_M(R)` are LEF for every `M`.

  The (⇒) proof uses the finitely presented Steinberg cover `St_N(Z⟨W⟩)` (import
  `steinberg-finite-presentation-and-kazhdan-theorem`, route `steinberg-finiteness-kazhdan-citation`) to extract a
  finite level ideal. Rank 3 alone is not covered. Review display note: the target's title is still phrased as a question.
- **The root stays OPEN.** Its ladder route `kazhdan-approximation-ladder-from-three-converses` requires (Σ⇒) and (M⇐),
  both open. A counterexample to either would itself be a new object.

**What the root unifies.**
- Pestov 9.1 is (L⇐) at `LC(X,F_q)⋊ℤ`.
- The non-MF paper's Leavitt theorem (tex Cor l.1016) is (M⇒) at `L_k(1,2)`.
- Both rings are Steinberg algebras of minimal effective ample groupoids (§2).
- Their elementary groups are simple modulo centre by one theorem (§3), so only the ring type decides the approximation
  type.

## 1. The two calibrating results

- **Non-MF paper.**
  - **[printed l.918]** Let `R` be countable unital with `ts = 1` and `R(1−st)R = R`. Then for `n ≥ 2` every homomorphism
    from `EL_n(R)` to an MF group is trivial. **[printed l.1016]** This covers simple rings that are not directly finite,
    e.g. `L_k(1,m)`.
  - **[printed l.1038]** `C*_r(EL_n R)` is stably finite and not MF.
  - **[printed l.1218]** For purely infinite simple `R`, `Rad_MF(GL_n R) = [GL_n R, GL_n R]`, with quotient `K_1(R)`.
  - **[printed l.1349]** Not MF ⇒ the canonical trace is not quasidiagonal.
- **Pestov 9.1** [PASS twice, `ex-review-groups-2026-09-12-part1.md`, `ex-pestov91-second-review-2026-09-13.md`; Lean +
  Comparator]. For an infinite minimal subshift `X`, `LC(X,F_q)⋊ℤ` embeds in `∏_ω M_N(F_q)` by return-word towers, and
  `S = EL_3(LC(X,F_q)⋊ℤ)/Z` is infinite, simple, Kazhdan and LEF.

## 2. The dictionary

- **Leavitt algebras** [import, PASS · 2ba472b59d, `leavitt-path-algebras-are-steinberg-algebras`, Clark–Sims 1311.3701
  Ex 3.2]. `L_k(1,2) = A_k(𝒢_2)` for the Cuntz groupoid.
- **Crossed products** [PASS · 2ba472b59d; **PRIOR**: Beuter–Gonçalves, J. Algebra 497 (2018); citation route added;
  `crossed-products-are-transformation-steinberg-algebras`]. `LC(X,k)⋊Γ = A_k(X⋊Γ)`.
- **Simplicity of the algebra** [import, PASS · 171f0f7525]. For Hausdorff ample `𝒢`, `A_k(𝒢)` is simple ⟺ `𝒢` is
  minimal and effective (Steinberg 1408.6014; Clark–Edie-Michell 1403.4684).
  - Non-Hausdorff case [import, PASS · e6fc337462, `cepss-nonhausdorff-steinberg-simplicity`]: add "no nonzero singular
    element" (Clark–Exel–Pardo–Sims–Starling 1806.04362).
- **The bridge `ι : S(𝒢) → V(A_k(𝒢))`, `[U] ↦ [1_U R]`** [PASS · f15928d5c9, item B]. `S(𝒢)` is the type semigroup and
  does not involve `k`. So groupoid paradox gives ring paradox over every field at once.
  - Whether `ι` reflects paradox is [OPEN] `type-semigroup-reflects-paradox-of-steinberg-algebra`, Kaplansky-hard (§8
    of part 2).

## 3. Uniform simplicity

**Theorem S4** [PASS · 171f0f7525; `steinberg-elementary-groups-are-simple-mod-centre`]. Let `k` be a field and `𝒢` a
Hausdorff ample groupoid with compact infinite unit space, minimal and effective. Put `R = A_k(𝒢)` and `n ≥ 3`.
- Every normal subgroup of `EL_n(R)` is central or everything, and `Z ⊆ k^× I_n`.
- `EL_n(R)/Z` is infinite and simple.
- When `k` is finite and `R` is finitely generated, it is finitely generated and Kazhdan.

**Three ingredients, all PASS · 171f0f7525.**
- `A_k(𝒢)` has local annihilation (the Lean predicate `LocalAnnihilation` verbatim).
- The centre is `k·1`.
- The Lean criterion `Pestov91.isSimpleGroup_elementaryGroup_quotient_center`: a simple ring with local annihilation has
  `EL_n/Z` simple. It was written by the Pestov formalization swarm.

**Without Hausdorffness** [PASS · e6fc337462; `ample-steinberg-el-simple-mod-centre-without-hausdorff`, Theorem NH].
The same conclusion holds whenever `A_k(𝒢)` is simple and the unit space is compact, infinite and Hausdorff.

**Novelty** (un-novelty part2 §1).
- **Method PRIOR:** Stepanov 1997 (Zap. POMI 236), Thm 4.4 with Lemmas 4.1 and 4.3 — standard normal structure from linear
  dependence conditions, via zero-divisor extraction.
- **Exchange-ring case PRIOR:** arXiv:1912.11386.
- **NEW (bounded):** the local-annihilation criterion as stated, and its Steinberg-algebra application. Before any
  "new criterion" framing, decide whether local annihilation implies Stepanov's condition (b).

**Reading.** Simplicity, (T) and scalar centres hold uniformly across the ladder. The Pestov group and the Leavitt groups
are both instances, so simplicity is not what separates them.

## 4. The flagship: one dynamical dichotomy inside one family of Kazhdan groups

**Flagship** `free-group-cantor-elementary-group-lef-iff-invariant-measure` [PASS · 560decb046, un-review3 part3 §1;
route `free-group-cantor-el-lef-iff-invariant-measure-proof`, landed 340b661d2f]. Owner review note: the route should
also require `elementary-group-fg-from-fg-coefficient-ring`, which is established and cited in the body.

**Setting.**
- `F_r` (`2 ≤ r < ∞`) acts minimally and topologically freely on the Cantor set `X`.
- `q` is a prime power, and `R = LC(X,F_q)⋊F_r` is finitely generated as a ring (e.g. expansive actions).
- For `N ≥ 3`, `S_N = EL_N(R)/Z`.

**Statement.** Every `S_N` is an infinite, finitely generated, simple Kazhdan group, and:
1. if `X` carries an `F_r`-invariant probability measure, `S_N` is LEF for every `N ≥ 3`;
2. otherwise there is `n` such that every homomorphism from `S_N` to an MF group is trivial for all `N ≥ 2n`, so those
   `S_N` are neither MF nor LEF.

Hence `S_N` is LEF in every rank iff an invariant measure exists. The band `3 ≤ N < 2n` in case 2 is [OPEN] (part 3 §16).

**Inputs, each [PASS]:**
- simplicity, S4 (171f0f7525);
- dictionary (2ba472b59d);
- measure ⟹ residually finite action (Kerr–Nowak Thm 5.2, primary source read; 10083fd646);
- residually finite ⟹ matricial crossed product (10083fd646);
- no measure ⟹ `2n[1] ≤ n[1]` ⟹ no MF quotient from rank `2n` (f15928d5c9);
- EJZ [import].

**Novelty:** NEW (bounded) as a group-level dichotomy (un-novelty part2 §2).

**Why free groups.** In characteristic `p` "measure ⇒ matricial" contains Kaplansky's stable finiteness conjecture (part
2 §8). For free groups dynamics bypasses it: measure ⟺ residually finite action, which supplies towers directly. Beyond
free groups see part 2 §8.4.

## 5. The two mirror objects

Same construction, `EL_N(LC(Y,F_q)⋊Γ)/Z`. Only the dynamics changes.

| | **Pestov's group** `S = EL_3(LC(X,F_q)⋊ℤ)/Z`, `X` minimal subshift | **the boundary group** `S_∂ = EL_N(LC(∂F_d,F_q)⋊F_d)/Z`, `d ≥ 2`, `N ≥ 3` |
|---|---|---|
| dynamics | invariant measure, return-word towers | paradoxical: `[∂F_d] = 2[∂F_d]` |
| infinite, f.g., simple | PASS (Pestov reviews; S4) | PASS · 171f0f7525 |
| property (T) | PASS (EJZ) | PASS · f15928d5c9, after a scope repair: `k` must be finite (owner fix c66fcabd05) |
| LEF / MF | LEF, hence MF, sofic, hyperlinear | no nontrivial MF quotient [PASS · f15928d5c9] |
| soficity | sofic | **nonsofic** [PASS · c725d8a93f and fbaddd57b0] |
| permutation stability | unstable in every sense | **stable**, strictly and flexibly [PASS · fbaddd57b0] |
| `C*_r` | stably finite, unique trace; MF OPEN (as hard as `infinite-kazhdan-group-with-mf-reduced-cstar`) | separable, stably finite, unique trace, not MF [unreviewed] |
| coarse geometry | not finitely presented, QI to no finitely presented group [unreviewed] | finite presentation OPEN |
| hyperlinear | yes | OPEN, famous either way |

**The boundary group's nodes.**
- `boundary-action-elementary-simple-kazhdan-not-mf` (title case `N = 3`, `F_2`, `k = F_2`).
- `boundary-action-simple-kazhdan-group-is-nonsofic`: over finite `k`, every `EL_N(R_∂)/C` contains `EL_N(R_∂)` and is
  nonsofic.
  - Inputs: the explicit unital `d`-ary Leavitt family in `R_∂` (`boundary-crossed-product-carries-leavitt-family`, PASS),
    and the axiom-clean Lean theorem `CompleteMatrixFamily.elementary_not_isSofic` (`d-ary-leavitt-groups-nonsofic-over-finite-fields`,
    PASS · c725d8a93f, probe GREEN).
  - Subsumed by the established `halvable-corner-makes-projective-elementary-groups-nonsofic`. The new content is the
    explicit boundary family and the mirror role.
- Stability: `purely-infinite-simple-projective-el-groups-stable-nonsofic` [PASS · fbaddd57b0].
- Reduced side: `measure-free-steinberg-el-n-reduced-cstar-not-mf` [unreviewed].
- Hyperlinearity: [OPEN] `boundary-action-simple-kazhdan-group-is-hyperlinear`.

**Novelty and credit.**
- Nonsofic groups already exist: `openai-leavitt-unit-nonsofic` (OpenAI, announced 2026-08-01) proves `L_(F_2)(1,2)^×`
  nonsofic, answering Weiss's question.
- So `S_∂` is a **new example** (bounded): a nonsofic group that is also infinite, finitely generated, simple and
  Kazhdan with no MF quotient, as the paradoxical mirror of Pestov's group. It is not the first nonsofic group.
- Credit the OpenAI theorem for the mechanism, and Spielberg 1991 for the C*-level Cuntz–Krieger presentation of
  `C(∂F_n)⋊F_n`.

**The stability face** [PASS · fbaddd57b0, "likely folklore"; `infinite-simple-group-permutation-stable-iff-nonsofic`].
For an infinite simple group, strict and flexible permutation stability are each equivalent to nonsoficity.
- Reason: the limit kernel of an almost action is normal, hence `1` or everything.
- On the ladder, instability and soficity coincide on the measure end, and stability and nonsoficity on the paradox end.
- Firewall: stability of a simple group carries no information beyond soficity, so any stability-based nonsoficity
  argument needs a non-simple input.

## 6. The sharpest one-line summary

Build `EL_N` over the Steinberg algebra of a minimal Cantor system:
- an invariant measure with towers gives an infinite simple Kazhdan LEF group;
- paradox gives an infinite simple Kazhdan group with no MF quotient;
- for the free group on its boundary, that group is nonsofic and permutation stable.

For free-group systems the two outcomes are exactly the two sides of Tarski's alternative [PASS · 560decb046]. In
general the ring-level ladder (L) is closed [PASS], while (Σ⇒) and (M⇐) are the program's open converses.
