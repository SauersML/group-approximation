# UN review (un-verify-open), part 2: un-reduced-cstar, un-full-groups-bridge, un-low-rank-band

Lane `un-verify-open`, 2026-09-13. Same method and legend as part 1. Sources read from PDFs downloaded to
`un/lanes/un-verify-open/lit/`: Matui arXiv:1210.5800, Ara–Goodearl arXiv:1004.4979. The manuscript is
`non_mf_groups_exist.tex` at main's tip.

## 1. un-reduced-cstar (3a56e40cf8)

**Quote checks.**
- tex Lemma `prop:mf-residual-calculus` (l.363), verbatim: "Let $A$ be a unital $C^*$-algebra and let
  $\pi\colon G\to\U(A)$ be an injective group homomorphism. If $A$ embeds in a norm matrix corona, then $G$ is MF\@.
  In particular, this applies to the canonical group homomorphisms into $\U(C^*_{\max}(G))$ and
  $\U(C^*_{\mathrm r}(G))$." Matches the lane's quote.
- `bkko-reduced-traces-concentrate-on-amenable-radical`: established literature import.
- Magee–de la Salle Definition 1.2 (PMF), as quoted in `mf-kazhdan-cstar-literature-status-2026-09-12.md`: matches the
  node.
- Inputs already reviewed: `no-invariant-measure-steinberg-elementary-no-mf-quotient` (PASS, un-verify part 3);
  `boundary-action-elementary-simple-kazhdan-not-mf` (PASS after scope repair: f.g. and (T) only for finite `k`).

**Subsumption scan.** Claim titles containing "reduced" / `C*_r` / "cstar" together with MF, untruncated (≈27 hits).
None states the Steinberg measure-free theorem. Related but distinct:
- the `SL_4(Z)` reduced non-MF nodes (Magee–de la Salle fixed vectors);
- the Hilbert-hotel reduced black-hole nodes (one Leavitt group);
- `Reduced MF makes every element outside the amenable radical tracially visible`, which is the content of the
  artifact's Remark 6, not a claim here.

### 1.1 `measure-free-steinberg-el-n-reduced-cstar-not-mf`: PASS (one justification repaired)
- Step 1: a homomorphism `Q → M` composed with `EL_N(R) ↠ Q` is trivial by the reviewed node, so `Q → M` is trivial,
  and `Q ≠ 1` is not MF.
- Step 2 is the lemma above with `G = Q`. Step 3: `Q` is countable, and the faithful canonical trace gives stable
  finiteness.
- **Corollary (unique trace of `C*_r(S_∂)`).** The route derives non-amenability from (T), which after the headline's
  scope repair needs finite `k`. The statement holds for every countable `k`:
  - `S_∂` is simple, so its amenable radical is trivial or everything;
  - the shift unit `u` spans `k[u] ≅ k[t]` (normal form), and `SL_2(k[t])` contains a free subgroup of rank 2 (for
    instance `SL_2(Z)` in characteristic 0, and Nagao's amalgam over `F_p[t]`);
  - that subgroup sits in the lower `2×2` block of `EL_N(R)` and meets the scalars trivially.
  So BKKO applies for every countable `k`. The review line records this.
- Necessity corollary: if no invariant measure, some `n` has `2n[1] ≤ n[1]`, so `C*_r` is not MF for all `N ≥ 2n`,
  hence MF only in finitely many ranks.
- Model tests: the Cuntz groupoid (`n = 1`) recovers tex Cor l.1038; a minimal `Z`-subshift is vacuous, as it should be.

### 1.2 `minimally-almost-periodic-groups-are-not-pmf`: PASS, folklore-level
- Item 1: `ρ_i(1 − g) = 0` while `‖λ(1 − g)‖ > 0`.
- Item 2: Malcev (f.g. linear groups are residually finite).
- Item 3: normal subgroups are central or everything (reviewed simplicity), with a finite centre for finite `k`, so
  there is no nontrivial finite quotient.

### 1.3 `ring-model-permutation-vectors-block-strong-convergence`: PASS
- **General firewall.** `‖V_i(h_K)‖ ≥ Re⟨V_i(h_K)ξ_i, ξ_i⟩ → 1`, while `λ_Γ|_(P_0)` is a multiple of `λ_(P_0)`, so
  `‖λ_Γ(h_K)‖ = ‖λ_(P_0)(h_K)‖ < 1` (Kesten). No subsequence converges strongly.
- **Invariant column.** A matrix `p` fixing `e_1` has first column `e_1`. Applying the unital `σ_i` entrywise gives first
  column `c_i`, so `σ_i(p)c_i = c_i` exactly. `ξ_i = δ_(c_i) − mean` lies in `ℓ²_0(F_i)` and is exactly invariant.
- **Orbit size.** `σ_i(e_21(r))c_i = (1, σ_i(r), 0, …)` gives at least `|σ_i(window)|` points.
- **Stabilizers.**
  - `diag(1, EL_(n−1)(R))` is infinite Kazhdan for `n ≥ 4`.
  - For Pestov's ring at `n = 3`, `SL_2(F_q[u])` in the lower block contains `F_2` (Nagao).
  - For `G/Z`, the lower block meets the scalars trivially.
- Credit to Magee–de la Salle's invariant-vector mechanism is present.

### 1.4 Open claim, route and display
- `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure` (OPEN): the display matches the artifact.
- Route `kazhdan-mf-reduced-from-measure-side-el-n` requires that open claim, so it does not fire.
- For `r = 1`, an infinite minimal subshift is free with an invariant measure (Krylov–Bogolyubov), and `R` is f.g., so
  the logic into `infinite-kazhdan-group-with-mf-reduced-cstar` is correct.

## 2. un-full-groups-bridge (8883ed4422, 21ed3e7571)

**Quote checks (Matui, arXiv:1210.5800 PDF).**
- p. after Remark 6.3, l.1250 of the text dump: "([34, Proposition 9.6]). This identification yields an isomorphism
  between" `V_(n,1)` and `[[G]]`.
- l.1466: "We call α ∈ [[G|Y ]] a transposition if there" exists a clopen `A` as in the node.
- Lemma 6.10 (the TeX label `Tgenerate`): "Suppose that (X, σ) is topologically mixing. Then [[G|Y ]]0 is generated by"
  the transpositions.
- §6.7.1 (full shifts): `H_0(G_(n,r)) ≅ Z_(n−1)`, `H_1(G_(n,r)) = 0`, abelianization `Z_(n−1) ⊗ Z_2`.

The import node's quotes match; its section numbers follow the TeX, and the PDF numbers are Lemma 6.10 and §6.7.1.

**Inputs present on main:** `full-group-units-embed-in-steinberg-algebras`, `abc-leavitt-path-k-theory-exact-sequence`,
`agp-purely-infinite-simple-k1-is-unit-abelianization`, `purely-infinite-unit-group-max-mf-quotient-is-k1`,
`leavitt-gl-equals-el-and-perfect-unit-group`, `sfts-without-finite-orbits-are-not-residually-finite-actions`, and
`simple-rings-with-local-matrix-models-are-matricial` (reviewed PASS).

**Subsumption scan.** Terms `locally residually finite|partial permutation matri|combinatorial (matricial )?model`, and
Higman–Thompson together with MF radical, untruncated. No older node states the LRF equivalence or the `V_d` parity
theorem. `virtually-free-crossed-product-matricial-iff-invariant-measure` and Ma's Theorem C import are
`distinct_from`-level relatives.

### 2.1 `lrf-cantor-actions-give-lef-full-and-elementary-groups`: PASS (domain wording repaired)
- **(i)⇒(ii'), multiplicativity.** `ψ_n(f u_g)ψ_n(f' u_h)δ_z = f(w) f'(β(h)z) δ_w` with `w = β(gh)z`. The product is
  `f·(f'∘α(g^(−1))) u_(gh)`, giving `f(w) f'(α(g^(−1))w) δ_w`. Then `β(g^(−1))w = β(h)z` (partial homomorphism on
  `F_n`), and `d(α(g^(−1))w, β(g^(−1))w) < ε_n`, with `f'` constant at scale `ε_n`.
- **Domain.** The artifact defines `ψ_n` by the formula only on supports in `S_n`, with "any additive extension" outside.
  A product of two window elements has support in `S_n^2`, so the formula must be used on supports in `F_n = S_n^3`,
  where `P_n` is defined. With that reading (clearly intended, and as in un-measure's reviewed Theorem A) the check
  holds. The review line records the domain.
- **Injectivity.** Lemma S plus simplicity.
- **Combinatorial.** Basic bisection units go to partial permutation matrices. Disjoint unions have disjoint row
  supports, and, for `ε_n` below a Lebesgue number, disjoint column supports.
- **(ii)⇒(i).**
  - (P2): an invertible ppm is a permutation matrix. (P1): an idempotent ppm is diagonal.
  - The clopen partition `E_n(U)` satisfies `β(g)E_n(U) = E_n(α(g)U)`.
  - Placement `ζ`: for `z ∈ E_n(U)`, `ζ(β(g)z)` lies in an atom meeting `α(g)U`, and both sets have diameter `< ε`. So
    `d(α(g)ζ(z), ζ(β(g)z)) < 2ε`. The node's "both lie in `α(g)U`" is loose; the bound `2ε` suffices.
- **(a).** Full bisection units map to permutations, so `[[α]] ↪ ∏_ω Sym`, which is LEF. **(b)** as in Theorem A.
- **Prop 3.1 / Cor 3.2.** `β(e_i)β(e_j) = β(e_i+e_j) = β(e_j)β(e_i)` inside `B_(3r)` gives a genuine action. The
  periodic-configuration argument is the cited node.

### 2.2 `leavitt-mf-quotients-see-thompson-vd-through-parity`: PASS (item 3 as flagged)
- **Lemma 2.1.** Under `R ≅ R^d`, `x ↦ (t_i x)`, left multiplication by `u` is `(t_i u s_j)`, and for a central scalar
  this is `λI_d`. `K_1` invariance gives `[λ] = [λ]^d`.
- **Lemma 2.2.** The block form `[[0,ψ^(−1)],[ψ,0]] ⊕ 1`. The identities
  `[[1,a],[0,1]][[1,0],[−a^(−1),1]][[1,a],[0,1]] = [[0,a],[−a^(−1),0]]` and `[[0,a],[−a^(−1),0]]·diag(−1,1) =
  [[0,a],[a^(−1),0]]` were recomputed. So the class is `[1 − 2·1_A] = ∏[1 − 2e_(w_i)] = [−1]^m`.
- **Items 1, 2, 4** follow from Matui's generation and the established unit-group MF quotient `(Q)`.
- **Item 3** additionally needs the canonical identification `K_1(L_k(1,d)) ≅ k^×/(k^×)^(d−1)` with `[λ] ↦ λ`. The node
  flags this, and it is consistent with tex Cor l.1297, which prints `K_1(R) ≅ k^×/(k^×)^(d−1)` through
  `GL_d(R) = EL_d(R)D_d(k)` (Khanh–Thanh).
- **Model test.** `d = 2`, `k = F_2`: `H` is perfect.

### 2.3 `matui-sft-full-groups-generated-by-transpositions`: PASS (import faithful)

### 2.4 `quantum-matricial-models-separate-full-groups-from-elementary` (OPEN): display checked
- The Attempts' restriction argument (a matricial model sends full bisection units into `∏_ω GL_N(F_q)`, so LEF of
  `EL_n` through a model gives LEF of `[[α]]`) is correct.

## 3. un-low-rank-band (e9a8f6bf70, 92fa30e814)

**Quote check (Ara–Goodearl, arXiv:1004.4979 PDF).**
- l.511–512 of the text dump: "(2) The monoids V(LK (m, n)), V(Am,n ), V(vAm,n v), and V(wAm,n w) are all of the form
  hx | mx = nxi, where the generator x corresponds to the classes [1], [w], [α1 α1∗ ], [w]".
- Intro l.25: "a universal isomorphism between the free modules of" ranks `m` and `n`.
- Both match the import node.

### 3.1 `ara-goodearl-leavitt-mn-monoid-is-one-relator`: PASS
- The consequence (IBN-m) holds: the congruence on `N` generated by `m ~ n` identifies `i, j` iff `i = j`, or
  `i, j ≥ m` with `i ≡ j (mod n−m)`.
- Left and right modules are exchanged by `Hom_R(−,R)`.

### 3.2 `leavitt-module-rank-iso-columns-are-not-completable`: PASS
- `R^N = ⊕_i x_i R` with `x_i R ≅ R` (since `y_i x_i = 1`), so the complement of `x_i R` is `≅ R^(M−1)`.
- Completion `x_i = g e_1` gives a second complement `≅ R^(N−1)`. Complements of one summand are isomorphic, so
  `R^(M−1) ≅ R^(N−1)` with minimum `m−1`, contradicting (IBN-m).
- Model tests re-checked (`L(1,2)`, `L(2,3)`, `L(3,4)`).

### 3.3 `module-iso-conjugates-of-el-are-stably-elementary`: PASS
- `A = diag(X,1)`, `B = diag(Y,1)`, `Ψ(h) = AhB`.
- `A E_(ic) r B = x_i r e_(c')^T = Σ_k E_(kc') x_ki r`, a product of commuting `e_(kc')(x_ki r)`; symmetrically for
  `e_(ci)`.
- `e_ij(r) = [e_ic(r), e_cj(1)]`, and `Ψ(diag(g,1)) = diag(XgY,1)`.
- Model test with `X = (s_1 s_2)`, `Y = (t_1; t_2)`: `XY = 1`, `YX = 1_2`.

### 3.4 Open claims and route
- `el3-leavitt-3-4-has-full-mf-radical`: `p(L(3,4)) = 3`, since `4x = 3x` while `3x ≤ 2x` fails in `⟨x | 3x = 4x⟩`. So
  the band is `{3, 4, 5}`, of which `N ≥ 4` is settled by `non-ibn-ring-el-n-full-mf-radical-above-module-rank` (PASS,
  un-verify part 4), leaving `N = 3`.
- Route `el3-leavitt-3-4-full-mf-radical-via-module-iso-image`: `φ∘Φ` on `EL_4` is trivial, and `ker φ` contains the
  normal closure. It requires the open part-1/part-2 claim, so it does not fire.
- `leavitt-3-4-module-iso-image-normally-generates-e3`: the dead-route computation
  `g(1 + e_1 w)g^(−1) = 1 + x_i r y_j` with `w e_1 = r y_j x_i = 0` was checked. The recalled Bass cancellation remark
  sits in Attempts only.

## 4. Ledger
| node | verdict |
|---|---|
| measure-free-steinberg-el-n-reduced-cstar-not-mf | PASS; unique-trace justification extended to every countable k |
| minimally-almost-periodic-groups-are-not-pmf | PASS; folklore-level |
| ring-model-permutation-vectors-block-strong-convergence | PASS |
| free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure (open) / kazhdan-mf-reduced-from-measure-side-el-n | display and wiring PASS |
| lrf-cantor-actions-give-lef-full-and-elementary-groups | PASS; domain of ψ_n is F_n = S_n^3 |
| leavitt-mf-quotients-see-thompson-vd-through-parity | PASS; item 3 rests on the K_1 identification (flagged, consistent with tex Cor l.1297) |
| matui-sft-full-groups-generated-by-transpositions | PASS |
| quantum-matricial-models-separate-full-groups-from-elementary (open) | display PASS |
| ara-goodearl-leavitt-mn-monoid-is-one-relator | PASS |
| leavitt-module-rank-iso-columns-are-not-completable | PASS |
| module-iso-conjugates-of-el-are-stably-elementary | PASS |
| el3-leavitt-3-4-has-full-mf-radical, leavitt-3-4-module-iso-image-normally-generates-e3 (open) / route | display and wiring PASS |
