# Referee report (gq-referee-c): twisted-brin-thompson-type-fn-criterion

- **Nodes** (version 329a4461c, lane `bh-typeA-universal`):
  - `research/twisted-brin-thompson-type-fn-criterion.md` and its route
    `twisted-bt-type-fn-interval-filtration-proof`;
  - `research/stein-complex-elementary-intervals-are-grid-spheres.md` and its route `stein-interval-grid-sphere-proof`.
- **Lens:** a second independent proof-gap pass, after `gq-referee-a` (16bd2d9b5). I re-derived every step. I also
  checked the Belk–Zaremsky inputs against the TeX on MSI (`gqsrc/bh-openq/2001.04579/twisted_Brin_Thompson.tex`,
  l.555–870) and FFWZ Proposition 4.8 against `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`, l.852–960.
- **Verdict: PASS** for the sufficiency proof (items 1–2), for item 4, and for the grid-sphere lemma. Item 3 and
  necessity rest on imports (Cameron 1976; FFWZ Corollary 4.18) that I did not re-read; that is referee b's lane.
  One claim in the "Lesson" paragraph is not supported as stated (§6). It is not part of the theorem.

## 1. Crux (iv): connectivity of X_m needs only faithfulness

FFWZ Prop 4.8(ii) (l.899–901) reads: "Assume G ↷ S is faithful … For all n ∈ N there exists M ∈ N such that for all
m ≥ M the complex SX^m_G is (n−1)-connected." FFWZ derive it from BZ Prop 7.9 and Bestvina–Brady.

At source, BZ `prop:E_hi_conn` gives the connectivity of the descending link `E_m` as at least
`min(ν(m/2)−2, log_2(m/2)−2)`, with `ν(k) = ⌊(k−2)/3⌋`. Its inputs are:
- `lem:VE_conn` (matching complexes);
- `lem:desc_merge_link`;
- `lem:some_small`;
- `lem:all_big`.

None of them uses an orbit or finiteness hypothesis on `G`. The bound tends to infinity with `m` independently of
`G ↷ S`. Rank is non-constant on edges, so `X_{m+1}` is `X_m` with cones attached over the descending links of the
rank-`(m+1)` vertices. Hence `X_m → X` is `n`-connected once every descending link above rank `m` is
`(n−1)`-connected, and then `X_m` is `(n−1)`-connected, since `X` is contractible (`prop:cible`). ✓ FFWZ's `SX_G`,
the flag complex on elementary edges, is BZ's `X`: a clique of pairwise ⪯-related vertices is a chain `v_0<…<v_k`
with `v_0 ⪯ v_k`, and conversely.

## 2. Crux (i): the interval filtration and the grid-sphere lemma

**Sub-intervals are elementary.** BZ assert "and hence v_i ⪯ v_j" without proof, so I checked it. In the partition
model of `prop:JoinForests`, a dyadic brick containing an elementary brick has `ψ'(s)` a prefix of
`ψ(s) ∈ {0,1,∅}`, so it is elementary. Rescaled to such a brick, each finer piece is cut at most once per
direction. ✓

**The filtration** (`F_d` = union of `|I|` over elementary intervals of length ≤ d).
- A simplex of `X_m` lies in `F_d \ F_{d−1}` exactly when its (min, max) interval has length `d`.
- A simplex of `|I|` lies in `F_{d−1}` exactly when it misses `v` or `w`.
- So `C(F_d)/C(F_{d−1}) = ⊕_I C(|I|, ∂I)` with `∂I = |[v,w)| ∪ |(v,w]|`, and grouping by orbits gives
  `⊕ Ind_{Γ_I}^Γ`.
- Γ acts by order-preserving maps, so stabilizers fix chains pointwise and the chain modules are permutation
  modules. ✓

**The grid-sphere lemma** (Quillen fiber lemma applied to `α(z) = {(i,s) : z_i^s ≤ z}`).
- Every `z ∈ (v,w)` lies above the atom of its first split. That atom is below `w` exactly when
  `s ∈ SSpec(f_i)`, as in BZ's proof of `lem:all_big`. So `α(z) ≠ ∅`.
- For `U ⊆ A`, `z_U` (the full grid of each cube `i` in `U_i`) is the least common refinement of its atoms. So
  each fiber `{z ≥ z_U}` has minimum `z_U`. That minimum lies in `(v,w)` for `U` proper and nonempty in the grid
  case, and for every nonempty `U` in the non-grid case, where `z_A < w`.
- Hence `|(v,w)|` is `≃ |B°| = S^(e−2)` in the grid case, and a cone otherwise.
- Relative homology: `|[v,w]|` is a cone and `∂I = Σ|(v,w)|`, so `H_k(|I|,∂I) = H̃_(k−2)(|(v,w)|)`. ✓
- I recomputed the four examples by hand. The full split `(x_b⊕x_b)x_r` has an open interval of six elements:
  two halvings and four three-brick partitions, forming two cones, so `≃ S^0`. The split `(x_b⊕id)x_r` gives one
  point. ✓
- `e = 1` gives `(v,w) = ∅` and `∂I = S^0`, so `H_1 = Z`. ✓
- The identification of `[v,w] ⊆ P_1` with `[[id_q],[f]] ⊆ F_q` is right multiplication by `h^(-1)`, as in BZ.

## 3. Crux (ii): stabilizers of grid intervals

BZ `prop:stabs` (l.703–719) is for exactly the chain `v_0 < v_k`: the stabilizer is commensurate with
`∏ Stab_G(Spec(f_i))`, through `lem:stab_spectrum`. For a grid tree, `Spec(f_i) = C_i` and `|C_i| ≤ e`.

**Under (HA_n) with e ≤ n.**
- `Stab_G(C_i)` is `FP_(n−|C_i|) ⊆ FP_(n−e)` when `|C_i| < n`.
- It is `FP_0`, which every group is, when `|C_i| = n`. This is N1.
- `G` is `FP_n`.
- Finite products and commensurability preserve `FP_k`. ✓

**Z_χ is FP_(n−e).** The route's argument (a resolution of `Z_χ` by the `FP_(n−e)` modules `Z[Γ_I/N]`, plus the
standard lemma that `A_j` of type `FP_(k−j)` gives `M` of type `FP_k`) is correct. A shorter route: the ring
automorphism `g ↦ χ(g)g` of `ZΓ_I` carries `Z` to `Z_χ` and free modules to free modules. Induction to `Γ`
preserves `FP_k`. ✓

## 4. Crux (iii): homological algebra (Step 0)

- **(a)** Shift a partial resolution. When `e = n`, only finite generation is used. ✓
- **(b), (c)** Standard; bounded complexes of free modules are K-projective. ✓
- **(d) Extensions.** I re-checked every identity.
  - `α(dτ) = −dλd = −α(τd)`, so `τ : Q⁻ → K` is a chain map.
  - `cone(φ)` has `H_i = 0` for `i ≤ n`. It uses surjectivity at `n` and injectivity at `n−1`.
  - `Q⁻` is free in degrees `−1..n−1`, so maps into the cone are null-homotopic.
  - The exact sequence `[Q⁻,P] → [Q⁻,K] → [Q⁻,C]` gives `ε, s` with `τ − φε = ds − sd`.
  - `D² = (dε + εd)q = 0`, since `ε` is a chain map on `Q⁻`.
  - `dΦ − ΦD = (dλ − λd − α(ds − sd) − αφε)q = 0`.
  - Five lemma for `i < n`, four lemma at `i = n`. ✓
- **(e)** `P → Z` exact in degrees `1..n−1` with `H_0 = Z` is a partial free resolution, which is `FP_n`. ✓

## 5. Steps 5–7

- **Orbit count (Step 5).** Γ is transitive on each rank (BZ `prop:cocpt`), and `Stab([id_r]) = G ≀ Σ_r` applies `g_i` to
  `C_i` and permutes the roots. So the orbits with `e ≤ n` correspond to multisets of `G`-orbits of subsets of
  total size `≤ n`. There are finitely many: the map `S^k ↪ S^n` that repeats the last coordinate is an injective
  equivariant map, so it injects orbits. ✓
- **Non-grid intervals, and grid intervals with e > n.** Infinitely many orbits are allowed here, because only the
  homology in degrees `≤ n` matters. ✓
- **Step 6.** `F_0` is `⊕_(r≤m) Z[Γ/(G≀Σ_r)]`, which is `n`-finite. Induct with (d). ✓
- **Step 7.** `(A_n)` with `n >= 2` gives Zaremsky's type (A):
  - `G` is `F_2`;
  - point stabilizers are `F_1`;
  - there are finitely many orbits on `S^2`.

  So `SV_G` is finitely presented, and `FP_n` together with finite presentation gives `F_n`. ✓

**Calibration.**
- At `n = 2` the hypotheses the proof actually uses are `G` `FP_2`, `Stab(s)` `FP_1`, 2-set stabilizers `FP_0`
  (vacuous) and orbits on `S^2`. That is Zaremsky's (A), up to FP versus F.
- At `n = 1` the proof uses exactly "G finitely generated with finitely many orbits".
- For every `n`, each hypothesis is used on precisely the intervals of the matching color count, and FFWZ's
  necessity shows none can be dropped.
- The proof never touches a simplex stabilizer of a long edge. That is exactly the obstruction FFWZ name at
  l.919–927.

## 6. Not verified; one overclaim

- **Wreath products.** The "Lesson" equivalence with `Z ≀_S G` (de Cornulier; Bartholdi–de Cornulier–Kochloukova)
  was not checked. I did not confirm the exact `k`-range in BCK's theorem.
- **The "iff" in the Lesson.** "H embeds in an F_n simple twisted Brin–Thompson group iff H embeds in an
  (A_n)-actor" is justified only in the ⇐ direction, since `G ≤ SV_G` and SV_G is simple (BZ).
  - For ⇒, `H ≤ SV_G` does not put `H` inside `G`.
  - Either restrict the sentence to ⇐, or add an argument that an `F_n` twisted Brin–Thompson group is itself
    contained in an `(A_n)`-actor.
