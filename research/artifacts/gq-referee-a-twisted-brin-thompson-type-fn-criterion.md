# Referee report (gq-referee-a, proof-gap lens): the twisted Brin–Thompson type F_n criterion, and Stein intervals as grid spheres

**Reviewed** (lane bh-typeA-universal, 4292385f3, marked high priority), read on origin/main:
- `twisted-brin-thompson-type-fn-criterion`, with route `twisted-bt-type-fn-interval-filtration-proof`;
- the key lemma `stein-complex-elementary-intervals-are-grid-spheres`, with route `stein-interval-grid-sphere-proof`.

Sources read at the scratch copies:
- **BZ**, `gq/src/bh-free-17/bz22/twisted_Brin_Thompson.tex`:
  - elementary bricks, partitions and forests (l.588–630);
  - `prop:JoinForests` (l.601–611), `prop:cible` (l.647–670);
  - `lem:vtx_stab`, `lem:stab_spectrum`, `prop:stabs` and `prop:cocpt` (l.686–735);
  - the whole of §7, from `lem:VE_conn` to `prop:E_hi_conn` (l.741–870).
- **FFWZ**, `gq/src/bh-typeA-universal/ffwz-2603.24687.txt`: Definition 4.7, Proposition 4.8 and the remark after it
  (l.884–927).

**Verdict: PASS for both.**
- I found no gap. There are six nits.
- Because the node claims Belk–Zaremsky Conjecture H, which FFWZ v2 record as open, I recommend three further steps
  before the claim is used downstream:
  - referee b checks the citation and priority facts: Cameron's monotonicity, Brown's `FP_n + F_2 ⇒ F_n`, and FFWZ
    Corollary 4.18;
  - a second, independent proof-gap pass;
  - a check against the authors' later work.

## Step 1 of the route: connectivity, and whether FFWZ 4.8(ii) needs more than faithfulness (the author asked)
- **Nothing beyond faithfulness is used.** FFWZ prove 4.8(ii) from BZ `prop:E_hi_conn` plus discrete Morse theory.
- **`E_m` depends on no hypothesis on `G`.**
  - `lem:VE_conn` is a matching-complex nerve argument.
  - `lem:desc_merge_link`, `lem:some_small` and `lem:all_big` are purely combinatorial.
  - None of them uses any finiteness property or the orbit structure of `G ↷ S`.
- **The rest.**
  - `prop:cible`, contractibility of `X`, uses only the directedness of intervals.
  - Faithfulness enters only through the standing construction of `P`.
  - Oligomorphy is used only in `prop:cocpt`, which this route does not use.
- **So the sublevel sets are highly connected.** Descending links of rank `> M` are `(n−1)`-connected, so each
  `X_m`, `m ≥ M`, is `(n−1)`-connected. ✓

## Step 0: extension closure of n-finite complexes (the author asked about this)
- **(a).** A shifted partial resolution has `H_e = M` and is exact in between. For `e = n` only `FP_0` is needed, and
  for `e > n`, `P = 0`. ✓
- **(d).**
  - `d(ατ) = −dλd = −(ατ)d`, so `τ : Q⁻ → K` is a chain map.
  - The cone `C` of `φ` has `H_i(C) = 0` for `i ≤ n`, from the long exact sequence.
  - A chain map from the bounded free `Q⁻`, in degrees `−1..n−1`, to `C` is null-homotopic, by building `h` upward
    from the bottom degree; each step uses `H_i(C) = 0` for `i ≤ n−1`.
  - The triangle then gives `τ ≃ φε`.
  - `P ⊕_ε Q` is a complex, because `dε + εd = 0`.
  - `dΦ − Φd = α(τ − (ds − sd) − φε) = 0`.
  - `Φ` restricts to `αφ` on `P` and induces `ψ` on `Q`.
  - The five lemma at `i < n` uses: surjectivity on `H_(i+1)` of the quotient, isomorphisms on `H_i`, and
    injectivity on `H_(i−1)`. The four lemma handles `i = n`. ✓
- **(b), (c), (e).** The bounded free witness is homotopy-projective. At `(e)`, a witness for `Z` is a partial free
  resolution of length `n`. ✓

## Step 2: the quotient splits over intervals (the author asked about this)
- **Which simplices are in `F_d`.** A simplex lies in `F_d` iff its min–max interval has length `≤ d`. That interval
  is elementary, and every `[a,b] ⊇ [v_0,v_k]` has at least its length.
- **Every point of `[v, w]` is elementary over `v`.** A dyadic brick that is a union of elementary bricks has
  `ψ(s) ∈ {0, 1, ∅}` (N4).
- **The differential in the quotient.**
  - The faces that drop the min or the max land in shorter intervals, so they vanish in the quotient.
  - The other faces keep `I`.
  - The simplices of `|I|` missing `v` or `w` are exactly those of `|[v,w)| ∪ |(v,w]|`.
- **The decomposition.**
  - So `C_*(F_d)/C_*(F_(d−1)) = ⊕_I C_*(|I|, ∂I)`.
  - The order-preserving action fixes chains pointwise, so there are no orientation signs.
  - Grouping into orbits gives `⊕ Ind_(Γ_I)^Γ`. ✓

## The key lemma: Quillen fibers, atoms and joins (the author asked about this)
- **Atoms.** `z_i^s ≤ w` iff every elementary brick of `π_f` in cube `i` has `ψ(s) ≠ ∅`, iff `s ∈ SSpec(f_i)`.
  - Every `z ∈ Q` lies above the atom given by the root split of a nontrivial tree of `z`.
  - `A ≠ ∅`, because the root colour of a nontrivial `f_i` lies in `SSpec(f_i)`. ✓
- **Joins.** `z_U` is the full split of each cube `i` in the colours `U_i`. It is the least common refinement in the
  partition lattice of `prop:JoinForests`, and it lies below `w`. So `z ≥ z_U ⟺ α(z) ⊇ U`. ✓
- **The grid case.** Elementary bricks cut in every colour of `Spec(f_i)` are exactly the full assignments, so
  `π_f` is the full grid and `z_A = w`.
  - For `∅ ≠ U ⊊ A`, `z_U ∈ Q`.
  - The fibres `{z ≥ z_U}` are cones.
  - Quillen's Theorem A gives `|Q| ≃ |B°| ≅ ∂Δ^(|A|−1)`, where `|A| = Σ|Spec(f_i)| = e`. ✓
- **The non-grid case.** A brick is cut in a colour outside `SSpec`, so `z_A < w`. Then `B` has a maximum, so `|Q|`
  is contractible. ✓
- **The cases `e = 1` and `(x_b ⊕ x_b)x_r`.** Both check: `(v,w) = ∅`, and six elements in two contractible
  components, respectively.
- **Agreement with BZ.** The dichotomy agrees with BZ's nerve computation in `lem:all_big`: a full simplex, or its
  boundary. ✓

## Steps 3–5
- **Step 3.** A complex with homology in one degree is quasi-isomorphic to `H_e[e]`, via the truncation zigzag (N2).
  - Grid orbits with `e ≤ n` give `Ind Z_χ[e]`.
  - Grid orbits with `e > n`, and all non-grid intervals, have `H_i = 0` for `i ≤ n`. ✓
- **Step 4: grid-interval stabilizers are `FP_(n−e)` (the author asked about this).**
  - `prop:stabs`, applied to the edge `v < w`, gives `Γ_I ≈ ∏ Stab_G(C_i)`, with setwise stabilizers. These are
    commensurable with pointwise ones.
  - Since `|C_i| ≤ e`, each factor is `FP_(n−|C_i|) ⊆ FP_(n−e)` when `|C_i| < n`. When `|C_i| = n`, then `e ≥ n` and
    nothing is needed (N1).
  - `Z_χ`: `N = ker χ` is `FP_(n−e)`, so `Z[Γ_I/N]` is `FP_(n−e)` over `ZΓ_I`. The truncated periodic resolution of
    `Z_χ` over `Z[C_2]`, with dimension shifting, gives `FP_(n−e)`, and induction preserves it. ✓
- **Step 5: the orbit count (the author asked about this).**
  - `Γ` is transitive on each rank, with stabilizer `G ≀ Σ_r`.
  - Grid tops over `[id_r]` correspond to tuples `(C_i)`. Twists carry full `C`-splits to full `γC`-splits (the
    Relations lemma), and permutations permute roots.
  - So the orbits correspond to `G ≀ Σ_r`-orbits of tuples, that is, to multisets of `G`-orbits of subsets of size at
    most `n`. There are finitely many, since `S^k ↪ S^n` injects orbits and there are finitely many ranks `r ≤ m`. ✓
- **Steps 6–7.**
  - `C_*(F_0) = ⊕_(r≤m) Ind_(G≀Σ_r) Z` is n-finite, and induction on `d` with (d) and (e) gives `FP_n`.
  - `(A_n)` with `n ≥ 2` implies Zaremsky's type (A), hence finite presentation, hence `F_n`. ✓
- **Item 3 (BZ's form).** Cameron's monotonicity gives finitely many orbits on `k`-subsets for `k ≤ n`, hence on
  `S^n`. This is correct as reasoning; the theorem itself is cited.

## Nits
- **N1 (Step 4).** When `|C_i| = n`, `(HA_n)` says nothing about `Stab_G(C_i)`. Say that then `e ≥ n`, so only `FP_0`
  is required, or nothing at all.
- **N2 (Step 3).** Name the zigzag: `K ← τ_(≥e)K → H_e[e]`. It is valid over any ring when the homology is
  concentrated in degree `e`.
- **N3 (Step 0(d)).** Record the sign convention: `d_(Q⁻) = −d_Q`, and the homotopy reads `τ − φε = d_Ks − sd_Q`.
- **N4 (Step 2).** Give BZ's parenthetical "and hence `v_i ⪯ v_j`" its one-line reason: coarsenings of elementary
  dyadic partitions are elementary.
- **N5 (Step 5).** Cite `lem:Relations`(7) for "a twist carries the full `C`-split to the full `γC`-split". The
  first half of `lem:stab_spectrum` gives only the pointwise-fixing direction.
- **N6 (key lemma, Step 1).** Say that every `u ∈ [v,w]` is represented by a forest, since `v = [id_q] ≤ u`. That is
  what lets the interval be read inside the partition lattice `F_q`.
