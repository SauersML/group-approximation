# Boone–Higman for Ã₂ groups through Robertson–Steger 2-graph full groups

Lane `hl-bh-a2-boundary-hosts`, 2026-09-14, executes idea 2 of
`research/artifacts/ideas-bh-round2-2026-09-14.md`. **Unreviewed.**

## 0. Outcome

- **Verdict: a reduction, not a solution.** For the vertex-free type rotating Ã₂ groups
  of Robertson–Steger, Boone–Higman reduces to one geometric/combinatorial statement:
  primitivity and aperiodicity of the Robertson–Steger transition matrices. Two imports
  still need pins.
- **The one new theorem**, `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`:
  the full group of any primitive aperiodic finite 2-graph embeds in a finitely presented
  simple group of type `F_∞`. Its proof is complete modulo standard k-graph facts that
  are recalled, not pinned. It uses Li's F∞ theorem, Li's AH exact sequence, Matui's
  simplicity theorem and Matui's Künneth formula, all read at source.
- **Answer to the directive's question.** `D([[Γ ⋉ ∂_F X]])` is not shown finitely
  presented. The lane instead embeds the full group into a *different* full group,
  `[[G_{Λ^(n) × B_2}]]`, which is finitely presented and simple. The "no finite nucleus"
  obstruction in the idea artifact is bypassed, because Li's Garside-category method needs
  no nucleus.

## 1. Sources read at source (TeX on MSI, `/scratch.global/sauer354/hl-bh-a2-boundary-hosts/src/`)

- **Robertson–Steger, arXiv:1302.5593:**
  - Theorem `main2` (C(Ω)⋊Γ ≅ 𝒜 with `1_{Ω(p)} = φ(s_{w̄,w̄})`);
  - Proposition `M_1M_2` ((H0), (H1), (H3) for free type rotating actions with finitely
    many vertex orbits);
  - Theorem `H(3)` and Corollary `H(3)+` ((H2) only for `PGL_3(K)`, char 0).
- **X. Li, arXiv:2110.04505:** Theorem `thm:k-graphs` and its higher rank graph corollary
  (two loops of each colour at every vertex ⇒ `F_∞`); the definition of `Ω_∞` (l.1126).
- **X. Li, arXiv:2209.08087:** Corollary `cor:AHConj`, and l.804 (purely infinite minimal
  ⇒ comparison).
- **H. Matui, arXiv:1210.5800:**
  - Theorem `simple2`, Definition `pi`;
  - SFT groupoid homology (l.214–220);
  - the recoding in "Finiteness properties" (l.2716–2751), which needs Theorem `classify`.
- **H. Matui, arXiv:1512.01724:** Theorem `Kunneth`.
- **Lawson–Vdovina arXiv:1909.13254, Lawson–Sims–Vdovina arXiv:2010.08960:** grep of the
  TeX for "finitely presented" returned only right-ideal statements. These papers give
  simple commutator subgroups for k-monoid Thompson-like groups, not finite presentation.
- **D. Yang, arXiv:2105.02183:** the abstract proves `[L_Λ, L_Λ]` simple; finite
  presentation is not addressed (checked via the arXiv abstract page).

Not read: Kumjian–Pask math/9912002 (the fetched TeX did not contain the Robertson–Steger
discussion); Renault arXiv:0803.2284 (fetched, the normalizer theorem not yet located);
CMSZ I/II (Springer paywall redirect).

## 2. Routes tried and why they fail as stated

1. **Li's corollary directly on Λ_Γ.** It needs `#vΛ^{ε_j}v >= 2`. Robertson–Steger words
   of shape `ε_j` are pairs of tiles with `M_j = 1`, so there is at most one loop per colour
   per vertex. The hypothesis fails.
2. **Matui's reduction to canonical form.** Matui replaces `G|Y` by `G̃|Ỹ` for a graph
   whose matrix has all diagonal entries `>= 2`, using his classification of SFT
   groupoids (Theorem `classify`). No classification of 2-graph groupoids up to
   isomorphism is available, so this does not transfer.
3. **A larger Garside family `{0..N}^2`.** Li's verification of condition (t<d) for
   saturated sets `{0, ε_j}` still needs two loops of degree `ε_j`, so this does not help.

The route that works rescales degrees (loops become `M_j^n(a,a)`), which moves to the
subgroupoid `c^{-1}(nZ²)`. The degree skew product over `(Z/n)²` recovers an embedding of
the original full group.

## 3. Homology obstruction on main does not bite here

`derived-full-group-h2-filtered-by-mod-two-groupoid-homology` forbids finite presentation
only when mod-2 groupoid homology is infinite. After the product with `G_2`, all groupoid
homology vanishes (Künneth), so the obstruction is void for `[[G_{Λ^(n) × B_2}]]`, and
Li's AH sequence makes the group perfect.

## 4. Exact gaps

1. **Primitivity** (`robertson-steger-a2-two-graphs-are-primitive-and-aperiodic`). For
   exotic Ã₂ buildings neither irreducibility nor primitivity of `M_1`, `M_2` is proved.
   A finite certificate for one CMSZ exotic group, from its triangle presentation, would
   settle that group. A general proof needs mixing of `Γ ↷ Ω`.
2. **Embedding pins** (`a2-group-embeds-in-full-group-of-its-rs-two-graph`):
   - Kumjian–Pask identification of 𝒜 as `C*(Λ_Γ)` with its diagonal;
   - Renault's normalizer theorem;
   - topological freeness of `Γ ↷ Ω`.
3. **Standard k-graph facts** (`finite-k-graph-boundary-groupoid-standard-facts`): Li's
   model = Kumjian–Pask groupoid, products, Cantor unit space, aperiodic ⇒ effective.

## 5. Nodes landed

- Claims:
  - `li-finite-k-graph-full-groups-are-f-infinity`,
    `li-ah-exact-sequence-for-minimal-comparison-groupoids`,
    `matui-purely-infinite-minimal-full-groups-have-simple-d`,
    `matui-groupoid-homology-kunneth-and-full-shift-vanishing`,
    `robertson-steger-a2-boundary-algebras-are-rank-two-ck` (imports, with citation routes);
  - `finite-k-graph-boundary-groupoid-standard-facts` (OPEN);
  - `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple` (claim + proof route);
  - `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` (OPEN);
  - `a2-group-embeds-in-full-group-of-its-rs-two-graph` (OPEN);
  - `vertex-free-type-rotating-a2-groups-satisfy-boone-higman` (OPEN).
- Route: `a2-boone-higman-via-rs-two-graph-full-groups`.
