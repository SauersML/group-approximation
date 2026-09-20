---
rg: 2
id: brin-thompson-groups-nv-are-a-t-menable
kind: claim
title: "Every Brin-Thompson group nV (n >= 2) has the Haagerup property"
---

For every `n >= 2`, the Brin–Thompson group `nV` admits a proper conditionally
negative definite function, equivalently a metrically proper affine isometric
action on a Hilbert space. Since `nV <= mV` for `n <= m`, the claim for all `n`
is equivalent to the claim for arbitrarily large `n`.

This is the "yes" answer to the Haagerup part of Zaremsky Problem 2.7
(`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`).

## Attempts

- **Farley-type charts (dies for n >= 2).** For `V`, let `X` be the set of
  pairs `(U, φ)` with `U ⊆ C` clopen and `φ: C → U` a homeomorphism in the
  Thompson groupoid, `V` acting by `g·(U, φ) = (gU, g∘φ)`, and `A ⊆ X` the
  standard cylinder charts `ι_w(u) = wu`. Then `g∘ι_w` is standard exactly
  when `[w]` lies inside a leaf of the reduced domain tree of `g`, so
  `|gA Δ A|` is the number of internal nodes of the reduced domain and range
  trees: finite, and proper in `g`. This gives a-T-menability of `V`.
  The same construction for `nV` with standard brick charts is not
  commensurated: `g(x, y) = (x, y)` on `[0] x C` and `(x, s(y))` on `[1] x C`,
  with `s` swapping the first letter, is not canonical on any brick
  `C x [v]`, and there are infinitely many such bricks. Breaks in dimension
  `>= 2` are codimension-one, so every brick-like family is broken infinitely
  often.
- **Stein–Farley complex (dies).** The cube complex of expansions of `nV`
  (Fluch–Marschler–Witzel–Zaremsky) is not CAT(0) for `n >= 2`: splitting a
  piece in direction 1 and then both halves in direction 2 gives the same
  vertex as the other order, a 6-cycle in the 1-skeleton that no cube corner
  or pair of squares fills. So its 1-skeleton is not a median graph.
- **No cubical proof at all.** `2V` has a distortion element with
  `|f^n| = O(log^4 n)` and admits no proper action on any CAT(0) cube complex
  (Callard–Salo, arXiv:2208.00685). This supersedes the two route-specific
  obstructions above. A Haagerup proof must be non-cubical: measured walls with
  an invariant measure, or a direct proper cocycle. Any proper conditionally
  negative definite `ψ` grows at most like `O(log^8 n)` along `⟨f⟩`, since
  `√ψ` is subadditive.
- **Coupled objects fail too.** Diagonal-type curve charts
  `u ↦ (αu, βu)` couple the tails, so breaks happen only when both prefixes
  are short. But canonical maps shift the imbalance `|α| - |β|` by the
  piecewise cocycle `δ_x - δ_y`, so balanced curves are not commensurated. Every
  object tried breaks by codimension-one faces (uncoupled objects) or by
  anisotropic scaling (coupled objects).
- **Local similarities.** Hughes (arXiv:0804.0610) proves a-T-menability for
  locally finitely determined groups of local similarities of compact
  ultrametric spaces. Brick maps scale the coordinates by independent powers of
  2, so they are not similarities of the max ultrametric on `C^n`. The theorem
  does not apply as stated (paper not read in full).
- **Groupoid-generic proofs (dies; class-kill).** `nV ≤ [[G_2^n]]`, and `G_2^n` is
  ample, topologically amenable, minimal, essentially principal and purely infinite.
  `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` builds another groupoid
  with all these properties, `(M ⋊ Γ) × G_2` with `Γ = Z^3 ⋊ SL_3(Z)` acting freely,
  minimally and amenably on a Cantor set `M`. Its full group contains `Γ`.
  - **Invariant:** property (T) of `Γ`.
  - **Where every member dies:** the passage from groupoid hypotheses to a proper
    conditionally negative definite function on `[[𝒢]]`, which would restrict to a
    proper one on `Γ`.
  - **Consequence:** a Haagerup proof, or even a proof that Kazhdan subgroups are finite,
    must use structure beyond this class, such as the zipper, product-of-trees or
    local-similarity combinatorics of `G_2^n`, or expansivity. Matui's SFT theorem
    (`sft-topological-full-groups-have-the-haagerup-property`) uses such structure.
  - **Compact generation and expansivity are now calibrated (2026-09-17, e-nv-calibrate).**
    - `ample-groupoid-products-expansive-iff-factors-are` (established): products are
      compactly generated when the factors are, and expansive iff both factors are. `G_2`
      is expansive. So `(M ⋊ Γ) × G_2` is compactly generated for every action of a
      finitely generated `Γ`, and it is expansive iff `Γ ↷ M` is a subshift. For the host's
      `M` (inside `X' × Z`, with `X' ⊆ T^Γ` and `T` infinite) this is not settled.
    - `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` (established): let `Γ` be a
      Kazhdan `PGL_3(K)` lattice acting on its Robertson–Steger boundary `Ω`. This action is
      an amenable, minimal, expansive subshift on a Cantor set, with no invariant measure.
      Both `Γ × Ω` and `(Γ × Ω) × G_2` are compactly generated, expansive and minimal, and
      `Γ` sits in their full groups. The germ groupoid is expansive, minimal and effective,
      and also contains `Γ`.
    - **Killed in addition:** proofs using compact generation and/or expansivity together
      with amenability, minimality, no invariant measure and a simple nuclear purely
      infinite C\*-algebra. Also killed: expansivity with effectiveness. They die at the same
      step (restriction of `ψ` to `Γ`).
    - **Still not ruled out at groupoid level:** proofs using effectiveness, amenability and
      expansivity *together*. The free host above is not known to be expansive, and the
      Robertson–Steger action is not known to be topologically free. Its germ groupoid is
      not known to be amenable.
- **Calibration table (2026-09-17, e-nv-calibrate).** The worlds are:
  - W1 = `(M ⋊ Γ) × G_2`, `Γ = Z^3 ⋊ SL_3(Z)` (open on citations; free, compactly
    generated);
  - RS = the Robertson–Steger boundary groupoid above, or its product with `G_2`;
  - SFT = SFT full groups (Haagerup, Matui);
  - 1V = `V` (Haagerup, Farley).

  For each route or proposal, the world it cannot tell from `2V`:
  - **Groupoid-generic** (amenable, minimal, effective, purely infinite): W1.
  - **The same plus compact generation:** W1, which is compactly generated (proved).
  - **Expansivity-based** (amenable, minimal, expansive, no invariant measure, simple nuclear
    purely infinite): RS. Only effectiveness is left out.
  - **Word-system / Z²-cocycle proposals** (prefix replacements with shape offsets, AF
    kernels of the degree cocycle): RS
    (`rank-two-prefix-replacement-groups-contain-infinite-kazhdan`).
  - **Farley charts, Stein–Farley, any cubical or wall-space proof:** not a world question.
    They die for `2V` itself (Callard–Salo distortion).
  - **Triangular split R1/R2:** R2 is fibred over the coordinate tower `C^n → ... → C`,
    which exists only for product word systems. RS has no such tower, so this route is not
    refuted by any world above. R1 must still be non-cubical.
  - **Negative routes** (non-Haagerup of `2V` via a Kazhdan or relative-(T) subgroup, or
    Problem B failing for the fibres): every step must fail for SFT and 1V, which are
    Haagerup. A step that only uses rank-one expansive structure proves a false statement.
  - **Lodha's groups:** not used. Their Haagerup status is not recorded on the graph, so
    they calibrate nothing yet.

  **Which property of `2V` a positive proof must use.**
  - Not compact generation: W1 and RS have it.
  - Not expansivity alone: RS has it.
  - Not distortion: it only constrains R1 (non-cubical).
  - What is left is the **product structure**: tiles `A = A_1 × A_2`, commuting row and
    column matrices `J ⊗ I`, `I ⊗ J`, each factor a rank-one SFT with Haagerup full
    group. At the groupoid level the conjunction effective + amenable + expansive is the
    only remaining unkilled alternative.
  - **Not ruled out:** proofs that use compact generation or expansivity of the
    groupoid. It is not known whether `(M ⋊ Γ) × G_2` is compactly generated.
- **Split along the triangular subgroup (2026-09-17, swarm-0917-w4-nv-cocycle; route tree
  plus class-kill).**
  - `haagerup-splits-as-coset-plus-subgroup-properness` (established): for any subgroup `H`,
    the Haagerup property is equivalent to a cnd function proper modulo `H` plus a cnd function
    proper on `H`. No normality is needed, so it applies to the simple group `nV`.
  - Route `brin-thompson-nv-a-t-menable-via-triangular-split` with `H = T_n`, the elements
    preserving the coordinate tower `C^n → ... → C`. R1: a cnd function proper modulo `T_n`. R2: a
    cnd function on `nV` proper on `T_n`, which implies Problem B for `Γ = V, Z`. Both are
    necessary, so this route is an equivalence.
  - `brin-thompson-triangular-subgroup-is-undistorted` (established): every infinite-order
    element of `T_n` grows linearly in the exponent cocycle, so it is undistorted in `nV`.
  - **Class-kill.** `brin-thompson-nv-no-cubical-action-proper-mod-triangular` (established)
    rules out "Farley-type walls for the cosets, plus Problem B for the fibres". No
    commensurating action, CAT(0) cube complex or wall space is proper modulo `T_n`, or modulo
    any undistorted subgroup.
    - **Invariant:** growth along the distorted Callard–Salo cyclic subgroup `⟨f⟩`.
    - **Where every member dies:** the bounded-or-linear dichotomy makes the wall count bounded
      on `⟨f⟩`. The pigeonhole into finitely many cosets then forces a power of `f` into `H`,
      where it would be undistorted
      (`cubical-coset-proper-actions-capture-distorted-elements`).
    - R1 must therefore be non-cubical, with `ψ_1(f^N) → ∞` and `ψ_1(f^N) = O(log^8 N)`.
- **No cubical proof of the fibre half either (2026-09-17, swarm-0917-w4-pull-nv-1;
  class-kill).**
  - `commensurating-loxodromics-split-their-centralizers` (established): if `ℓ(z^N)` is
    unbounded, the finitely many `⟨z⟩`-orbits with one-ended trace of `A` are permuted by
    `C_G(z)`. A finite-index subgroup then translates along one of them, giving `φ : C' → Z`
    with `φ(z) = 1`. So a central element of a perfect group with no finite quotients is
    elliptic in every commensurating action.
  - `brin-thompson-nv-fibre-elements-are-cubically-elliptic` (established): `C(C,Z) ⋊ V` is
    perfect with no finite quotients, and `1_C` is central. Its copies in `nV` make every
    element of the fibrewise subgroup `K_n`, of `V^n`, and of their conjugates and coordinate
    permutations elliptic in every commensurating action of `nV`. So no commensurating action is
    proper on `T_n` (R2), on `V × id`, or on `C(C,Γ) ⋊ V` for any `Γ` with an infinite-order
    element (Problem B).
    - **Invariant:** a central element of a perfect group without finite quotients. The
      elements involved are undistorted, so the distortion kill above does not reach them.
    - **Where every member dies:** the finite set of one-ended orbits of the central element,
      whose translation character cannot be nonzero on it.
    - **Consequence:** both halves R1 and R2 of the triangular split, and every approach to
      Problem B through walls or charts, must be non-cubical. A proof needs a
      non-commensurating cnd function, for example an infinite weighted sum of wall counts, or a
      cocycle whose representation either has spectrum of `π(1_C)` accumulating at `1`, or has
      a nonzero `1_C`-invariant component. If the spectrum stays away from `1` on the
      orthogonal complement of the invariant vectors, the cocycle restricted to `⟨1_C⟩` is a
      coboundary there.
    - **Not ruled out:** uniform ellipticity of `V × id` (property FW for `nV`). Elementwise
      ellipticity gives no uniform bound. Ellipticity of the baker's map is also open.
- **Linear growth along fibre elements for every cnd function (2026-09-17,
  swarm-0917-w5-pull-nv-1; new constraint plus class-kill).**
  - `nv-cnd-functions-grow-at-most-linearly-along-fibre-elements` (established): for every
    unitary representation of `G = C(C,Z) ⋊ V` and unit vector `ξ`,
    `|Im⟨π(1_C)ξ,ξ⟩| ≤ 28(‖π(1_{[0]})ξ − ξ‖² + max_i ‖π(h_i)ξ − ξ‖²)`, with three fixed `h_i ∈ V`.
    Spectral shells of the central `1_C` then give `ψ(k·1_C) ≤ 2ψ(1_C) + 28π²k(…)` for every cnd
    `ψ`. Through `Φ`, `ψ(g^k) = O(k)` on `nV` for every `g` fixing a coordinate and every
    element of `V^n`.
  - **Invariant:** `V`-paradoxicality of `C` (`[0] ~ [00] ~ [01] ~ [1]`). It makes the
    first-order part `U ↦ Im⟨π(1_U)ξ,ξ⟩` of an almost invariant vector state a paradoxical,
    almost invariant, finitely additive functional.
  - **Consequence:** a proof of R2 or of Problem B for `Z` needs a cnd function that is proper
    along `id × s` yet grows at most linearly there. Word length gives only `O(k²)`.
  - **Class killed:** positive-drift characters `e^{2πiτ}` of `C(C,Z)`, with `τ ≥ 0`, any number
    of atoms or none. Spectral measures of `ε`-almost invariant vectors give them mass `≤ 10ε`.
    This extends §3(g) of the 2026-09-16 artifact.
  - **Not ruled out:** signed drifts that cancel to first order. Relative (T) of `(G, Z·1_C)`
    stays open. The inequality is second order, so it cannot give a spectral gap.
- **Vertically triangular chart cocycles are bounded (2026-09-17, swarm-0917-w6-w6-nv-pull;
  class-kill).**
  - `nv-vertically-triangular-chart-cocycles-are-bounded` (established). Let
    `v: X → H` be supported on charts with `pr_n∘φ(x, y) = w(x)·y`, twisted by any unitary
    representation. If `v − g·v ∈ ℓ²` for `g_i = h_i × id` and for all vertical swaps
    `id × s_w`, then `‖v‖² ≤ 100 Σ_i ‖v − g_i·v‖²`. So the cocycle is a coboundary and bounded
    on `nV`.
  - In particular, every infinite weighted sum of brick wall counts `Σ_k w_k|gA_k Δ A_k|` that is
    finite on `nV` is bounded by `400 Σ_i ψ(g_i)`. This closes the loophole "infinite weighted
    sums of wall counts" left open above.
  - **Invariant:** the paradoxical spectral gap `1/10` of `V` on ℓ² of any `V`-set with a
    `V`-equivariant extraction to `Prob(C)` (here `φ ↦ (pr_1∘φ)_*λ`).
  - **Step where every member dies:** the codimension-one sweep. The swap `id × s_w` at the
    depth of a row's vertical prefix pushes the whole row out of the support. So `v` is ℓ² on
    each `V × id`-invariant row, and the gap then bounds each row by three fixed elements.
  - **Consequence:** P1, P2, P3 and both routes R1 and R2 need cnd functions not of this form.
    The same goes for any proof of non-(T) or non-FW.
  - **Not ruled out:** supports with some `V × id`-invariant piece where `v` is not ℓ². Examples
    are charts with non-triangular last coordinate, all charts, point orbits, and non-chart
    parameter spaces.
- **swarm-0917-w6-nv-last2 (2026-09-17): the triangular split collapses to the one hole R1.**
  - **Result (ESTABLISHED):** `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`. For
    `n ≥ 2`, `nV` is Haagerup iff some cnd function is proper modulo `T_n`, iff one is proper
    modulo `V^n`.
  - **Mechanism:** finitely many automorphic images of `T_n` meet in a finite group
    (`brin-thompson-nv-product-subgroup-has-finite-shear-core`). Coordinate permutations cut
    `T_n` down to `V^n`. Shears `t^{(i,j)}_s` (`s ∈ S`, a generating set of `V`) cut `V^n` down
    to at most `2^n` elements, because `Z(V) = 1`. Averaging then applies
    (`haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core`).
  - **New route:** `brin-thompson-nv-a-t-menable-via-proper-modulo-triangular`. It has one hole,
    R1, and the hole is also necessary. R2 and Problem B are consequences of R1
    (`brin-thompson-nv-cnd-proper-on-triangular-via-transversal`), so they are no longer
    independent prerequisites.
  - **Does not transfer:** to `K = ker c` or the diagonal subgroup, because small-support
    elements survive finite conjugation.
- **Integrated measured walls on `C^n` (2026-09-17, e-nv-walls; dies; class-kill, OPEN only
  through one input).** Plan: build R1 as a non-cubical measured-wall function with an invariant
  measure, e.g. the anisotropy wall `ψ(g) = ∫|α(g,x)| dx` on `C^2 × Z`, which is cnd on the
  area-preserving subgroup.
  - **Input.** `callard-salo-element-is-ae-locally-periodic` (OPEN; the argument is complete except
    for a written-out transport through Callard–Salo's block embeddings). The Callard–Salo element
    acts inside the head's conveyor belt, so it is Lebesgue-a.e. locally periodic, and its germ size
    is `≤ C(L(x)+1)` uniformly in the power, where `λ(L ≥ ℓ) ≲ ℓ q^ℓ`.
  - **Kill.** `nv-local-density-walls-bounded-on-callard-salo-element`: every wall function
    dominated by `∫ Φ(germ size) h dλ`, with `h` bounded and `Φ` subexponential, is bounded on
    `⟨f⟩`. So none is proper modulo `T_n`. This covers the anisotropy wall, cocycle integrals and
    Lebesgue-integrated wall counts.
  - **Invariant:** the belt-length tail, set against the uniform germ bound.
  - **Where every member dies:** `sup_N ψ(f^N) ≤ A + ‖h‖_∞ Σ_ℓ λ(L=ℓ) Φ(C(ℓ+1)) < ∞`.
  - **Computation that changes belief.** The expected `O(log N)` head-displacement growth does not
    occur: displacement is bounded by the belt length. SMART on a cyclic tape of length `c` has
    4 cycles of length `2c·3^c` (`experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py`).
  - **Forced shape for R1:** weights exponential in germ size on the rare regions `{L = ℓ}`, i.e.
    infinite-measure Maharam walls in `C^n × Z^n`. They must not be fibre-constant and must sit at
    fibre height `≍ L`, which gives odometer-type growth `≍ log N`.
- **Zipper transplant: Matui, Hughes, Lehnert/Farley (2026-09-17, e-nv-affine; class-kill plus
  loophole closure).**
  - **Dictionary.** Matui's zipper for `[[G_A]]` (arXiv:1210.5800, l.2054–2175) uses
    `Ω` = classes of compact open `G`-sets with cylinder source, modulo `U_{μ,ν}`, and
    `Z` = cylinders. Its analogue for `G_2^n` has `Ω_n` = brick-source bisections modulo
    products of `U_{μ_i,ν_i}`, and `Z_n` = bricks.
  - **Where it fails.** Matui's step (b), "φ_α([C_λ]) is in Z iff C_λ is contained in some
    C_{ν_i}", bounds the broken cylinders by the number of words of length `< m(α)`. For
    bricks, only one side has to be short, so infinitely many bricks break. These are the
    codimension-one faces of `brin-thompson-brick-charts-are-not-commensurated`.
  - **Class-kill.** `brin-thompson-2v-embeds-in-no-zipper-group` (OPEN: candidate proof,
    demoted at landing because its referee votes were lost): no group with a zipper action
    contains a distorted element.
    - So `2V` embeds in no SFT full group `[[G_A]]`, in no locally finitely determined group
      of local similarities of any compact ultrametric space, and in no group acting
      properly on a space with walls.
    - This settles the "Local similarities" bullet above: no choice of metric helps.
    - **Invariant:** distortion of the Callard–Salo element.
    - **Where every member dies:** step (b) made formal as the bounded-or-linear dichotomy.
      Zipper counts are linear along `⟨f⟩`, but they are `O(log^4 N)`.
  - **Expansivity loophole closed (OPEN, one narrow gap).**
    `expansive-amenable-purely-infinite-groupoid-hosts-kazhdan` builds
    `(M ⋊ Γ) × G_2`, with `Γ` a hyperbolic Kazhdan group and `M` a free minimal subshift
    extension of its horofunction subshift. That groupoid is expansive in Nekrashevych's
    sense, compactly generated, amenable (by Ozawa's boundary theorem, which avoids the
    exactness import), minimal, effective and purely infinite, and `Γ ≤ [[𝒢]]`. The gap is
    `hyperbolic-cayley-graph-ozawa-boundary-facts`.
  - **Surviving lever.** `G_2^n` carries a continuous `Z^n`-cocycle with AF kernel. The
    host's canonical cocycle has kernel `(M ⋊ Γ) × AF`, which contains `Γ`. A Haagerup proof
    must use such structure, with `ψ(f^N) → ∞` and `ψ(f^N) = O(log^8 N)`, and so it cannot
    be an integer wall count.
- **Brick-size functionals (2026-09-17, swarm-0917 e-nv-compute; exact census plus class-kill).**
  - Tools: `experiments/brin-thompson-cnd-2026-09-17/`. They compute 2V brick diagrams exactly: composition, and the
    minimal brick count `L` by a guillotine DP checked against brute force. They also run a zero-sum spectral cnd census
    with exact integer or Decimal certificates.
  - **Class-kill.** `brin-thompson-nv-max-type-size-functions-are-not-cnd` (established): no `ψ` with
    `ψ(g(w)) ~ κ G(‖w‖_∞)` on the `Z^3` of disjoint-support baker maps `b_00, b_01, b_1` is cnd, even plus
    `M(1 − δ_e)`. Here `G` is regularly varying of index `≥ 1/4`.
    - This kills `log L`, `(log L)^β` (`β ≥ 1/4`), diagram depth and its powers. `log L` is the natural survivor of the
      distortion test: it is cnd on `V` and grows like `log N` on distorted elements.
    - **Invariant:** the asymptotic shape of `ψ` on that `Z^3`, where `log L = ‖w‖_∞ log 2 + O(1)`.
    - **Where every member dies:** `ℓ^∞`-type kernels on `Z^3` are not of negative type (integer certificate for
      `‖·‖_∞^{1/4}` on `{−5..5}^3`, then Schoenberg powers), transported to `ψ` by a scaling limit.
    - `L − 1`, `√L − 1` and the symmetrized exponent integrals `∫(|a_x|+|a_y|)`, `∫|a_x − a_y|` die on small exact
      random witnesses.
  - **Lesson:** random test sets of up to 320 elements do not detect the failure of `(log L)^{1/2}` or `(log L)^{3/4}`,
    so a cnd census on `nV` must include structured abelian configurations.
  - **Survivors:** slowly varying functions such as `log log L`, and functions additive over disjoint supports
    (`ℓ^1`-like) on that `Z^3`.
  - **Not done:** numerics along the Callard–Salo element. Word norms are not computable by brute force, and the
    obstruction above does not use distortion.
- **Coordinate-extractable cocycles are bounded on centralizers (2026-09-17, swarm-0917-w7-w7-nv-follow;
  class-kill).** ESTABLISHED as `nv-extractable-cocycles-bounded-on-centralizers`.
  - *Statement.* Let `ρ` be a unitary representation of `nV` with a measure extraction `r ↦ μ_r ∈ M_+(C)` that is
    equivariant for `V` acting in one coordinate `j`. Then every 1-cocycle `b` into `ρ` satisfies
    `‖b(a)‖² ≤ 400 Σ_i ‖b(h_i^{(j)})‖²` on the centralizer of `h_1^{(j)}, h_2^{(j)}, h_3^{(j)}`, which contains the copy
    `E_j ≅ (n−1)V` acting on the other coordinates.
  - *Proof.* The paradoxical gap `1 ≤ 5δ` gives spectral gap 1/10. The commuting identity
    `(1 − ρ(β))b(a) = (1 − ρ(a))b(β)` then does the rest.
  - *Class covered.* Chart modules with no support condition; `ℓ²(nV/L) ⊗ π` for every `L` fixing a probability
    measure on `C^n` (amenable `L`, point and chart stabilizers, the regular representation); Koopman modules on
    `L²(C^n)`. The class is closed under direct sums, weak containment, inner conjugation and coordinate permutation.
  - *Consequence.* No such cocycle is proper. None witnesses R1 (via the explicit shear and permutation sum of
    `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`), P1, P2 or P3. This removes the survivors listed by
    `nv-vertically-triangular-chart-cocycles-are-bounded`, as far as they carry an equivariant location.
  - *Forced shape.* The representation of any Haagerup witness has almost invariant vectors for every conjugate of
    every coordinate copy of `V`, so it is weakly contained in no extractable representation.
  - *Open edge.* Gap-class cocycles are bounded on `E_1 ∪ … ∪ E_n` (for `n = 2`, on `V^2`). Whether they are bounded on
    all of `nV`, a relative FH for the class, turns on whether `nV` is boundedly generated by the `E_j` and a finite
    set. Heuristically the answer is no: the baker's powers move unboundedly many bits between coordinates.
- **The gap class has vanishing H^1** (2026-09-18, swarm-0917-w8-w8-nv-follow; class-kill, closes the open edge above).
  `nv-gap-class-cocycles-are-coboundaries`, proved by `nv-gap-class-cocycles-are-coboundaries-proof`.
  - *Statement.* Suppose every brick-local coordinate copy `A_P^{(j)} ≅ V^{|P|}` has spectral gap in `ρ`. Then
    `H^1(nV, ρ) = 0` for `n ≥ 2`. Every measure-extractable representation is in this class (constant `1/10`): chart,
    `ℓ²(G/L)` for `L` fixing a measure (including the regular representation, so `β_1^{(2)}(nV) = 0`), and Koopman.
    So is anything weakly contained in these.
  - *Proof.* The commuting identity with a gap set in a second coordinate bounds `b` on each brick-product subgroup
    `H_P = A_P^{(1)} ⋯ A_P^{(n)}`. Normalize `b = 0` on `V^n`. Then `b = 0` on every `H_P`, because some `A_{P'}^{(1)}`
    lies in both `H_P` and `V^n`. Finally `g H_D g^{-1} = H_R` makes `b(g)` `H_R`-invariant, hence `0`. No bounded
    generation is used; the heuristic above is true but beside the point.
  - *Class killed.* Proper cocycles, cocycles proper modulo `T_n`, and non-(T) witnesses in the gap class all die.
    Invariant: local spectral gap. Step: the conjugation `g H_D g^{-1} = H_R`.
  - *Forced shape.* A witness representation must have almost invariant vectors for some `A_P^{(j)}`. So it is weakly
    contained in no representation with an equivariant location in `C^n`.
  - *Calibration.* For `n = 1` the bounding step has no second coordinate, which is consistent with Farley's cocycle.
- **2026-09-18 (swarm-0917-w8-w8-nv-last1, host-geometry): a one-dimensional necessary prerequisite, the lift
  T-bar of Thompson's T (new decomposition, no kill).**
  - *Established.* `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`. The winding labels
    `n_a = ⌊a(·)⌋` on cones give an injective homomorphism `a ↦ (n_a ∘ ā^(-1), ā)` from `T̄` into
    `C(C,Z) ⋊ T ≤ C(C,Z) ⋊ V ≤ 2V`. It sends the central translation `z` to `1_C`.
  - *New prerequisite that can fail on its own.* `lifted-thompson-t-is-a-t-menable` (OPEN) is
    necessary for this claim, via route `lifted-thompson-t-a-t-menable-from-cantor-integer-maps`.
    - `T` is Haagerup, so this is equivalent to a cnd function on `T̄` being proper on its centre.
    - It is an instance of the open central-extension problem, quoted verbatim in the node from
      arXiv:1905.10081, p. 96.
    - So any proof for `nV` must settle the Haagerup property of `T̄`, a finitely presented
      extension of `T` by `Z` with the bounded Euler class.
  - *One-dimensional refutation route.* `lifted-thompson-t-center-has-relative-t` (OPEN) implies
    `cantor-integer-maps-central-direction-has-relative-t`, via
    `cantor-integer-maps-central-direction-via-lifted-thompson-t`, and so refutes this claim. Here
    the central direction is tested inside a group whose central quotient is the Haagerup group `T`.
    The obstructions recorded for `C(C,Z) ⋊ V` do not pass to `T̄`:
    - every homogeneous quasimorphism of `G` vanishes on `1_C`, but in `T̄` the rotation
      quasimorphism has `rot(z) = 1`, so `z` is undistorted;
    - the cubical ellipticity of `1_C` and the Callard–Salo distortion concern the larger groups.
  - *Killed inside T-bar.* Permutation witnesses on dyadic `T̄`-orbits of `R`, by (TC1) of
    `thompson-t-orbits-carry-no-invariant-means`.
  - *Cheapest next step.* Check CCJJV Proposition 4.2.14 verbatim. If its hypotheses hold for
    `T̄ → T`, the new prerequisite closes and the refutation route dies.
- **2026-09-18 (swarm-0917-w9-w9-nv-pull, symbolic-dynamics): an AF-by-Z² kill of the
  rank-≥2 groupoid route (class kill, counterexample to need (S_k), k ≥ 2).**
  - *Established.* `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan`, via
    `af-by-z2-kazhdan-host-proof`. Take the Robertson–Steger boundary groupoid `Γ⋉Ω` of a
    Kazhdan `PGL_3(K)` lattice. It is effective, because the action is topologically free:
    the proof tests simplicity against the representation on `ℓ²(Γ/Γ_ω)`. It carries a
    continuous `Z²` cocycle, the shape offset of any generator `s_{v̄,ū}` that realizes
    `u_γ1_{Ω[ū]}`. The offset is well defined by the gauge action (new import
    `robertson-steger-rank-two-ck-algebra-gauge-action`) and injectivity of φ. The kernel
    of the cocycle is AF: it is the union of the same-shape chart groupoids `K_{(N,N)}`.
  - *Killed class.* Proofs that the Kazhdan subgroups of `[[𝒢]]` are finite, or that
    `[[𝒢]]` is Haagerup, from any sublist of the following:
    - minimal, effective, ample, Hausdorff, expansive, amenable action groupoid;
    - `C*` simple, nuclear and purely infinite;
    - a continuous `Z^k` cocycle with AF kernel, `k ≥ 2`.

    Invariant: property (T) of `Γ`. Step where every member dies: the finiteness
    conclusion, or the properness of the cnd function, which Delorme–Guichardet bounds on `Γ`.
    This also closes audit D1 of `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`.
  - *What survives.* The product factorization of `G_2^n`, and `(S_1)`.
  - *Cross-reference (added at the e2-w2-nv-separate landing, same day).* This is the
    concrete instance of the risk that referee lens 3 flagged against (S_k) in the entry
    below: the hypothesis list of `af-by-zk-full-groups-have-finite-kazhdan-subgroups`
    carries no expansivity and no pure infiniteness, so it quantifies over far more than
    `G_2^n`. That entry raised the worry abstractly; this one settles it for `k ≥ 2` with
    an explicit host, so `nv-finite-kazhdan-subgroups-via-af-by-zn` must be restated with
    the extra hypotheses `G_2^n` actually has, or abandoned for `n ≥ 2`. It also resolves
    loose end 1 recorded on `nv-brick-groupoid-and-kazhdan-host-are-both-o2`: the
    Robertson-Steger action **is** topologically free, so `𝒢_RS` is effective and the
    effective form of the C\*-level class kill is available through Step 6 alone, without
    the `𝒢_W1` gap.
- **2026-09-18 (e2-w2-nv-separate, operator-algebras): the C\*-layer is killed for at least
  one Kazhdan host, and the separation collapses onto the AF-by-`Z^n` cocycle. Posted with
  two claims ESTABLISHED; **both returned to OPEN at landing**, 2 of 3 referees refuted.**
  - **Named invariant tried:** the reduced C\*-algebra `C*_r(𝒢)` of the groupoid, together
    with Matui's groupoid homology `H_*(𝒢)`. It **fails to separate**.
  - **Mechanism.** For second countable Hausdorff étale groupoids
    `C*_r(𝒢 × ℋ) ≅ C*_r(𝒢) ⊗_min C*_r(ℋ)` (proved from scratch in
    `nv-brick-groupoid-and-kazhdan-host-are-both-o2-proof` Step 1:
    `(𝒢 × ℋ)_{(x,y)} = 𝒢_x × ℋ_y`, so the reduced representation of the product is a
    tensor of two faithful reduced representations, whose norm is the minimal tensor
    norm). Hence `C*_r(G_2^n) ≅ O_2^{⊗n}` and `C*_r(𝒢 × G_2) ≅ C*_r(𝒢) ⊗ O_2`, and
    Kirchberg's `O_2`-absorption theorem (`A ⊗ O_2 ≅ O_2` for unital separable simple
    nuclear `A`; no UCT) collapses each side to `O_2`. Matui's Künneth formula with
    `H_*(G_2) = 0` gives vanishing homology throughout.
  - **What survived the referees (the class kill, in its weaker form).** For the
    Robertson–Steger host `𝒢_RS = (Γ' ⋉ Ω) × G_2` the input is clean:
    `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` item 4 states simplicity,
    nuclearity and pure infiniteness of `C(Ω) ⋊_r Γ'` directly. So
    `C*_r(G_2^n) ≅ O_2 ≅ C*_r(𝒢_RS)` and `H_* = 0` for both, and:
    - **Invariant:** property (T) of the Kazhdan lattice `Γ'`.
    - **Step where every member dies:** the passage from an invariant of `C*_r(𝒢)`, or of
      `H_*(𝒢)`, to a statement about `[[𝒢]]`. A groupoid whose full group contains an
      infinite Kazhdan group has the *same algebra and the same homology* as `G_2^n`.
    - **Scope:** K-theory and all classification data, traces and tracial states, the
      ideal lattice, the Cuntz semigroup, nuclear dimension, decomposition rank,
      `Z`-stability, strong self-absorption, quasidiagonality, the UCT, Matui's HK-type
      invariants, and even the hypothesis "`𝒢` is amenable with `C*_r(𝒢) ≅ O_2`". **The
      COLD operator-algebras family is closed on this goal unless a proof uses the
      diagonal.**
  - **What the referees took away.** `nv-brick-groupoid-and-kazhdan-host-are-both-o2` is
    **OPEN**, demoted at landing. Lens 2 refuted Step 5 of its route: the
    Rørdam–Sierakowski sentence quoted there is an *existence* statement about *some* free
    amenable minimal action of `Γ`, and it was applied universally to the host's `M`,
    which is a different, independently constructed action. Step 5's four needed
    properties (unital, separable, simple, nuclear) are now the open prerequisite
    `kazhdan-host-crossed-product-is-simple-and-nuclear`, closable by two standard imports
    (amenable action ⇒ nuclear crossed product; topologically free + minimal ⇒ simple).
    Until it closes, `C*_r(𝒢_W1) ≅ O_2` is not available, and with it go **the effective
    form of the class kill** (`𝒢_W1` is the only host asserted effective;
    `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` explicitly does not assert
    that `Γ'` acts topologically freely) **and the Cartan gate below**.
    `brick-groupoid-has-zn-cocycle-with-af-kernel` is also **OPEN**, but only
    procedurally: all three lenses checked its route and found every step correct, so it
    waits on `brick-af-cocycle-referee-confirmation`, a per-claim vote.
  - **Gate (Cartan), conditional on that gap closing.** `G_2^n` and `𝒢_W1` are ample,
    Hausdorff, minimal and effective, so by Renault/Steinberg reconstruction the remaining
    operator-algebraic question is whether `C(C^n)` and `C(M × C)` are conjugate Cartan
    subalgebras of `O_2`. A surviving operator-algebraic proof must be
    **diagonal-sensitive**: it must use the Cartan pair, never the algebra alone.
  - **New necessary prerequisite (OPEN), which can fail on its own.**
    `brick-groupoid-not-isomorphic-to-kazhdan-host`, via
    `brick-host-nonisomorphism-from-nv-haagerup`: if `G_2^n ≅ 𝒢_W1` then
    `nV = [[G_2^n]] ⊇ Γ` and this claim is refuted — by an explicit isomorphism, with no
    cnd function anywhere. No invariant on the graph currently decides it. (The equality
    `[[G_2^n]] = nV` used there is proved in that route and was checked by lens 1: boxes
    form a semiring, so differences of bricks are finite disjoint unions of bricks.)
  - **The candidate invariant that may still separate.**
    `brick-groupoid-has-zn-cocycle-with-af-kernel`: `c^{(n)} : G_2^n → Z^n` is continuous
    with kernel the tail equivalence relation `R_2^n`, which is AF. The recorded hosts are
    **not known** to carry any such cocycle *and not known not to*, so this separates
    nothing yet — it is the only property on which they have not already been shown to
    match. Lemma B of `af-by-zk-full-groups-have-finite-kazhdan-subgroups` (established
    there, and confirmed by all three lenses including the Minkowski step for
    `Γ ≤ GL_4(Z)`) gives the first constraint: the full group of an AF groupoid is locally
    finite, so any AF-kernel cocycle on a product must be almost faithful along a Kazhdan
    subgroup of a factor. That kills the host's canonical cocycle and every cocycle that
    ignores `Γ` — but not every cocycle.
  - **One-hole route to a downstream node.** `nv-finite-kazhdan-subgroups-via-af-by-zn`
    gives `kazhdan-subgroups-of-brin-thompson-groups-are-finite` from the single open
    statement (S_k) = `af-by-zk-full-groups-have-finite-kazhdan-subgroups`. The route is at
    groupoid level, so none of the cnd-function class kills above applies to it. **But
    (S_k) is much stronger than it looks** (lens 3, recorded on that node): its hypothesis
    list contains no expansivity and no pure infiniteness, so it quantifies over *every
    free minimal Cantor `Z^k`-system* (`ker c` is then the unit space groupoid, which is
    elementary, hence AF). In particular (S_1) is **not** established by
    `input-encoded-sft-groupoid-hosts-are-not-universal`, whose item 2 is stated for
    irreducible one-sided SFT groupoids only; and for `k ≥ 2` the class contains minimal
    Cantor `Z^2`-systems with non-amenable full groups containing free subgroups
    (Elek–Monod). A proof of (S_k) must survive those members, or (S_k) must be restated
    with the extra hypotheses `G_2^n` actually has.
  - **The gate, stated as required, with the correction the referees forced.** *Every
    surviving proof of a-T-menability for `nV`, and every surviving proof that its Kazhdan
    subgroups are finite, must use a property of `G_2^n` that the hosts provably lack.*
    Individually dead as separators: compact generation, expansivity, pure infiniteness,
    effectiveness, amenability, minimality, absence of an invariant measure, and anything
    computed from `C*_r(𝒢)` or `H_*(𝒢)`. **The list is not closed under conjunction**
    (lens 1): `𝒢_W1` is effective and amenable but is not known to be expansive, and
    `𝒢_RS` is expansive and amenable but its action is not known to be topologically free,
    so the *conjunction* "effective + amenable + expansive" is still an unkilled
    groupoid-level alternative, as this node already records at the Robertson–Steger
    entry. The candidates left are therefore that conjunction, the AF-by-`Z^n` cocycle,
    and the Cartan pair — and these are three distinct things, not two: the cocycle is
    strictly weaker data than the Cartan pair, which recovers the groupoid entirely.
    Finally, the proof must be non-zipper: the only known proof of the `k = 1` SFT case is
    Matui's zipper action, and `brin-thompson-2v-embeds-in-no-zipper-group` forbids a
    zipper for `2V` because of the Callard–Salo distorted element.
- **2026-09-19 (swarm-0917-w15-w15-nv-pull, obstruction-miner / cohomology-index): (K) is a
  Hermitian-domination problem, and census refutations of (K) are dead.**
  - **Setting.** On the `T̄`-Haagerup prerequisite, the square-root branch is (K),
    `lifted-thompson-t-euler-class-in-kahler-subspace`.
  - **Reformulation.** `thompson-t-kahler-euler-class-is-a-hermitian-domination-problem`
    (ESTABLISHED, self-contained) proves that (K) holds iff the following has a solution:
    - unknowns: a cnd function `ψ` on `T` and an odd function `f`;
    - condition: `|⟨c, (Ω + ∂f)c⟩| ≤ ⟨c, G_ψ c⟩` for all `c ∈ c_c(T)`;
    - here `Ω(g,k) = ∫_0^1 u_{g^{-1}} du_{k^{-1}}` is the explicit displacement area kernel,
      with `|Ω| ≤ 1`.

    The GNS completion is a universal witness for this condition.
  - **Class-kill.** Every finite section `E × E` is feasible, with `f = 0` and
    `ψ = 2C·1_{≠1}`. So finite SDP certificates, finite relator checks and bounded-radius
    computations cannot refute (K), which rules out the census-computation family on this edge.
  - **No bounded witness.** The displacement form `i(Ω + ∂f)` is `ℓ²`-unbounded for every odd
    `f`, so every successful `ψ` must be unbounded. This part uses `e_R ≠ 0`, which is recalled.
  - **What remains.** A refutation of (K) has to be global: for every unbounded cnd `ψ`, it
    must produce violating vectors that escape to infinity. A proof of (K) has to construct one
    `ψ` that dominates this form. By the integrably-paired kill, that `ψ` cannot be a wall
    function.
- **2026-09-19 (swarm-0917-w16-w16-nv-last1, last-mile / entropy-measure): the kernel K is the
  meet of the Jacobian and diagonal subgroups; new necessary prerequisite "[[X]] is Haagerup".**
  - **Decomposition.** `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal` (ESTABLISHED,
    self-contained) proves `K = M_n ∩ D`. Here `M_n` is the Lebesgue-preserving subgroup (log-Jacobian
    `Σc_i ≡ 0`), and `D`, the subgroup with diagonal cocycle values, is the Higman–Thompson group
    `V_{2^n,1}`, by block interleaving. Since cosets of `M_n` and `D` meet in cosets of `K`,
    `P1 ∧ P2 ⟺ (Q_J) ∧ (Q_D)`: some cnd function is proper modulo `M_n`, and some is proper modulo
    `D`. The goal also splits as (Q_J) plus "proper on `M_n`", and as (Q_D) plus "proper on `D`".
    Both halves are non-cubical (the fibre element `z` has powers in distinct cosets of each), and
    the gap class sees neither.
  - **New necessary prerequisite that can fail on its own.** Conjugating by Salo's baker map `Φ`
    identifies `M_2` with the full group of the homoclinic-plus-shift groupoid, and puts the
    full-shift topological full group `[[X]]` inside `M_2`. So the goal implies
    `full-shift-topological-full-group-is-a-t-menable` (OPEN, route
    `full-shift-full-group-a-t-menable-from-nv`). That group is invisible to (Q_J) and tests only
    "proper on `M_n`". It is a subgroup of the wobbling group of `Z`, contains all RAAGs, and has
    linear orbit growth, so it contains no `Z^2 ⋊ SL_2(Z)`.
  - **Established on the way.** `full-shift-full-group-kazhdan-subgroups-are-finite`: aperiodic
    orbits of a Kazhdan subgroup are finite of size `≤ 1 + 8r/ε²`, by a half-line Cheeger cut, so
    the subgroup is finite. This settles the `[[X]]`-part of
    `kazhdan-subgroups-of-brin-thompson-groups-are-finite`. The argument dies on `M_2`, whose orbits
    grow exponentially.
  - **Class-kill (recorded on the new node).** Every cnd function `∫|k_g| dν` over `σ`-invariant
    measures, and every summable series of them, is not proper on `[[X]]`. This includes the
    restriction of the Maharam wall `ψ_M`, which is cnd and unbounded on `M_n` because `M_n`
    contains no brick-local copy of `V`. The involutions that swap a deep cylinder around an
    aperiodic point with its shift have `ψ → 0`, because invariant measures have no atoms at
    aperiodic points. So a proper-on-`M_n` witness cannot be an invariant-measure wall.
  - **What remains.** (Q_J) (Jacobian transversal), and a non-invariant-measure proper cnd
    function on `[[X]]`, as the first test of "proper on `M_n`".
- 2026-09-20 (swarm-0917-w21-w21-nv-pull, obstruction-miner): the cubical side is split off
  into `brin-thompson-2v-has-property-fw` (OPEN in the literature, FFWZ arXiv:2603.24687
  Remark 6.7, quoted there). A yes answer there kills every wall, cube and tree route to this
  node outright. That is stronger than the existing properness-modulo-`T_n` kill.
  - *Recorded kill.* One suggested fixed-point proof covers `C²` by rigid stabilizers and
    applies a pairwise (or `k`-wise) Helly lemma. It is invalid. See
    `commensurating-actions-have-no-finite-helly-number` (ESTABLISHED): the affine Weyl group
    `Ã_k` is generated by `k+1` reflections, any `k` of which generate a finite group, and
    it has unbounded wall count. The invariant: fixed-vertex sets are median-closed but not
    convex. Every such proof dies at the step "the fixed sets meet".
  - *Open single-element test.* Is the baker map `β(x, ey) = (ex, y)` elliptic? It is
    undistorted, and its centralizer gives no obstruction.
