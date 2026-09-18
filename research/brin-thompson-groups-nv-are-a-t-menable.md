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
