---
rg: 2
id: hs-stable-vertex-rounding-for-every-model
kind: claim
title: Every trace-preserving matrix-ultraproduct representation of the actor rounds on the Kazhdan vertex to genuine representations
distinct_from:
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) when the whole actor is coordinatewise genuine; this asks only that the restriction to the Kazhdan vertex round, for every model, with no genuine coordinates assumed.
  el-r-polynomial-robust-spectral-gap: that is the robust spectral gap for asymptotic finite-dimensional representations, free from property (T); this asks for rounding to genuine representations close on generators, which a spectral gap alone does not supply.
  hs-literal-commutant-profile-rounding-is-false: that refutes rounding onto the exact commutant of the supplied matrices; this asks for a nearby genuine representation, a target stable under the perturbation that kills the literal version.
  hs-rounding-and-actor-gap-force-ccr: that is the proved conditional which assumes (H1) for one model and derives normalization; this is (H1) itself, for every model, and nothing proved decides it.
refuted_by:
  - vertex-rounding-fails-at-symplectic-product-pair
---

**REFUTED as stated (2026-09-16).** (H1) fails at an explicit trace-preserving model of the residually finite
Kazhdan pair `Z^(2g) ⋊ Sp_(2g)(Z) × EL_r(F_q[x_1..x_d]) < Z^(2g) ⋊ Sp_(2g)(Z) × (EL_r(F_q[x_1^(±1)..x_d^(±1)]) ⋊ SL_d(Z))`
(`vertex-rounding-fails-at-symplectic-product-pair`). The Theorem E instance, which is what the unit-type chain
uses, is untouched and is now the open claim `theorem-e-vertex-rounds-at-every-actor-model`. The statement as
posed:

Let `Gamma < G` be an infranormal, non-normal pair of Kazhdan groups, with `(F, kappa)` a Kazhdan
pair for `Gamma`. For every trace-preserving `sigma : G -> U(prod_U M_n)` with coordinates `sigma_n`, after
`o(n)` padding there are genuine representations `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with

```text
max_(s in F) ||sigma_n(s) - pi_n(s)||_2  ->  0   along U.
```

This is hypothesis (H1) of `hs-rounding-and-actor-gap-force-ccr`, required for every model. It is
flexible normalized-HS stability of `Gamma`, restricted to the approximate representations that
extend to trace-preserving representations of `G`.

## Attempts

- **Refuted by a product pair (2026-09-16, lane `swarm-hs-stable-vertex-rounding-for-every-model`).**
  - **The pair.** Put `Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)`, let `K < H` be the Theorem E pair, and take
    `Γ = Γ_g × K < G = Γ_g × H`. It is residually finite and Kazhdan, with compression semigroup `Γ_g × P_K`,
    so it is infranormal and not normal.
  - **The model.** Tensor the Heisenberg models `α_(k_j)` of `rf-kazhdan-group-not-flexibly-hs-stable` with
    permutation models `λ_j` of `H`. The result is trace-preserving on `G`.
  - **Why nothing rounds.** Any rounding of `σ|Γ` on a generating set propagates to `Γ_g × e`. There the
    amplified models `α_(k_j) ⊗ 1_(m_j)` are non-roundable with constants uniform in `m_j`, by property (T)
    of the Heisenberg cover and the bimodule argument.
  - **Scope.** It holds under padding and under Dogon's compression, at every Kazhdan set. Unlike the Leavitt
    and Fournier--Facio scope bullets below, it needs no hyperlinearity input.
  - **Consequences.** `theorem-e-vertex-unit-type-via-deep-root-mass`,
    `hs-normalization-via-vertex-rounding-and-actor-gap` and `hs-normalization-via-vertex-rounding-and-liftable-masa`
    required this claim. The first is restated as `theorem-e-unit-type-via-instance-vertex-rounding`, through the
    instance claim. The other two target the general `kt-centralizer-normalization-hs` and have no replacement.
    Artifact:
    `research/artifacts/vertex-rounding-product-pair-2026-09-16.md`.
- **Literal commutant rounding.** Dead (`hs-literal-commutant-profile-rounding-is-false`). A small generic
  perturbation makes the literal commutant scalar, so the rounding target must be a nearby genuine
  representation.
- **Robust spectral gap.** Property (T) gives `(T;FD)^rob` (`el-r-polynomial-robust-spectral-gap`). It moves
  almost invariant vectors of each adjoint representation to invariant ones, but it produces no
  genuine representation close on generators. No mechanism beyond it is recorded.
- **Uniform Kazhdan constants.** Unavailable for the linear Theorem E pair
  (`uniform-kazhdan-fails-for-linear-theorem-e-pair`), so a rounding argument must work at the fixed
  generating set `F`.
- **Genuine coordinate models.** They satisfy it trivially. The content is models with no genuine
  coordinate structure, which is exactly where `kt-centralizer-normalization-hs` is open.
- **Scope (2026-09-12, lane `hyperlinear-nonsofic-l-times`).** Read literally over every infranormal,
  non-normal Kazhdan pair, this claim contains the nine-leaf Leavitt pair. There it is equivalent to
  nonhyperlinearity of `L_(F_2)(1,2)^x` (`leavitt-pair-vertex-rounding-is-nonhyperlinearity`), because
  both configuration groups are the unit group, which is minimally almost periodic. So the general form
  implies the unit group is not hyperlinear, and a hyperlinearity proof for that group refutes the
  general form. The Theorem E instance `theorem-e-vertex-rounds-to-unit-type-representations`, whose
  vertex has rich finite images, is unaffected.
- **Existence, not rigidity, is the whole gap (2026-09-12, lane `nh-h1-vertex-rounding`).** With
  `vertex-rounding-deep-nonunit-root-mass-vanishes` established, the route
  `theorem-e-vertex-unit-type-via-deep-root-mass` makes
  `theorem-e-vertex-rounds-to-unit-type-representations` — and through
  `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` the non-hyperlinearity of the Kun–Thom
  wreath — open *only* through this claim (H1) for the Theorem E pair. The median route
  `hs-normalization-via-vertex-rounding-and-actor-gap` also requires it. So (H1) is the unique open
  bottleneck of the whole chain.
  - **Every established input is conditional on the rounding.**
    `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
    `nonunit-projection-bounded-by-root-spectral-mass`, the shallow and deep root-mass claims, and
    `compressor-transport-exactifies-under-vertex-rounding` all begin "let `sigma` satisfy (H1) with
    roundings `pi_n`" and then constrain the non-unit mass of the given `pi_n`. None constructs
    `pi_n`. The compressor/torus action and property (T) of `G` are spent entirely on rigidity of an
    assumed rounding, never on its existence.
  - **G-extendability has not been used before rounding.** Whether `sigma|Gamma` rounds is a property
    of the single asymptotic homomorphism `sigma_n|Gamma : Gamma -> U(n)`; the extra data
    `sigma_n(t_i)` attaches to that same `sigma_n|Gamma` and only narrows which asymptotic
    representations must round. No argument in the corpus turns that narrowing into a genuine `pi_n`.
    So (H1) is exactly flexible normalized-HS stability of the infinite higher-rank Kazhdan group
    `Gamma` at `G`-extendable models: the strict form is impossible (Becker–Lubotzky), and the
    flexible form is unknown for every infinite higher-rank Kazhdan group (open even for `Sp_2g(Z)`,
    Dogon). By `amenable-flexible-hs-stability-is-strict-hs-stability` any proof must use models with
    non-injective limit trace, exactly the "far from genuine on the actor" case the theorem-e
    attempts already isolate.
  - **Correction (2026-09-13, lane `ex-hs-instability-kazhdan`).**
    - **Too broad.** "Unknown for every infinite higher-rank Kazhdan group" overstates what is
      open.
    - **A residually finite Kazhdan group that is not flexibly stable.** `Z^(2g) ⋊ Sp_(2g)(Z)`,
      `g >= 2`, a lattice in `R^(2g) ⋊ Sp_(2g)(R)`, is residually finite and Kazhdan, and it is
      not flexibly HS-stable (`rf-kazhdan-group-not-flexibly-hs-stable`). Its non-roundable
      models have regular limit trace.
    - **What is still unknown.** Flexible stability of lattices in higher-rank simple groups
      (`SL_n(Z)`, `Sp_(2g)(Z)`), and of `Gamma` itself.
    - **Consequence.** (H1) cannot follow from property (T), residual finiteness and the
      regular trace alone.
    - **Caveat on the scalar mechanism.** It is void wherever `H_1` and `H_2` of the vertex are
      finite (`finite-multiplier-projective-models-round-strictly`). An instability witness at
      such a vertex needs non-scalar defects.
  - **No known reduction makes (H1) easier, but equivalence to the target is not proved.** (H1) ⟹
    non-hyperlinear is established (modulo review); the converse — that hyperlinearity of the wreath
    yields a `G`-model whose vertex restriction does not round — is not on main. So (H1) is
    un-reduced, not proven strictly as hard as the target.
    **Update (lane `ex-q34-kt-double`, 2026-09-12).** The implication quoted as "not on main" is now on
    main as `kt-wreath-models-never-round-on-the-vertex` (landed 22:14, base wreath, every wreath model).
    `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex` extends it to every intermediate coset wreath
    `W_K` with `N` not in `K`. What stays open is a genuine converse: that failure of (H1) at some model
    produces a hyperlinear wreath.
  - **Most concrete handle: the Laurent sibling.** theorem-e also has route
    `unit-type-rounding-via-laurent-vertex-rounding` (requires `laurent-vertex-rounds-for-every-model`).
    Lane `nh-laurent-commutant` (52efa2195) reduced its converse to a relative-(T) question: is the
    mixed-level root group `K_i` Kazhdan for `r >= 4`? **Answered (lane `nh-ki-kazhdan`, 44267adad; PASS in
    `research/artifacts/review-swarm6-analysis-2026-09-12.md` §5):** yes for `r >= 5`
    (`mixed-level-root-group-is-kazhdan-in-rank-at-least-five`), no for `r = 4`
    (`mixed-level-root-group-is-not-kazhdan-in-rank-four`). The sub-target is settled. What it gives the
    converse is recorded in the correcting bullet on `laurent-vertex-rounds-for-every-model`.
- **Congruence-kernel projections (2026-09-12, lane `nh-h1-theorem-e-instance`).** Void at every fixed level
  (`theorem-e-congruence-projections-vanish-at-regular-trace`). The route was: take almost-invariant vectors of
  the congruence kernels `Γ(I)`, project onto their fixed subspaces, then correct with a Kazhdan projection.
  - At the regular trace, fixed subspaces of infinite subgroups have trace 0. Fixed-level almost-invariant
    subspaces with defect `< κ/√|S|` have vanishing dimension. So the hard step, "almost invariant but not close to
    invariant", never arises at a fixed level.
  - The route proves (H1) exactly for purely profinite vertex restrictions, and at the regular trace there are none.
  - Any rounding has asymptotically regular traces, and its root ideals escape every nonzero ring element. So a
    correction must work at `n`-dependent levels, with generating sets of unbounded `F`-length and non-uniform
    Kazhdan constants.
  - Extendability to `G` shortens the normal generators of the level `(x_1^m..x_d^m)` to `G`-length `O(log m)`.
    Averaging over the quotient needs `G`-length `>= m^d log q / log(2|F_G|+1)`, so compressor transport does not
    supply the projection.
  - No equivalence with a known-hard statement was obtained. Artifact: `nh-h1-theorem-e-instance-2026-09-12.md`.
- **Scope: the Fournier--Facio pair (2026-09-12, lane `ex-q34-kt-double`).** Read literally over every
  infranormal Kazhdan pair, this claim contains the Fournier--Facio pair, where it is false at every
  faithful model (`fournier-facio-vertex-rounding-fails-at-every-model`). The vertex contains a finitely
  presented infinite simple group, which every genuine finite-dimensional representation kills. So the
  general form implies that the Fournier--Facio group is not hyperlinear, and a hyperlinearity proof for
  that group refutes the general form. The Theorem E instance is unaffected.
- **What extension to the actor buys (2026-09-13, lane `ex-hs-instability-extension`).** The Theorem E instance
  stays OPEN. The map below is unreviewed.
  - **Before any rounding.** The largest roundable corner of `σ|Γ` commutes with `σ(G)`. So (H1) is zero-one
    after an actor-invariant split.
    - With `gcd(r, q-1) = 1`, (H1) holds at every actor model iff each actor model has an almost-intertwiner with a
      genuine-coordinate model of defect below the Kazhdan constant `κ`. The intertwining defect is either `0` or
      `>= κ`.
    - Base and intermediate wreath models are totally non-roundable.
    - See `compressor-extension-makes-roundable-vertex-part-invariant`.
  - **Under rounding.** With `d = 3` and `r >= 6`, vertex rounding at an actor model lifts to Laurent-vertex
    rounding (`actor-extension-lifts-vertex-rounding-to-the-laurent-vertex`).
  - **Calibration: one compressor forces nothing.** There are trace-preserving models of `<Γ, A>`, even of its
    wreath, whose vertex is exactly genuine of pure origin type and whose commutant is not normalized
    (`one-compressor-actor-models-with-exact-origin-vertex`, `one-compressor-wreath-has-models-with-exact-origin-vertex`).
    Extension to `G` acts only through the torus step and the two attractors, and only on an assumed rounding.
  - **Known instability mechanisms.**
    - Retract models (`el-r-polynomial-vertex-not-flexibly-hs-stable`) do not extend: the torus forces any actor
      model that kills `e_ij(x_2 R_+)` to be trivial on `Γ`.
    - Scalar cocycles are void wherever the multiplier is finite.
  - **The gap.** Nothing in extension produces an almost-intertwiner below `κ`.
