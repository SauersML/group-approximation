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
---

**OPEN.** Let `Gamma < G` be an infranormal, non-normal pair of Kazhdan groups, with `(F, kappa)` a Kazhdan
pair for `Gamma`. For every trace-preserving `sigma : G -> U(prod_U M_n)` with coordinates `sigma_n`, after
`o(n)` padding there are genuine representations `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with

```text
max_(s in F) ||sigma_n(s) - pi_n(s)||_2  ->  0   along U.
```

This is hypothesis (H1) of `hs-rounding-and-actor-gap-force-ccr`, required for every model. It is
flexible normalized-HS stability of `Gamma`, restricted to the approximate representations that
extend to trace-preserving representations of `G`.

## Attempts

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
  - **No known reduction makes (H1) easier, but equivalence to the target is not proved.** (H1) ⟹
    non-hyperlinear is established (modulo review); the converse — that hyperlinearity of the wreath
    yields a `G`-model whose vertex restriction does not round — is not on main. So (H1) is
    un-reduced, not proven strictly as hard as the target.
  - **Most concrete handle: the Laurent sibling.** theorem-e also has route
    `unit-type-rounding-via-laurent-vertex-rounding` (requires `laurent-vertex-rounds-for-every-model`).
    Lane `nh-laurent-commutant` (52efa2195) reduced its converse to a relative-(T) question: is the
    mixed-level root group `K_i` Kazhdan for `r >= 4`? Unlike flexible stability, relative (T) is
    within reach of Ershov–Jaikin-Zapirain angle methods, so `K_i` Kazhdan is the one point where the
    existence problem becomes a (T)-style question the corpus has tools for. Recommended sub-target.
