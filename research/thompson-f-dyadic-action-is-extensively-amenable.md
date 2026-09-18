---
rg: 2
id: thompson-f-dyadic-action-is-extensively-amenable
kind: claim
title: The action of Thompson's group F on the dyadic rationals is extensively amenable
distinct_from:
  thompson-f-is-amenable: that is amenability of the group F; this is extensive amenability of one of its actions. The two are equivalent by thompson-f-amenable-iff-dyadic-action-extensively-amenable, but they are stated about different objects.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is amenability of certain Schreier graphs; extensive amenability of an action is strictly stronger than amenability of its Schreier graph in general.
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

**OPEN.** The action of `F` on the dyadic rationals `D ⊂ (0,1)` is extensively amenable. That is, some
`F`-invariant mean on the finite subsets of `D` gives full weight to the subsets containing any given
finite set.

## Consequences

- **Co-amenability of Jones' subgroup.** Through `jones-subgroup-coamenable-if-dyadic-action-extensively-amenable`
  it gives `jones-subgroup-is-co-amenable-in-thompson-f`, answering the question in Aiello–Brothier–Conti
  Remark 4.7 positively.
- **A refutation proves F nonamenable**, by Lemma 2.1 of Juschenko–Matte Bon–Monod–de la Salle
  (`affine-lamplighter-amenable-iff-extensively-amenable`).

## Known obstacles

- **The base graph is transient.** Mishchenko (arXiv:1512.03083) shows the simple random walk on the dyadic
  Schreier graph has nontrivial Poisson boundary. So the recurrence criterion of Juschenko–Nekrashevych–de la
  Salle does not apply.
- **The action is primitive.** Point stabilizers in `(0,1)` are maximal subgroups (Aiello–Nagnibeda,
  arXiv:2103.07885, abstract). So there is no nontrivial `F`-quotient of `D` along which to apply the extension
  principle.

## Attempts

- **Inverted-orbit target (2026-09-14, hl-f-extensive-amenability-dyadic).** By JMBMdlS Proposition (§"The
  inverted orbit"), this claim is equivalent to a `μ`-independent confinement of the inverted orbit `O_n` of
  a random walk on `F`: for every `ε > 0`, `P(|O_n| < ε n) > e^{−ε n}` infinitely often, equivalently
  subexponential decay of `E(2^{−|O_n|})`, equivalently subexponential return probability of the
  switch-walk-switch walk on `(Z/2)^{(D)} ⋊ F`. This is the ESTABLISHED equivalence
  `f-dyadic-ea-iff-inverted-orbit-confinement`; the concrete OPEN target is
  `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`, with route
  `f-dyadic-ea-from-inverted-orbit-confinement`.
- **The recurrence route provably fails (2026-09-14).** `f-dyadic-action-is-not-recurrent`: the mean
  inverted orbit is ballistic, `(1/n) E|O_n| → P(T = ∞) > 0`, from Mishchenko's transience. So the
  sufficient condition `(1/n) E|O_n| → 0` fails, and any proof must use the strictly weaker rare-event
  confinement. A genuine exponential upper bound on `E(2^{−|O_n|})` would instead prove `F` nonamenable.
- **Collapse onto the root (2026-09-17, swarm-0917-w4-f-decomp).** This claim is *equivalent* to
  `thompson-f-is-amenable`, by the ESTABLISHED `thompson-f-amenable-iff-dyadic-action-extensively-amenable`.
  - *Mechanism.* The breakpoint cocycle `c_g = β(g⁻¹) ∈ Z^{(D)}` embeds `F` in `Z^{(D)} ⋊ F` with trivial
    kernel. JMBMdlS Corollary "prop:functor:amenable:intro" then turns extensive amenability into
    amenability of `F`.
  - *Consequences.* The earlier distinct_from entry ("the converse is not known") was stale and is
    corrected. A refutation proves `F` nonamenable, and a proof proves `F` amenable. So
    `jones-subgroup-coamenable-if-dyadic-action-extensively-amenable` gains nothing beyond amenability of `F`.
  - *Quantitative form.* `thompson-f-dyadic-ea-witnesses-need-tower-size`: a `Γ`-invariant witness at
    level `C^{−n}` that covers the generators' breakpoints satisfies `|supp ν|·(4LC^n+3)^k ≥ exp_n(0)`. So
    witnesses of fixed tower size are excluded by Moore's theorem.
  - *Route into the root.* `thompson-f-amenable-via-dyadic-extensive-amenability`.
- **Algebraic certificates are killed (2026-09-17, swarm-0917-w5-f-extensive).** See
  `f-ea-calculus-certificates-force-f-prime-to-act-trivially` (ESTABLISHED, unrefereed).
  - *Class.* Take the smallest class `𝓟` of actions that contains:
    - recurrent actions;
    - all actions of groups with no copy of `F`.

    Require `𝓟` to be closed under:
    - pullbacks, invariant subsets, images and local-to-global;
    - the extension principle (JMBMdlS Proposition 2.4);
    - functor extensions with `F`-free values (Theorem 1.3).

    `𝓟` contains every certificate assembled from those JMBMdlS results.
  - *Invariant.* Property P: the commutator subgroup of every copy of `F` fixes every point.
  - *Where every member dies.* The base case is `thompson-f-recurrent-f-sets-factor-through-the-abelianization`.
    - The extension principle preserves P because `Φ′ ≤ G_y` is exhausted by the commutants of the rigid
      copies `ψ(F[a,b])`.
    - Functor extensions preserve P because a nontrivial action of `Φ′` would embed `F′` in the functor value.
    - `F ↷ D` has `F′` acting nontrivially, so it has no certificate in `𝓟`.
    - For twisted embeddings, `ker c ⊇ F′ ⊇ F`.
  - *What remains.* This claim can only be proved by a non-algebraic analytic certificate, namely the
    rare-event inverted-orbit confinement above.
- **Endpoint root gaps are inverse-square, and endpoint localization stalls (2026-09-17,
  swarm-0917-w5-f-dyadic-extensive).** See `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square` and
  `f-ea-endpoint-localization-certificates-stall` (both ESTABLISHED, unrefereed).
  - *Normal form.* Let `κ(m)` be the spectral gap of the switch-walk-switch operator rooted at `2^{−m}`. Then
    `κ(m) ≤ π²/(5m²)` unconditionally (the slope walk confined to a strip near `0`), and `κ(1) ≤ 20(4m−1)²κ(m)`
    (path comparison along `x_0^{−(m−1)}`). So this claim holds iff `liminf m²κ(m) = 0`, and fails iff the strip
    strategy is optimal up to a constant at every depth.
  - *Class killed.* A certificate that confines the walk to a linear endpoint zone of depth `W`, and then transports
    the root to `1/2` by path comparison (even through a chain of stages of Schreier length at least `4`), outputs
    `gap(1/2) ≤ c` with `c ≥ 8/225`. The confinement gain is `≍ W^{−2}`, and any comparison word for `δ_{1/2}` has
    length `≥ 2(W+1)`, so the exponents cancel.
  - *What remains.* A spectral proof must certify a rate at a root whose inverted orbit leaves both endpoint zones
    (where `F` acts non-linearly), or transport by something finer than letter-counting path comparison. By the
    Chabauty remark there, the endpoint zones are the only recurrent localizations, so no recurrence input is left
    for this step.
- **Group-ring transplant to the lamplighter decouples (2026-09-18, swarm-0917-w6-w6-f-pull; dead end, no
  file).** Let `L = Z^{(D)} ⋊ F` and `K[L] = K[t_x^{±1} : x ∈ D] * F`. `L` is locally indicable, so by the
  Kielak/Tamari criterion `K[L]` is Ore iff `L` is amenable. With `thompson-f-amenable-iff-dyadic-action-extensively-amenable`,
  that is iff `F` is amenable. The hope was that Ore pairs in `K[L]` are easier to settle than pairs in `K[F]`. They are not.
  - *Lamp-free pairs are the root problem.* `K[L] = ⊕_c K[F] t^c` is a free left `K[F]`-module, and
    `a(Σ_c u_c t^c) = Σ_c (a u_c) t^c`. So for `a, b ∈ K[F]`, `aK[L] ∩ bK[L] ≠ 0` iff `aK[F] ∩ bK[F] ≠ 0`,
    coordinate by coordinate, and Guba's `P_(d,m)` reappear unchanged.
  - *Lamp binomials are trivially Ore.* For `b = Σ_g β_g g` (coefficients may contain lamps), put
    `Y = {g⁻¹x : g ∈ supp b}` and `v = ∏_{y∈Y}(1−t_y)`. Then `b v = Σ_g β_g ∏_y(1−t_{gy}) g` has the left factor
    `1−t_x` in every term. These pairs therefore carry no information about `F`.
  - *Product witnesses.* Product-measure EA witnesses on `(Z/2)^{(D)}` have energy at least the capacity of
    their support, so they die by transience (`f-dyadic-action-is-not-recurrent`).
  - *Where it dies.* Every pair that is not trivially Ore reduces to a `K[F]` pair. The transplant adds no
    leverage beyond the root Ore route (`thompson-f-amenable-iff-group-ring-is-ore`) or its obstructions
    (`thompson-f-ore-obstructions-must-see-finite-support`).
- **Symbolic-dynamics transplant: full-group hosts reduce to orbit recurrence (2026-09-18,
  swarm-0917-w7-w7-f-pull; dead end, with one ESTABLISHED by-product).** The idea was to place `F` inside an
  amenable topological full group `[[H ↷ Y]]` (or a fragmentation of a minimal `Z`-action, or piecewise `BS(1,2)`
  maps) and inherit extensive amenability of `F ↷ D` from the host's orbit action.
  - *Dictionary.* `F ≤ [[H ↷ Y]]` makes each element of `F` move points a bounded distance in the `H`-orbital
    graphs. Every known amenability engine for full groups (Juschenko–Monod, Juschenko–Nekrashevych–de la Salle,
    Juschenko–Matte Bon–Monod–de la Salle, Nekrashevych fragmentations) takes as input recurrent orbital graphs, or
    graphs of subexponential growth.
  - *Where the recurrent engines die.* `thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs` already
    kills finitely supported symmetric recurrence on bounded-degree graphs. The remaining loophole was a host whose
    orbit chain is recurrent only for a heavy-tailed, infinitely supported or non-symmetric measure, possibly on an
    infinitely generated host. `f-prime-acts-trivially-in-every-measure-recurrent-action` (ESTABLISHED, unrefereed)
    closes it. For any countable `G`, any `θ : F → G`, any transitive `G`-set and any measure whose support generates
    `G` as a semigroup, recurrence of the induced chain forces `θ(F′)` to act trivially.
    - *Invariant.* The escape probability `P_x(T⁺ = ∞)`, written as a capacity.
    - *Mechanism.* Subordination to full support keeps the Green function comparable. Symmetrization cannot raise
      capacity, via the equilibrium-potential bound. Rayleigh comparison with `θ(S)` then carries the capacity to
      the Schreier network of `F`, where the base theorem applies.
    - *Consequence.* The mean inverted orbit is ballistic for every generating measure in every host where `F′`
      acts.
  - *Where the transplant dies.* A host that could still help must have transient orbital graphs on the orbits where
    `F′` acts, for every measure. Its extensive amenability must then be proved by rare-event inverted-orbit
    confinement (`f-dyadic-ea-iff-inverted-orbit-confinement`), and that is this claim again, transported by bounded
    displacement. Subexponential-growth hosts are already excluded by Chaudkhari
    (`thompson-f-confined-subgroups-fix-finite-sets`).
  - Two cheaper symbolic ideas also fail:
    - `F`-equivariant cellular automata on `A^D` are trivial, since each point stabilizer has two infinite orbits.
    - Witnesses from Markov random sets with bounded state space fail calibration already for `Z`.
