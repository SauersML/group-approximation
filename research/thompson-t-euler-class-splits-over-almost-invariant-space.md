---
rg: 2
id: thompson-t-euler-class-splits-over-almost-invariant-space
kind: claim
title: "There is a nonsingular Thompson T-space whose Koopman representation has almost invariant vectors and over which the Euler extension T-bar splits measurably (a real cocycle beta on T-bar with beta(z,.) = 1)"
distinct_from:
  lifted-thompson-t-is-a-t-menable: that is the Haagerup property of T-bar; this is a measure-theoretic statement about T that implies it through central-extension-haagerup-from-measurable-euler-splitting, and is not known to follow from it
  lifted-thompson-t-center-has-relative-t: that is the refuting statement for T-bar; this claim implies its negation, but its own failure refutes nothing
  thompson-t-orbits-carry-no-invariant-means: that kills counting measure on orbits in S^1; this asks for spaces that do not map to S^1 at all
artifacts: []
---

**Statement (MT).** There are:
- a standard σ-finite measure space `(X, μ)` with a nonsingular action of Thompson's `T`,
  whose Koopman representation `κ` has almost invariant unit vectors;
- a measurable `β : T̄ × X → R`, with `T̄` acting through `T`, satisfying the cocycle identity
  and `β(z, ·) = 1` a.e.

**Status.** OPEN.

## Role

- (MT) implies `lifted-thompson-t-is-a-t-menable`, by
  `central-extension-haagerup-from-measurable-euler-splitting`. `T` is Haagerup by Farley,
  `thompson-v-has-haagerup-property`. The route is
  `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting`.
- The failure of (MT) does not refute the target. Only a converse would make it necessary, and
  that converse is not established (see Remarks).

## Forced shape (established)

By `perfect-extension-splittings-are-not-uniformly-integrable`, for any witness `(X, μ, β)`:
- (F1) No subsequence of the almost invariant densities `ν_n = ξ_n² μ` makes all `β(g, ·)`
  uniformly integrable. In particular, `β` is not bounded, and if `μ` is an invariant
  probability then `β` is not in `L¹`.
- (F2) `X` admits no measurable `T`-equivariant map to `S^1`. Otherwise the bounded circle
  splitting pulls back, and Part 3 of that claim gives spectral gap.

So the circle, its orbits, and every space fibred over it are excluded. The Cantor set
`{0,1}^N`, with `T ≤ V` acting and the binary coding map onto `S^1` being equivariant, is
excluded too.

## Remarks (not established)

- *Converse, sketch only.* Suppose `T̄` has a cnd function `ψ` with `Σ_m e^{-ψ(z^m)/8} < ∞`. Then
  the nonsingular Gaussian action built from the affine action of `ψ` should make `z`
  dissipative. Its quotient by `⟨z⟩` should be a witness for (MT), with almost invariant
  vectors pushed down by fibrewise `ℓ²` norms.
  - The dissipativity criterion for nonsingular Gaussian actions, in the style of
    Arano–Isono–Marrakchi, was not read verbatim.
  - Boosting the growth of an arbitrary proper `ψ` on `⟨z⟩` failed. Spectral reweighting by
    `w(ρ(z))` needs a spectral-measure comparison that was not proved.
- The discrete special case is `thompson-t-co-amenable-subgroup-kills-real-euler-class`.

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): statement isolated; forced shape (F1) and (F2)
  proved; discrete special case split off. Not decided.
- 2026-09-18 (swarm-0917-w11-w11-nv-pull, operator-algebras): the probability-measure case of
  (MT) was reformulated, and the Bernoulli and Gaussian candidates were killed, conditionally.
  - *Reformulation.* For an invariant probability `μ`, the Koopman hypothesis is automatic,
    since `1` is invariant. So pmp (MT) says exactly that `e_R ↦ 0` in
    `H²(T; L⁰(X, R))` for some pmp `T`-space `X`.
  - *Universal space.* Equivalently, the following `T`-action has an invariant Borel
    probability. The space is `Q_0 = {q : T̄ → R : q(1) = 0, q(zg) = q(g) + 1}`. The action is
    `(h·q)(g) = q(gh) − q(h)`, on which `z` acts trivially.
    - Given `β`, the map `x ↦ β(·, x)` is equivariant into `Q_0`.
    - Conversely, `β(g, q) = q(g)` is a splitting over `Q_0`.
    - The displacement map `x ↦ (g ↦ g(x̃) − x̃)` embeds `S^1` equivariantly into `Q_0`.
      Invariant measures with integrable coordinates would have a barycentre fixed point, which
      is impossible. This recovers (F1) and (F2).
  - *Kill.* `thompson-t-bernoulli-euler-splittings-need-amenable-f` (ESTABLISHED as an
    implication): if `F` is nonamenable, no generalized Bernoulli space (over `T`, or over
    `T/PSL_2(Z)`, and so on) and no weakly mixing Gaussian space with spectral gap on `F_A`
    is a witness.
    - The proof untwists `e^{2πiθβ}` on the commuting pair `F_A × F_B` by Popa's
      spectral-gap theorem.
    - It then spreads the untwisting along overlapping arcs to all of `T̄`, and perfectness
      forces `e^{2πiθ} = 1`.
  - *Surviving pmp witnesses* must be non-Bernoulli and non-Gaussian over `F_A × F_B` (for
    example, with some `F_J` not weakly mixing), unless `F` is amenable.
- 2026-09-18 (swarm-0917-w13-w13-nv-last1): the converse sketched in Remarks is now
  ESTABLISHED, in corrected form, as `central-zero-poincare-exponent-gives-euler-splitting`.
  - If some cnd `ψ` on `T̄` has `Σ_m e^{−sψ(z^m)} < ∞` for **every** `s > 0`, then (MT) holds with
    an integer `β`. A single `s` is not enough, since almost invariance needs `ψ/j`.
  - The proof uses AIM Theorem B (`t_diss ≤ 2√(2δ)`, quoted verbatim), Prop. 4.9 for freeness, a
    fundamental domain for `⟨z⟩`, and a fibrewise `ℓ²` pushdown.
  - So (MT) sits between (SL), the new open node
    `lifted-thompson-t-has-cnd-with-zero-central-poincare-exponent`, and the Haagerup property of
    `T̄`: `(SL) ⇒ (MT) ⇒ T̄ Haagerup ⇒ ψ proper on ⟨z⟩`.
  - Route: `lifted-thompson-t-a-t-menable-via-central-poincare-exponent`.
  - (MT) itself is still OPEN.
- 2026-09-18 (swarm-0917-w13-w13-nv-pull, entropy-measure): new forced shape (F3), established as
  `thompson-t-euler-splitting-witnesses-are-asymptotically-free`. Not decided.
  - *(F3).* Along every almost invariant sequence, `ν_n(Fix g) → 0` for all `g ≠ e`.
    - Proof: the stabilizer laws of `ν_n` are almost conjugation invariant, so their limits are
      IRSs of `T`. The character simplex of `T` (only `1` and `δ_e`) forces each limit to be
      `a δ_T + (1 − a) δ_{e}`, with `a` the mass of the global fixed set.
    - The Euler normalization makes that fixed set null: there, `β(·, x)` would be a homomorphism
      `T̄ → R` with `z ↦ 1`, and `T̄` is perfect.
  - *Killed by (F3), not by (F2).* Witnesses with local stabilizers (every `g` trivial near a
    support `K(x)` fixes `x`) whose supports miss a fixed arc, have bounded cardinality, or fail to
    be `ε`-dense with mass bounded below. This includes all bounded-size configuration spaces of
    `S^1`.
  - *Limits of the method.* (F3) cannot decide (MT). A Bernoulli shift of `T` is free and
    probability-measure-preserving, so it satisfies (F2) and (F3), and the whole question sits in
    the cocycle.
    - For free pmp `X`, (MT) says that the integral Euler 2-cocycle of `T` becomes a coboundary
      in `L⁰(X, R)` coefficients, which is measurable cohomology of the orbit relation.
    - That reformulation is recorded, not proved equivalent in the nonsingular case.
  - *Discrete case, cross-check.* In the discrete case, (F3) reproduces the mean-free conclusion
    for co-amenable `H` reported on the bus by w10-nv-follow. Independently of w10 and w12, it was
    rechecked that `PSL_2(Z)` is not co-amenable in `T`:
    - the double cosets of `PSL_2(Z)` force `H ∩ gHg^{-1}` into the stabilizer of a finite
      breakpoint set, which is virtually cyclic;
    - item 4 of `mean-free-amenable-actions-residually-amenable-and-sofic` then applies.
    - Not written up, since it duplicates their entries.
- 2026-09-19 (swarm-0917-w14-w14-nv-follow, operator-algebras): new decomposition through
  symplectic Gaussian spaces, with one class killed. (MT) is still OPEN.
  - *Established lemmas.*
    - `symplectic-gaussian-actions-split-area-cocycles`: an affine `Sp_res` action whose area
      cocycle is `a·ε + dβ₀`, `a ≠ 0`, splits the extension measurably over each nonsingular
      Gaussian space `X_t`, with an explicit Paley–Wiener splitting.
    - `thompson-t-dirichlet-space-restricted-symplectic-model`: `PPSL_2(Z)` is `C^1`,
      so the smoothed `T` is Weil–Petersson and acts on `H^{1/2}/R` in `Sp_res`. Its displacement
      cocycle has area `−ε + dβ_A`, so `a = −1`.
  - *Decomposition.* (MT) ⇐ (G_aff),
    `thompson-t-affine-dirichlet-koopman-almost-invariant` (OPEN), via the
    route `thompson-t-euler-splitting-via-affine-dirichlet-gaussian`. The space and the splitting
    are explicit, and only the almost invariant vectors are missing.
    - (F2) would kill (G_aff) if some `X_t` mapped equivariantly to `S^1`. No such map is known,
      and none was looked for.
    - (F1) and (F3) become constraints (A3) and (A4) on the vectors.
  - *Kill.* `thompson-t-linear-gaussian-koopman-has-spectral-gap` (ESTABLISHED). The linear
    Koopman representation `κ₀` has no almost invariant vectors, so the "`t → 0` from `κ₀`" branch
    (part 3 of the lemma) is dead.
    - *Invariant:* `PSL_2(Z)` acts by Moebius maps, and its chaos representation is tempered, since
      it sits inside tensor powers of the weight-2 discrete series. This gives spectral gap on
      `1^⊥`.
    - *Step where it dies:* the non-Moebius element `g_0` moves the vacuum by a fixed Hellinger
      amount.
    - This answers negatively, in this model, the w13 spark on almost invariant vectors of
      `M ⊗ M̄` (the identification is a remark).
    - The cocycle is unbounded on `⟨P⟩`, so the kill does not reach `t ≠ 0`.
