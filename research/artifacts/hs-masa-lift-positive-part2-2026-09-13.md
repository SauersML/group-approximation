# Liftable masas of Kazhdan relative commutants, part 2: dominated at the Theorem E pair (2026-09-13)

Lane `ex-hs-masa-lift-positive`. Part 1: `research/artifacts/hs-masa-lift-positive-2026-09-13.md`.

## 1. Theorem 4: vertex rounding of one model normalizes that model

**Setting.** `Gamma = EL_r(R_+) < G = EL_r(L) x| SL_d(Z)`, with `R_+ = F_q[x_1..x_d]`,
`L = F_q[x^(+-1)]` and `r, d >= 3`: the explicit Theorem E pair. Let `sigma : G -> U(prod_U M_n)` be
trace-preserving and satisfy (H1) *for this one model*, with rounding representations `pi_n`.

**Claim.** `sigma(G)` normalizes `sigma(Gamma)' cap prod_U M_n`.

*Proof.* Every premise below is stated for one `sigma` with (H1) roundings. None quantifies over
models.
1. **Finite images.** By item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
   `pi_n` factors through `St_r(R_+/I_n)`, and `R_+/I_n = A_u x A_nu`. Let `P_n` be the projection onto
   the constituents trivial on `St_r(A_nu)`.
2. **Projection bound.** By `nonunit-projection-bounded-by-root-spectral-mass`,
   `tau(1 - P_n) <= r(r-1) mu_n(chi|A_nu != 1)`. Also `chi|A_nu != 1` iff `depth_nu(chi) >= 1`.
3. **Root mass.** Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` gives
   `mu_n(depth_nu = 1) <= q eta_n + eta_n^t -> 0`. `vertex-rounding-deep-nonunit-root-mass-vanishes`
   gives `mu_n(depth_nu > 1) -> 0`. Both limits are along `U`.
4. **Normalization.** So `tau(1 - P_n) -> 0`. Items 3-4 of the rigidity claim give
   `eps_n <= 4 tau(1 - P_n)^(1/2) -> 0`, hence (CCR) for each nonnegative strict compressor, and
   normalization. ∎

These are steps 1-3 of route `theorem-e-vertex-unit-type-via-deep-root-mass`, read for one model.

## 2. What this does to the liftable-masa input

- **Dominated at this pair.** `hs-vertex-rounding-and-liftable-masa-force-normalization` assumes
  (H1) and (LM) for one model and concludes normalization. At the Theorem E pair, (H1) alone
  concludes it.
  - The route `hs-normalization-via-vertex-rounding-and-liftable-masa` consumes (LM) for nothing here.
  - The unit-type chain `theorem-e-vertex-unit-type-via-deep-root-mass` ->
    `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` needs only (H1).
- **Exact consequence for `non-hyperlinear-group`, through the unified theorem.** By
  `kazhdan-commutant-compression-stability-is-finitary`, `UCS_HS(F, {A, B})` at the pair is
  equivalent to normalization for every homomorphism, with any trace.
  - Here "trace-preserving" means `tau o sigma = delta_e`, as in
    `theorem-e-congruence-projections-vanish-at-regular-trace`. The Section 1 premises are stated for
    such models.
  - For `non-hyperlinear-group` only such models matter, because a hyperlinear embedding of the
    wreath restricts to one. (H1) at them gives normalization at them.
  - (LM) adds nothing to this implication. The step to `UCS_HS` itself needs the premises at arbitrary
    traces, which is not checked here.
  - The remaining input on this chain is (H1) for every model at the Theorem E pair: the Theorem E
    instance of `hs-stable-vertex-rounding-for-every-model`. Read in general form, that claim is
    false at the Fournier--Facio pair, and the instance is unaffected.
  - The review status of the four premises in Section 1 is the only other dependency.
- **Readoff of the three faces.** In the Hilbert--Schmidt row at the Theorem E pair, once rounding
  (R) holds, localization (L) comes from the arithmetic of the actor, not from a masa:
  - the Laurent torus element `t` removes shallow non-unit mass;
  - the two compressor attractors remove deep mass.

  The necessity remark of the unified artifact (Section 3) concerns the one-compressor group
  `<Gamma, t>`, which has no torus. That is consistent with this readoff.
- **Where (LM) is still meaningful.**
  - *Other pairs.* Theorem 2 of the unified part 2 holds for every infranormal Kazhdan pair, so (LM)
    matters at pairs with no congruence or torus mechanism.
  - *The nine-leaf Leavitt pair.* (H1) is itself equivalent to the target there
    (`leavitt-pair-vertex-rounding-is-nonhyperlinearity`), so the masa input is moot too.
  - *As a structural question.* By part 1, (LM) for every model of `G` is the `Pi^0_3` partition
    inequality `DEC_kappa`.

## 3. The shape of `Q` under (H1) at this pair (recorded, not pursued)

Under (H1), Theorem 4 makes `alpha_g = Ad sigma(g)` an automorphism of `A = sigma(Gamma)' cap M`.
- `alpha_gamma = id` for `gamma in Gamma`.
- Therefore `alpha_(g gamma g^-1) = id`, and `alpha` factors through `G / <<Gamma>>`.
- `<<Gamma>>` contains `EL_r(L)`. Every `x^v` is `M . x_1^m` for some `M in SL_d(Z)`, because
  `SL_d(Z)` is transitive on primitive vectors.
- So `G / <<Gamma>> = SL_d(Z)`, and `Q = sigma(G)' cap M` is the fixed-point algebra `A^(SL_d(Z))`.
- `A = prod_U A_n` with finite-dimensional `A_n` (item 1 of
  `vertex-rounding-reduces-ccr-to-commutant-excess`). So (LM) here is a Kun-type problem: an
  approximate `SL_d(Z)`-action on isotypic labels, with finite-dimensional multiplicity fibres.

No step of the non-hyperlinear chain consumes it.
