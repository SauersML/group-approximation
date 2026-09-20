---
rg: 2
id: thompson-f-is-not-hyperlinear
kind: claim
title: Thompson's group F is not hyperlinear
refuted_by:
  - thompson-f-is-hyperlinear
distinct_from:
  thompson-f-is-not-sofic: that is the Hamming statement, implied by this one.
  thompson-v-not-hyperlinear: that is nonhyperlinearity of V, implied by this one because F <= V.
---

**OPEN.** Thompson's group `F` admits no injective homomorphism into a tracial matrix ultraproduct.

**Equivalent form** (`thompson-f-hyperlinear-iff-relator-system-hs-unstable`): unitary almost-solutions
of the two relators of `F` almost commute, uniformly in the dimension.

## Attempts

- **Kazhdan mechanisms.** No instance: `F` has the Haagerup property
  (`a-t-menable-groups-have-no-rigid-compression-defect`).
- **Uniform stability.** Fournier-Facio--Rangarajan (arXiv:2301.03970) prove uniform stability of `F`
  for submultiplicative norms. That controls uniform defect, not the pointwise normalized-HS defect
  statement 3 needs.
- **Entropy-measure transplant: every counting tool stops at nonsoficity** (lane
  swarm-0917-w2-nh-pull-1, 2026-09-17). Dead as a route to this claim; the exact split is recorded as
  `thompson-f-not-hyperlinear-via-nonsoficity-and-frames`.
  - **Invariant.** The input of each tool is a finite set with an approximate action: a sofic
    approximation or model space counted in Hamming measure. This covers sofic entropy and covering
    exponents, Rokhlin-entropy maximality (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`),
    cellular-automaton and quantum cellular automaton surjunctivity (`sofic-groups-are-qca-surjunctive`),
    and Kun--Thom nonsofic actions (`groups-containing-kun-thom-pair-have-nonsofic-actions`). A unitary
    microstate yields such a set only through a basis that each `U_g` approximately permutes.
  - **Dying step.** Coupling one frame across the non-commuting generators `a, b`. For `F` nothing is lost
    in the permutation skeleton: monomial HS models have abelian normal soft kernel
    (`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`, clause 3), and every nontrivial normal
    subgroup of `F` contains the nonabelian `F'`. So frames for `F` are equivalent to soficity of `F`, and
    the transplant proves at most `thompson-f-is-not-sofic`. The missing step is exactly
    `thompson-f-hyperlinear-models-normalize-a-full-masa`, the frame problem at `F`. Exact
    finite-dimensional models are jointly diagonalizable, since `Rep_n(F) = Rep_n(Z^2)`, but they are not
    regular.
  - **Kun--Thom instance.** This needs an infranormal, non-normal pair of Kazhdan subgroups. `F` is
    Haagerup (`a-t-menable-groups-have-no-rigid-compression-defect`), so its Kazhdan subgroups are finite,
    and torsion-free, so they are trivial. The tool has no instance inside `F` at all.
  - **Action-level versions.** A non-embeddable Bernoulli crossed product `L^∞(X) ⋊ F` does not imply
    that `F` is non-hyperlinear, because it contains `L(F)` rather than embedding into it. The only
    permanence in the other direction, `gkp-connes-embeddable-generalized-wreath-permanence`, needs a sofic
    action, and for Bernoulli shifts that again needs soficity of `F`.
  - **Covering entropy.** It has no threshold short of emptiness of the microstate space
    (`atlas-entropy-and-cmi-stop-at-face-emptiness`), which is this claim itself.
  - **Calibration.** Spatial permutation models that follow `F` on `[0,1]` almost commute
    (`thompson-f-spatial-permutation-models-almost-commute`). So the natural geometric frame is
    degenerate, consistent with the dying step.
- **Reframing: germ-local (inverse-semigroup) unitary models** (d-nhg-p3, 2026-09-17). Dead as a route
  to this claim; the class-killing half is recorded as `thompson-f-germ-local-hs-models-almost-commute`.
  - **Class killed.** HS models with an approximately covariant dyadic frame `P_w` that is also
    approximately germ-local, `U_g P_w ≈ U_h P_w` when `g|_[w] = h|_[w]`. Such models satisfy
    `||U_c − 1||_2 ≤ 2η_loc + 2 sqrt(1/N + η_cov)`. This covers Koopman representations for every
    quasi-invariant measure, quasi-regular representations on orbits, Pythagorean (direct-sum Jones)
    representations, restrictions of `O_2` representations through `F ≤ V ≤ U(O_2)`, and every
    finite-rank almost-invariant compression of these.
  - **Invariant and dying step.** The invariant is germ-locality at the two end germs. Interior cylinders
    have `N` disjoint `x_0^3`-translates, so a central state gives them mass `≤ 1/N`. All frame mass sits
    on `[0^m] ∪ [1^m]`, where `F'` acts trivially by locality, so `t = 0` in
    `thompson-f-character-simplex`.
  - **Why this is not a route.** The intended reformulation was "every witness admits an approximately
    covariant frame, and covariant frames can be made local", which would prove this claim. It dies at
    the second clause. Covariance can always be arranged: if `σ_n` is a witness and `λ_n` are the
    `x_0`-ray permutation models, then `λ_n ⊗ σ_n` is a witness with approximately covariant frame
    `P_w ⊗ 1`. Its locality defect at `c` is about `||σ_n(c) − 1||_2`, however the frame is chosen
    among amplified frames. So "covariant ⇒ almost commuting" is equivalent to this claim, and
    "covariant ⇒ local" presupposes `t = 0`. A locality-extraction step cannot be proved without
    already knowing the answer.
  - **What it rules out for `thompson-f-is-hyperlinear`.** No witness is a compression of a
    direct-sum/Cuntz/Koopman representation. The only natural unitary families left are tensor-type
    Jones representations (Temperley–Lieb–Jones functors) and Koopman representations of generalized
    Bernoulli actions, which carry no evident germ-local frame.
- **Inverter biography: group-level permanence cannot reach `F`** (lane swarm-0917-w5-pull-nh-2,
  2026-09-17). Recorded as `thompson-f-in-permanence-closure-only-via-base-copy`.
  - **Invariant.** "Contains a subgroup isomorphic to `F`". It is preserved backwards by subgroups, directed
    unions, unrestricted products, extensions, graphs of groups with arbitrary edge groups, local embeddability
    and recurrent extensions.
  - **Consequence.** `F` lies in the permanence closure of amenable, LEA and LEF groups only if `F` is amenable.
    So if this claim is false and `F` is non-amenable, a hyperlinearity certificate must be a direct metric
    construction for `F`, or for a new base group containing `F`. It cannot come from gluing witnesses along a
    splitting, product or extension.
  - **New tool.** Relative property FA for `F`: every action on a tree fixes a vertex unless an edge stabilizer
    contains a copy of `F`.
  - **Not killed.** Quotients and metric ultraproducts, action-level permanence, and direct almost-representations.
    Those are where any refutation or proof of this claim must live.
- **Operator-algebra split: compression models see only the factorization property** (lane
  swarm-0917-w5-pull2-non-1, 2026-09-17). This is a decomposition, and the claim stays OPEN.
  - **Established.** `thompson-f-factorization-iff-ucp-models-separate`. `F` has Kirchberg's
    factorization property iff compressions `P pi(.) P` of honest representations of `F` by almost-invariant
    finite-rank projections can stay non-commuting.
  - **Proof ingredients.**
    - The Stinespring defect is subadditive.
    - Amenable traces form a face, because domination on `A (x)_max A^op` preserves vanishing on the
      min-kernel.
    - The character simplex turns any non-abelian amenable limit into amenability of `tau_reg`.
  - **Route.** `thompson-f-not-hyperlinear-from-llp-and-no-factorization` splits this claim into two
    independently failable premises: `thompson-f-full-c-star-algebra-has-llp` (lifting) and
    `thompson-f-lacks-factorization-property` (uniform collapse of compressions). Amenability of `F` would
    falsify the second. Hyperlinearity of `F` without the factorization property would falsify the first.
  - **Class obstruction.** Every attack through ucp or compression models dies at the same step. This
    includes Jones, Pythagorean, Cuntz `O_2`, Koopman and induced representations, and any ucp map on
    `C*(F)`.
    - A collapse theorem for the class proves exactly `thompson-f-lacks-factorization-property`.
    - The invariant is the gap between Connes-embeddable and amenable traces on `C*(F)`.
    - The dying step is lifting an arbitrary `R^omega`-valued homomorphism to ucp microstates. That step is
      LLP of `C*(F)`, or at least the conclusion of `llp-makes-hyperlinear-traces-amenable` for `tau_reg`.
    - Conversely, a compression-model proof that `F` is hyperlinear proves the factorization property. If
      `F` is nonamenable, that makes `C*(F)` nonexact (`nonamenable-factorization-groups-have-nonexact-full-cstar`).
- **Symbolic-dynamics transplant: shift-covariant (QCA/tensor-shift) models** (lane
  swarm-0917-w7-w7-nh-pull, 2026-09-17). Recorded as
  `thompson-f-exact-shift-covariant-models-force-amenability`. The claim stays OPEN.
  - **Ansatz.** `F` is an ascending HNN extension along the shift `phi`. So put `x_0 = a` and
    `x_1 = sigma(a)` for a trace-preserving endomorphism `sigma`. All relations of `F` then reduce to two
    relations on one unitary: `a* sigma(a) a = sigma^2(a)` and `a* sigma^2(a) a = sigma^3(a)`.
  - **Exact models die at injectivity.** A non-commuting exact model in a host `M` makes `L(F)` a direct
    summand of `pi(F)'' ⊆ M`. This uses the character simplex and Radon–Nikodym.
    - In `R`, or any injective host, exact models exist iff `F` is amenable.
    - In the Bernoulli algebra, finitely supported exact models are scalars.
  - **Approximate local Bernoulli models.** Defect `delta` on `L` sites forces
    `||[a, sigma a]||_2 <= (5^(L-1) - 1) delta`, so the support must grow like `log(1/delta)`. A
    non-commuting sequence would prove `thompson-f-is-hyperlinear`. An `L`-uniform linear bound would kill
    the class, but not prove this claim, since not every witness is known to be shift-covariant.
  - **Numerics.** `experiments/thompson-f-shift-covariant-2026-09-17/results.txt` is qubits, `L = 2, 3`,
    best found, uncertified. There, a commutator of `c` costs a defect of about `sqrt(2c)` at `L = 2`
    and about `sqrt(1.5c)` at `L = 3`. So `c` is roughly quadratic in the defect, well inside the proved
    linear ceiling. Two sizes cannot show a trend in `L`.
  - **Where it stops.** This is the same place as the entropy transplant: sites. Symbolic and QCA tools need
    a tensor-site structure, and exactness inside a hyperfinite site algebra is amenability. What remains
    is quantitative: the propagation constant of the site-peeling step as `L` grows.
- **Census computation: large-dimension defect profile with calibration** (lane swarm-0917-w19-w19-nh-pull,
  2026-09-19). Recorded as `thompson-f-fixed-dimension-constants-exceed-four`. The claim stays OPEN. Its only
  numerical support, apparent saturation of `C_n`, is gone.
  - **Certified growth.** Exact `Q`-arithmetic certificates give `C_16 >= 3.536`, `C_32 >= 3.98`,
    `C_64 >= 4.23` and `C_128 >= 4.45`. The previous record was `3.2286`. This claim is exactly `sup_n C_n < infinity`, and the reading
    of "saturation near 3.23" (the `n = 6` search was worse than `n = 4`) was a search artifact.
  - **Why earlier searches stalled.** Direct-sum mixing with trivial blocks gives
    `tau/C_n^2 <= D_n(tau) <= tau rho/sigma` along multiples of the witness dimension. So a floor
    `e(c) >= tau` below the witness separation only rescales the best ratio. The growth appeared only at floor
    `tau = 1.8`, with dimension doubling seeded by block copies. Along the doubling ladder, `C^2` is roughly
    `2 + 2.6 log_2 n` for `n <= 128`.
  - **Calibration.** At `tau = 1.8` and `n = 16`, the best defects are:
    - `F`: `0.144`;
    - Baumslag--Gersten, sofic via permanence: `0.0033`, with an explicit `O(1/m^2)` spectral-matching family at
      separation `2 - 2/(m-1)`;
    - Higman's `H_4`, open: `0.06`.

    So `F`'s profile does not look like that of a permanence-closure group, and that is consistent with
    `thompson-f-in-permanence-closure-only-via-base-copy`.
  - **Where it dies.** Finite search only produces lower bounds on a monotone sequence. No amount of it proves
    boundedness, which is this claim, or even unboundedness. The lane cannot close this claim. What would matter is
    a structural reason for the `log n` growth of the doubling ladder: an explicit doubling map `m -> 2m` with
    `C_(2m)^2 >= C_m^2 + kappa`, which would prove `thompson-f-is-hyperlinear`. No mechanism for that is known.
    The certified witnesses keep `c ~ I` on about a third of the space. They are not perturbed block copies of
    their seeds: about `0.67` of their normalized mass lies off the seed's block diagonal at `n = 64` and `n = 128`.
    So a doubling map would have to couple the two copies, and a block-diagonal gluing will not do.
- **Census: tensor-shift ratio profile** (lane swarm-0917-w20-w20-nh-break, 2026-09-20). Recorded as
  `thompson-f-tensor-shift-pairs-have-bounded-commutator-ratio` (OPEN). Artifact:
  `experiments/thompson-f-shift-profile-2026-09-17/results.txt`. The claim stays OPEN.
  - **Question.** Can the tensor shift serve as the doubling map `m -> 2m` that raises the fixed-dimension
    constant `C = sqrt(e([X,Y]) / max e(R_i))`, as the w19 fixed-dimension-constant census (not yet on main) asks?
    The pair is `X = a ⊗ 1`, `Y = 1 ⊗ a` in `U(q^(L+1))`.
  - **Invariant (proved, elementary).** Take `L = 2` and suppose `a = u ⊗ v` is a product, with
    `u, v in U(q)`. The pair then factors site by
    site as `(u,1) ⊗ (v,u) ⊗ (1,v)`. Both relators and `[X,Y]` lie in `[F,F]`, so they are trivial on the
    two abelian factors. Since `tr_n` is multiplicative on tensor products, every `e`-value equals the
    value on the `U(q)` pair `(v,u)`, so `C ≤ C_q(F)`.
  - **Numerics (best found, uncertified; q = 2, L = 2..5, n = 8..64).**
    - The ratio optimum is `C = 2.3803` at every `L`, with `e(c) = 3.4201`.
    - Neither random restarts nor perturbations of size `eps ≤ 1` beat it by more than 0.6% (best 2.3935
      at `L = 4`).
    - The optimum is a product to 0.5% (op-Schmidt `[2, .0106, 0, 0]`). Its `U(2)` factor alone gives
      `C = 2.3797`.
    - In the small-commutator regime (`||[X,Y]||_2 = 0.3`), `C = 0.76 / 0.85 / 0.99 / 1.01`.
    - The generic constants are `C_n ≥ 3.2286` for `n ≥ 4` and `C_128 ≥ 4.45`.
  - **Where it stops.** Tensor shifts are not the ratio-increasing doubling: the search collapses them onto
    one-site-product pairs, which are bounded by `C_q`. This leans toward the `L`-uniform bound left open
    in `thompson-f-exact-shift-covariant-models-force-amenability`. That bound is not proved. The missing
    step is to control non-product `a`, i.e. operator-Schmidt rank at least 2, uniformly in `L`.
