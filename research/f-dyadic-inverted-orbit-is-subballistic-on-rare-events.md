---
rg: 2
id: f-dyadic-inverted-orbit-is-subballistic-on-rare-events
kind: claim
title: The inverted orbit of a random walk on Thompson's F acting on the dyadic rationals is confined to o(n) points on events of only subexponentially small probability
distinct_from:
  f-dyadic-action-is-not-recurrent: that says the mean inverted orbit is ballistic, an established fact; this is the strictly weaker rare-event confinement, which is open and would prove extensive amenability.
  thompson-f-dyadic-action-is-extensively-amenable: that is extensive amenability of the dyadic action; this is its concrete probabilistic form via the inverted orbit, equivalent to it by f-dyadic-ea-iff-inverted-orbit-confinement.
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
  - experiments/f-dyadic-rare-confinement-2026-09-17/cloning.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_long.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_long.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/psl_return.py
  - experiments/f-dyadic-wobbling-calibrator-2026-09-17/wobbling_tree.py
---

**OPEN.** Let `μ` be a non-degenerate symmetric finitely supported probability measure on `F` with
generating support, `x_0 ∈ D`, `g_n = h_n⋯h_1` the left random walk, and
`O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}` the inverted orbit. Then for every `ε > 0`,

`P(|O_n| < ε n) > e^{−ε n}` for infinitely many `n`.

Equivalently, `E(2^{−|O_n|})` decays subexponentially. By `f-dyadic-ea-iff-inverted-orbit-confinement` this
does not depend on `μ` or `x_0`.

**Status of the two directions.**
- A proof of this claim gives `thompson-f-dyadic-action-is-extensively-amenable`
  (`f-dyadic-ea-from-inverted-orbit-confinement`), hence co-amenability of Jones' subgroup
  (`jones-subgroup-is-co-amenable-in-thompson-f`), answering Aiello–Brothier–Conti Remark 4.7 positively.
- A refutation — a genuine exponential upper bound `E(2^{−|O_n|}) ≤ e^{−cn}`, equivalently exponential decay
  of the switch-walk-switch return probability on `(Z/2)^{(D)} ⋊ F` — proves `F` is not amenable.

**Why it is hard.** The mean is ballistic, `(1/n) E|O_n| → P(T=∞) > 0`
(`f-dyadic-action-is-not-recurrent`), so the confinement is a large-deviation statement: the trajectory
of the inverse walk must, with only subexponentially small probability, stay confined to a vanishing
fraction of the dyadics it would typically escape through. This is a spectral-radius / cogrowth question
for the dyadic lamplighter, of the same order of difficulty as the unsettled cogrowth numerics for `F`
itself (recorded in `research/artifacts/ideas-wildcards-2026-09-14.md`).

## Attempts

- **Calibration against PL worlds (2026-09-17, e-f-calibrate, swarm-0917, family calibration).** Result:
  `pl-ea-calibrators-are-nonamenable-interval-groups` (ESTABLISHED).
  - For every countable PL interval or circle group `G` with breakpoints, `G` is amenable iff `G ↷ B(G)` is
    extensively amenable. The proof uses real-valued breakpoint lamps.
  - Every orbit action of a subgroup of `PL_+([0,1])` is amenable, through the germ group at the infimum of the
    orbit.
  - A PL circle group has an amenable orbit action only if its rotation number is a homomorphism whose kernel
    fixes a point.
  - Consequence for this hole:
    - `T` (and any PL circle world with a free subgroup) fails confinement already because its orbit action is
      nonamenable. It is not a meaningful counter-calibration for the large-deviation question here.
    - A PL world that is amenable but not EA on breakpoints exists iff `PL_+([0,1])` has a nonamenable subgroup.
    - A confinement proof built only from properties shared by all breakpoint actions of `PL_+([0,1])` groups
      would prove all of them amenable. It must use an input specific to `F` (dyadic arithmetic, finite
      presentation, specific generators), and no PL world can currently test such an input.
  - This claim stays **OPEN**.

- 2026-09-17 (e-f-scale, swarm-0917, scale-shifter): **quantifier shift, decomposition, class kill,
  numerics.** Established node: `f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent`. This claim stays
  OPEN.
  - **One number instead of a quantifier.**
    - `E 2^{−|O_n|} = ⟨(1_E P 1_E)^n 1_E, 1_E⟩`, where `P` is the Koopman operator of the Bernoulli shift
      `F ↷ {0,1}^D` and `E = {ω(1/2) = 0}`.
    - So the exponent exists and equals `−log ‖1_E P 1_E‖`. This claim is equivalent to `‖1_E P 1_E‖ = 1`,
      and also to almost invariant sets inside the cylinder `E`.
  - **Two-sided bounds.**
    - Upper: the exponent is at most `−log ρ(F)`, which is `≤ 0.10366` for simple random walk by
      `thompson-f-norm-bound-from-hhr-exact-moments`.
    - Lower: `−log((1+ρ_0^+)/2)`, where `ρ_0^+` is the top spectrum on nonempty Walsh levels. It squeezes the
      exponent whenever finite-set stabilizers are amenable.
  - **Decomposition into prerequisites that can fail.**
    - The band exponents `λ_C = limsup P(O_n ⊆ D_C)^{1/n}` are survival rates of finite killed chains
      `T_i = h_iT_{i−1}`, with `λ_C ≤ ‖1_E P 1_E‖`.
    - Dyadic depth grows by at most 1 per generator, so `λ_{R+2}` is at least the Perron eigenvalue of the
      walk confined to the Cayley ball `B_R`.
    - Hence `F` amenable ⟺ `λ_C → 1`. Each `λ_C` can be `< 1`; they all stay bounded away from 1 only if `F`
      is nonamenable.
  - **Correction to `research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md`.** Its "rate that
    does not go to 0 with the band" is equivalent to nonamenability of `F`, so it is not an established
    obstruction. The multi-scale nesting of bands is unnecessary.
  - **Dead class: Walsh-level spectral gaps.** They cannot show this claim fails.
    - On `ℓ²(P_k(D))` the top of the spectrum is 1 for every `k`. The witnesses are the `k`-subsets of the
      ray `{2^{−j}}_{j≤N}`, which `x_1` fixes and `x_0` shifts.
    - Every sector-by-sector bound on `⟨Pf_0,f_0⟩` therefore gives only exponent `≥ 0`. A positive exponent
      must come from the toggle coupling `f̂(A) = f̂(A Δ {1/2})` between neighbouring levels.
    - The amenable-stabilizer squeeze is unavailable, because finite-set stabilizers contain copies of `F`.
  - **Numerics.** Scripts are in `experiments/f-dyadic-rare-confinement-2026-09-17/`, with bounded runtime.
    - `F`: exponent estimate 0.058 at `n = 1000` and 0.046 at `n = 4000` (late windows about 0.042). Band
      rates for `C = 2..8`: 0.34, 0.20, 0.15, 0.11, 0.087, 0.082, 0.06.
    - Calibrator `PSL_2(Z) ↷ P¹(Q)`: not extensively amenable, so its exponent is provably positive. Its
      estimates (0.047 late) and ball-band rates (down to 0.045 at 110 points) decrease the same way.
    - `F_2` on itself: estimate 0.298, above the rigorous ceiling 0.1438.
    - `Z³` and the lamplighter on themselves: estimates 0.19 and 0.12, where the true value is 0.
    - Verdict: finite-size cloning at these sizes cannot tell which way this claim goes.
  - **Where it stops.** No lower bound on `‖1_E P 1_E‖` beyond `ρ(F)` and no upper bound below 1 is proved.
    The open step is to build almost invariant sets inside `E` (positive direction), or to control the
    toggle coupling across Walsh levels (negative direction).

- **Last-mile audit, then a rate kill (2026-09-17, swarm-0917-w6-w6-f-last2, quantifier-shift).**
  - *Closest route.* This hole is the only open prerequisite on `thompson-f-amenable-via-dyadic-extensive-amenability`,
    the route into `thompson-f-is-amenable` with the fewest open prerequisites. But it is equivalent to the root
    (`thompson-f-amenable-iff-dyadic-action-extensively-amenable`), so "last missing" here means the root itself.
  - *Second route.* `thompson-f-amenable-via-exotic-co-amenable-subgroup` has two open prerequisites, and its first
    one refutes the Brin–Sapir conjecture. Every sandwich split collapses by
    `f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic`, and algebraic EA certificates die by
    `f-ea-calculus-certificates-force-f-prime-to-act-trivially`. So no route is closer than the analytic target.
  - *Established,* `f-dyadic-confinement-witness-times-match-folner-function`. Let `e ∈ supp μ`, and let
    `N_μ(ε)` be the least `N` with `P(|O_N| < εN) > e^{−εN}`. Then
    `log₂ Føl_Γ(1/η) / O(log²(1/η)) ≤ N_μ(ε)` whenever `ε ≤ η²/polylog(1/η)`, and `N_μ(ε) ≤ 2⌈4 Føl_Γ(8/ε)/ε⌉`.
    - *Lower bound.* An almost invariant lamp law `f²` comes from a good return ratio of the switch-walk-switch
      chain. Conjugated switches and unions of independent lamp sets make it a breakpoint-covering measure. The
      box and cocycle push of `thompson-f-dyadic-ea-witnesses-need-tower-size-proof` turns that into a Følner set.
    - *Upper bound.* A Følner set `U` lifts to `{(φ,g) : g ∈ U, supp φ ⊆ Ux_0}` in the lamplighter, and a spectral
      lower bound on its return probability follows.
    - *Credit.* The Moore instance, tower-size witness times, was obtained independently by swarm-0917-w6-w6-f-last1
      (`f-dyadic-inverted-orbit-confinement-needs-tower-times`, uniform `μ` at the root `1/2`). This node answers that
      sibling's spark about the tetration survivor band.
  - *Invariant.* The witness-time function `N_μ(ε)`, compared with `log Føl_Γ`.
  - *Class killed.* Passing to this hole in order to get a target quantitatively cheaper than Følner sets. Every
    certified witness time is a certified Følner bound one exponential up (Step 5 of the proof). So effective
    confinement proofs, and trap strategies bounded by a fixed tower, die against Moore's bound.
  - *Dies at / survives.* The hole stays OPEN. The survivor band is exactly the Følner band: if `F` is amenable,
    `N_μ(ε) ≤ Føl_Γ(8/ε)/ε`. So the hole is quantitatively the Følner problem, and no reduction through it can buy
    more than one exponential.

- 2026-09-17, swarm-0917-w6-w6-f-last1 (family probability-random): quantitative class kill, the hole stays OPEN.
  The spectral route `f-dyadic-inverted-orbit-confinement-needs-tower-times-proof` works for `μ` uniform on
  `{e, x_0^{±1}, x_1^{±1}}` and `x_0 = 1/2`. Take a good return ratio of the switch-walk, project onto
  root-switch invariant functions, take a union of `r` samples, and apply
  `thompson-f-dyadic-ea-witnesses-need-tower-size`. This proves
  `f-dyadic-inverted-orbit-confinement-needs-tower-times`:
  - `E 2^{−|O_{2n}|} ≤ exp(−n C^{−2 log* n − O_C(1)}/O_C((log* n)²))` at every time;
  - the first `N` with `P(|O_N| < εN) > e^{−εN}` is at least a tower of height about `½ log_C(1/ε)`.
  Invariant: Moore's Følner tower, carried to finite dyadic sets by the breakpoint cocycle. Dying step: exhibiting
  the confinement time `n(ε)` or the lower-bound profile. Explicit times of bounded tower height die there, and so
  do profiles `exp(−n/g(n))` with `log g/log* n → ∞`, including stretched exponentials. The hole itself needs only
  a vanishing rate, and item 2 allows rates `C^{−2 log* n}`, so nothing here decides it.

- 2026-09-18, swarm-0917-w13-w13-f-pull (family host-geometry, calibration): class kill by a piecewise projective
  calibrator; the hole stays OPEN. Results: `piecewise-projective-groups-amenable-iff-breakpoint-action-ea`
  (JNS with recurrence replaced by extensive amenability on the singular orbits only) and
  `lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea`.
  - In Thurston's model `F = ⟨a, b⟩ ≤ H`, the breakpoint set is `B(F) = F·0 = Q` (Euclidean descent, checked in
    `experiments/lodha-moore-ea-calibrator-2026-09-17/orbit_of_zero.py`). The Lodha–Moore group
    `G_0 = ⟨a, b, c⟩ ⊇ F` has the same breakpoint set and orbit `Q`.
  - `G_0 ↷ Q` is transitive and hereditarily amenable but not extensively amenable. So for its inverted orbit,
    `P(|O_n| < εn) ≤ e^{−εn}` for some `ε > 0` and all large `n`: this is the exact negation of this hole, on the
    same set `Q` where `F` acts. For `F ↷ Q`, EA is equivalent to this hole.
  - Invariant: JNS inputs (1), (2), (4), hereditary amenability, finite presentation, no free subgroups, rational
    breakpoints, and translation germs. All are shared by `F ↷ Q` and `G_0 ↷ Q`. Dying step: any upgrade
    "hereditarily amenable plus this germ data ⇒ confinement". This corrects the remark in
    `pl-ea-calibrators-are-nonamenable-interval-groups` that finite presentability cannot currently be tested.
  - Survivors: `PSL_2(Z)` integrality (`c` has determinant 2), `C^1` regularity (killed as well if Lodha–Moore's
    unproved remark that `⟨t+1/2, b⟩` is nonamenable holds), and the specific relations of `F`.

- 2026-09-17, swarm-0917-w17-w17-f-last1 (family calibration, role calibrator): class kill by a wobbling
  calibrator with the same orbit metric; the hole stays OPEN. Result:
  `f-dyadic-orbit-geometry-cannot-force-extensive-amenability`.
  - Construction. The dyadics `φ(u) = .u1`, for reduced words `u` in the blocks `01, 011, 0111`, form a
    free tree inside `[1/4, 1/2]`. Prepending or stripping a block moves a point a bounded distance in the
    Schreier graph `Γ_D`, because an explicit element of `F` is affine between the two cylinders.
    Measured distances are at most 9 (`experiments/f-dyadic-wobbling-calibrator-2026-09-17/wobbling_tree.py`).
  - The three resulting involutions `σ_c` generate `Z/2 * Z/2 * Z/2`, acting freely on the tree. Put
    `G = ⟨x_0, x_1, σ_A, σ_B, σ_C⟩ ≤ W(Γ_D)`. Then:
    - the identity of `D` is bi-Lipschitz from `Γ_D` to the Schreier graph of `G`;
    - `G ↷ D` is transitive and amenable, with `x_0`-ray Følner sets in `(0, 1/8]`;
    - `G ↷ D` is not EA (restrict to the tree and apply JMBMdlS Lemma 2.1);
    - so the walk on `G` has `P(|O_n| < εn) ≤ e^{−εn}` for some `ε > 0` and all large `n`, the exact
      negation of this hole on the same orbit geometry.
  - Invariant: the orbital graph `Γ_D` up to bi-Lipschitz equivalence (so recurrence, growth,
    isoperimetry, resistance, return-probability class), and the wobbling group `W(Γ_D)` with arbitrary
    pieces.
  - Dying step: any implication "orbit graph of `F` in this class ⇒ confinement or EA". Any
    Juschenko–Monod-style proof that makes `W(Γ_D)`, or a full group with arbitrary pieces, act EA and
    then restricts to `F` dies there too.
  - Gate: order preservation. Every order-preserving element of `W(Γ_D)` is piecewise-`F` with finitely
    many pieces, so `W^+(Γ_D) ≤ PL_+([0,1])`. An order-preserving calibrator would therefore be a
    nonamenable subgroup of `PL_+([0,1])`, which is item 4(b) of
    `pl-ea-calibrators-are-nonamenable-interval-groups`.
  - Any proof of this hole must use that `F` acts by homeomorphisms, or finer data. The Liouville
    property is not a bi-Lipschitz invariant and is untouched.

- 2026-09-19, swarm-0917-w19-w19-f-last1 (family reframing, role survivor audit): the order gate collapses to
  the hole, and the named survivors are re-audited. The hole stays OPEN. Result:
  `f-dyadic-order-preserving-wobbles-are-locally-f`.
  - **Order gate.** `W^+(Γ_D) ≤ Q_2`, the group of homeomorphisms that are piecewise `x ↦ 2^k x + d`
    (`d ∈ Z[1/2]`) with rational breakpoints.
    - `Q_2` is a directed union of subgroups `Q_2^M`, whose breakpoints lie in `(1/M)Z[1/2]`, `M` odd.
    - `θ_M = τ_M ∘ (x ↦ Mx)` conjugates `Q_2^M` into `F`, with `θ_M(D) ⊆ D`.
    - EA passes through subgroups, invariant subsets, conjugacy and directed unions. So
      `F ↷ D` EA ⇔ `W^+(Γ_D) ↷ D` EA ⇔ `Q_2 ↷ D` EA ⇔ `F` amenable.
    - An order-preserving calibrator on the `Γ_D` geometry, or any `H ≤ Q_2` acting amenably but not EA
      on an invariant subset of `D`, exists iff `F` is nonamenable.
    - This replaces the w17 gate "a nonamenable subgroup of `PL_+([0,1])`" with "F is nonamenable".
      "Order preservation plus orbit geometry" is therefore not an independent survivor. With arbitrary
      wobbles it is killed by the w17 calibrator; with order it is the root.
  - **Status of the other survivors named above.**
    - `PSL_2(Z)` integrality is circular: `integral-piecewise-projective-groups-are-locally-subgroups-of-f`.
    - `C^1` regularity is killed through `G_{1/2}` in `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable`,
      item 2. This answers the w13 NEED items.
    - The "Liouville property" survivor of the w17 entry is not a positive ingredient:
      - finitely supported, finite-entropy and finite-breakpoint-moment walks on `F` are non-Liouville
        (`thompson-f-random-walks-are-not-liouville`, `thompson-f-finite-entropy-walks-are-not-liouville`,
        `thompson-f-finite-breakpoint-moment-walks-are-not-liouville`);
      - Liouville action criteria are recorded as unable to decide the question
        (`liouville-action-criteria-cannot-decide-thompson-f-amenability`).
  - **What is left.** Any proof must use data that a mean on `P_f(D)` cannot see after conjugation into `F`.
    Every order-preserving host tried so far (PL, integral projective, `W^+`) has turned out to be locally
    `F` or nonamenable. So the remaining content is `F`'s own relations: the large-deviation question
    itself, with no enlargement shortcut.
