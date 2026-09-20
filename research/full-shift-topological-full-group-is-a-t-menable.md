---
rg: 2
id: full-shift-topological-full-group-is-a-t-menable
kind: claim
title: "The topological full group of the two-sided binary full shift has the Haagerup property"
distinct_from:
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's theorem for one-sided shifts of finite type, where the groupoid is expansive in one direction and zipper actions exist; this is the two-sided full shift, whose full group sits inside 2V, which embeds in no zipper group
  full-shift-full-group-kazhdan-subgroups-are-finite: that proves the weaker consequence that Kazhdan subgroups are finite; this asks for a proper cnd function
  brin-thompson-groups-nv-are-a-t-menable: that is the goal for nV; this is a necessary prerequisite of it that lives in the measure-preserving subgroup M_2 of 2V and can fail on its own
---

**OPEN.** `X = {0,1}^Z`, `σ` the shift, and `[[X]]` is the group of homeomorphisms
`f(x) = σ^{k_f(x)} x` with `k_f: X → Z` continuous. The claim: `[[X]]` has a proper
conditionally negative definite function.

## Role

This claim is necessary for `brin-thompson-groups-nv-are-a-t-menable`, by the route
`full-shift-full-group-a-t-menable-from-nv`: `[[X]] ≤ 2V ≤ nV`. By
`nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 3(c), the copy of `[[X]]` lies in the
Jacobian subgroup `M_2`. So it is invisible to the half (Q_J) of the goal, and it tests only the
part of the goal that is "proper on `M_n`". A refutation here refutes the Haagerup property of every
`nV` with `n ≥ 2`.

## Known

- **Kazhdan subgroups are finite** (`full-shift-full-group-kazhdan-subgroups-are-finite`).
- **Residually finite** (`full-shift-topological-full-group-is-residually-finite`).
- **Contains every right-angled Artin group** (`every-raag-embeds-in-full-shift-topological-full-group`).
  So it contains `F_2 × F_2` and is not amenable.
- **It is a subgroup of the wobbling group of `Z`.** Let `x*` have a dense `σ`-orbit, and identify
  the orbit with `Z` through `j ↦ σ^j x*`. Each `f ∈ [[X]]` acts on it with displacement at most
  `max|k_f|`, and the action is faithful because the orbit is dense. So `[[X]] ↪ W(Z)`, the group
  of bijections of `Z` with bounded displacement. Haagerup for `W(Z)` would imply this claim.
- **No relative-(T) pair built from exponential distortion.** Every orbit ball satisfies
  `|B_S(x, R)| ≤ 2rR + 1`, where `r` bounds the displacement of the generators. By the orbit
  pigeonhole of `subexponential-schreier-growth-excludes-sl3z-and-bs1k` (item 1), no element of
  infinite order is exponentially distorted in a finitely generated subgroup. So `Z^2 ⋊ SL_2(Z)`,
  whose `Z^2` is exponentially distorted, does not embed, and the standard relative-(T) witness to
  non-Haagerup is not available inside `[[X]]`.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-nv-last1): invariant-measure walls (die; class-kill).**
  - *Class.* `ψ = Σ_k w_k ψ_{ν_k}` with `w_k ≥ 0`, each `ν_k` a `σ`-invariant σ-finite Borel measure,
    and `ψ_ν(g) = ∫ |k_g| dν`. Each `ψ_ν` is cnd. On `X × Z` with `ν ⊗ counting`, let `g` act by
    `(x, t) ↦ (gx, t − k_g(x))`. Every `g ∈ [[X]]` preserves every `σ`-invariant measure, being `σ^k`
    on the pieces of a clopen partition with disjoint images. So `ψ_ν(g)` is the measure of
    `g A Δ A` for the half-space `A = {t ≥ 0}`. The class includes the Maharam wall `ψ_M` of
    `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 6(c), restricted to `[[X]]`: under
    `Φ`, Lebesgue measure `λ` becomes the Bernoulli(1/2, 1/2) measure, and `c_1 = −k`.
  - **Reduction.** `k_σ ≡ 1`, so `ψ(σ) = Σ_k w_k ν_k(X)` must be finite. So `ψ = ψ_ν` for the single
    finite invariant measure `ν = Σ_k w_k ν_k`.
  - **Where every member dies.** Choose an aperiodic `x*` with `x*_0 ≠ x*_1`, and let
    `E_m = {x : x_{[−m,m]} = x*_{[−m,m]}}`. Then `E_m ∩ σE_m = ∅`, since a point of both has
    `x_0 = x*_0` and `x_0 = x*_1`. Let `g_m` be `σ` on `E_m`, `σ^{-1}` on `σE_m` and the identity
    elsewhere. This is an involution in `[[X]]`, and the `g_m` are pairwise distinct. Then
    `ψ(g_m) = ν(E_m) + ν(σE_m) = 2ν(E_m) → 2ν({x*}) = 0`: a finite invariant measure has no atom at
    an aperiodic point, because the infinitely many points of its orbit would carry equal mass. So
    `{ψ ≤ δ}` is infinite for every `δ > 0`, and `ψ` is not proper.
  - **Invariant:** invariant measures do not see deep cylinders around aperiodic points.
  - **Surviving:** cnd functions that are not integrals of `|k_g|` against invariant measures, for
    example measured walls over non-invariant but quasi-invariant data, or walls on the orbit space
    `Z` that weight boundary points by local pattern complexity.
- **2026-09-19 (swarm-0917-w16-w16-nv-last1): periodic-point sums (die).** `ψ = Σ_p w_p ψ_p`, where
  `ψ_p(g) = Σ_{x ∈ Per_p} |k_g(x)|` sums over the finite set `Per_p` of points of least period `p`.
  Then `ψ_p = ψ_{ν_p}` for the counting measure `ν_p` on `Per_p`, which is finite and invariant. So
  this is in the class above, and it dies by the same involutions `g_m`. (Finiteness of `ψ(σ)` forces
  `Σ_p w_p |Per_p| < ∞`.)
- **2026-09-19 (swarm-0917-w17-w17-nv-last1): refutation by normal relative-(T) pairs (class-kill
  outside positive characteristic).**
  - *Class.* Refutation witnesses `(Γ, H)` with `Γ ≤ [[X]]`, `H ⊴ Γ` infinite and `(Γ, H)` relative
    (T). This is the CSV Cor 1.2 / Burger pattern `R² ⋊ EL_2(R)`, and it includes quotients of
    Haagerup wreath products by base submodules, such as Salo's lamplighter subgroups of `[[X]]`.
  - **Result.** `wobbling-normal-relative-t-subgroups-are-locally-finite` (ESTABLISHED, for every
    subgroup of `W(Z) ⊇ [[X]]`) proves that such an `H` is locally finite.
  - **Invariant:** the one-dimensional orbit geometry. Every element of `Γ` moves points of a
    `σ`-orbit by a bounded amount.
  - **Where every member dies.**
    - Interval vectors `L^{-1/2} 1_I ∈ ℓ²(Z)` are almost invariant. Normality makes the relative
      projection `Γ`-equivariant, so it has a quantitative form. Hence at most a `2δ²` fraction of
      each long window lies in `H`-orbits larger than `2L`.
    - A large orbit of a finitely generated `H' ≤ H` has bounded gaps, so it fills a positive
      fraction of some window. This bounds the `H'`-orbits, and `H'` is finite.
    - So every characteristic-zero witness `R² ⋊ EL_2(R)` is excluded, and so is any witness whose
      normal part contains `Z`. The earlier distortion exclusion only removed exponentially
      distorted ones.
  - **Surviving:** a locally finite normal `H`. The candidate is `EL_2(F_p[t,t^{-1}]) ⋉
    F_p[t,t^{-1}]²`, recorded as the new failable node
    `full-shift-full-group-has-infinite-normal-relative-t-subgroup`. A proof of that node refutes
    this claim and the goal.
  - Non-normal relative-(T) subsets survive as well. Removing normality needs Jolissaint's
    quantitative relative (T), which was not checked verbatim.
  - *Side observation, not proved in a node.* For the basic Salo module `A[G]/J ⋊ G`, the
    orbit-indicator characters form an amenable `G`-set, because `W(Z)`-orbits have linear growth.
    The permutation representation on them therefore has almost invariant vectors and no
    base-invariant vector. So that module fails relative (T) directly.
- **2026-09-19 (swarm-0917-w17-w17-nv-follow): the overgroup `M_2` is `RTM(2,1)`; where the
  cubical kill switches on (calibration plus new prerequisite).**
  - **Result.** `lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group` (ESTABLISHED).
    - Under `Φ`, the Lebesgue-preserving subgroup `M_2 ⊇ [[X]]` of `2V` is exactly the
      moving-tape group `RTM_fix(2, 1)`: a Jacobian-zero brick table on `(r, r)`-bricks is a
      Turing-machine local rule, and conversely.
    - So Callard–Salo's Theorem D places an element with `|f^N| = O(log^4 N)` in `M_2`. That
      answers the question left open in `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`.
    - It follows that `M_n` has no proper commensurating action, and the "proper on `M_n`" half
      of the Jacobian split has no cubical witness.
  - **Calibration for this claim.** `[[X]]` embeds in `W(Z)` by a dense orbit, so by item 3 of
    `heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs` (`d = 1`) it has no distorted
    element.
    - So the Callard–Salo/Haglund cubical kill does not reach this claim. Cubical and
      commensurating proofs of it remain open.
    - It does reach the intermediate group `RTM(2, 1)`. The kill switches on exactly when tape
      overwriting (homoclinic moves) is added to the shift.
  - **New prerequisite.** `reversible-turing-machine-groups-are-a-t-menable` (OPEN).
    - It is necessary for the goal via `turing-machine-group-a-t-menable-from-nv`.
    - It is sufficient for this claim via `full-shift-full-group-a-t-menable-from-turing-machines`.
  - **Not done.**
    - No cnd function on `[[X]]` was constructed.
    - Whether the Callard–Salo element (or any distorted element of `M_2`) has a power in
      `[[X]]` is not decided. If one had, the relative capture lemma would make every cubical
      function on `M_2` that is proper modulo `[[X]]` impossible to rule out by this route.
- **2026-09-19 (swarm-0917-w19-w19-nv-break): refutation by any relative-(T) subgroup pair
  (class-kill, host-geometry).**
  - Normality is removed from the w17 kill.
    `relative-t-subgroup-pairs-have-uniform-invariant-projection` imports Cornulier's Theorem 2.2.3
    (arXiv:math/0505193), checked verbatim: for a countable group, relative (T) of a subgroup or a
    subset gives uniform convergence of positive definite functions on it. With the lemma of the
    centre, this gives the quantitative projection that w17 derived from normality.
  - Hence `wobbling-relative-t-subgroups-are-locally-finite`: in every subgroup of `[[X]]` (indeed
    every countable subgroup of `W(Z)`), every `H` with `(Γ, H)` relative (T), normal or not, is
    locally finite. Examples are non-normal copies of `Z`, of surface groups and of free groups.
  - *Where every member dies.* The invariant is the uniform almost invariance of interval vectors
    in `ℓ²(Z)`. Each member dies at the bounded-jump density count: an orbit of a finitely generated
    subgroup with jumps at most `c` is `c`-dense in its span.
  - *Survivors.*
    - (S1) Infinite locally finite `H`. The candidate is `Γ_p`, now possibly with a non-normal `H`.
    - (S2) Subset witnesses that generate no relative-(T) subgroup. Cornulier's
      `SO_n(Z[2^{1/3}]) ⋉ Z[2^{1/3}]^n`, `n = 3, 4`, shows that these occur. For (S2) only the
      necessary shape `|xI Δ I| < δ²|I|` (uniform in `x ∈ X`, for long intervals) is derived.
  - Status of this node: still OPEN. The TH alternative is open in general.
- **2026-09-20 (swarm-0917-w20-w20-nv-last1, host-geometry): witnesses extended from the orbit
  wobbling group (die; class-kill).**
  - *Class.* `ψ = ψ̃ ∘ ι`, where `ι: [[X]] → W(Y)` restricts to any σ-invariant set `Y` of aperiodic
    points (one dense orbit, several, or all of them), and `ψ̃` is any cnd function on the whole
    orbit wobbling group `W(Y)`. This includes half-line commensurating actions, wall sums over
    orbit cuts, and finite sums of pullbacks along several orbits. It also answers the Known remark
    that "Haagerup for `W(Z)` would imply this claim": that hypothesis is not merely unproved, it
    is false in the strongest sense.
  - **Result.** `wobbling-group-cnd-functions-are-bounded-on-displacement-balls` is ESTABLISHED,
    with Cornulier 2006 imported verbatim. Every cnd function on `W(Y)` is bounded on each
    displacement ball of constant flux. The flux of `ι(g)` is a continuous σ-invariant function,
    hence constant.
  - **Invariant.** The displacement bornology is bounded for every Hilbert action. The route is
    flux, then a factorisation as a product of two block permutations, then `S_L^J ⊆ A_L^J · A_{2L}^J · A_{2L}^J`
    with each factor strongly bounded.
  - **Where every member dies.** On the involutions `g_m ∈ B_1` above, which have
    `‖k_{g_m}‖_∞ = 1`.
  - **Surviving.** Cnd functions on `[[X]]` that do not extend to `W(Y)`, such as countable orbit
    sums `Σ_i ψ_i ∘ ι_i` whose bounds on `B_r` diverge but which are finite on `[[X]]`. Any proper
    witness must use the continuity of the local rules `k_g`, that is, the coherence of the action
    across orbits, and not only bounded displacement along each orbit.
