---
rg: 2
id: lifted-thompson-t-center-has-relative-t
kind: claim
title: "The pair (T-bar, Z) has relative property (T): every cnd function on the lift T-bar of Thompson's T is bounded on its centre"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that asks relative (T) for (C(C,Z) ⋊ V, Z·1_C); this is the same statement for the subgroup T-bar, whose centre goes to Z·1_C. It is stronger and implies that claim.
  lifted-thompson-t-is-a-t-menable: that is the Haagerup property of T-bar; this claim refutes it
refuted_by:
  - lifted-thompson-t-is-a-t-menable
---

**Statement.** Let `T̄` be the lift of Thompson's `T` to `R`, and let `z(x) = x + 1`. For every
cnd function `ψ` on `T̄`, `sup_M ψ(z^M) < ∞`.

**Status.** OPEN.

**Why it matters.** It is a one-dimensional sufficient condition for refuting
`brin-thompson-groups-nv-are-a-t-menable`:
- it implies `cantor-integer-maps-central-direction-has-relative-t`, through
  `cantor-integer-maps-central-direction-via-lifted-thompson-t`;
- that implies `cantor-integer-maps-by-v-are-not-a-t-menable`, and hence that `2V` is not
  Haagerup.

**Evidence either way.**
- The class of the extension is bounded, since the rotation number gives `rot(z) = 1`.
- On the refuting side: bounded-class central extensions *can* have a relatively-(T) centre, as
  in lifts of lattices of `Sp(2n,R)`, but there the quotient has (T). No example with a
  Haagerup quotient is known to this lane. By arXiv:1905.10081, p. 96, the question whether
  Haagerup lifts through central extensions is open.
- On the supporting side: lattices in the universal cover of `SL_2(R)`, and the braid group
  `B_3`, which is the lift of `PSL_2(Z) ≤ T`, are Haagerup. There the centre is not relatively
  (T).
- A proof would need an invariant that sees the centre through cnd functions. Quasimorphisms do
  not qualify, since they are not cnd.

## Attempts

Earlier ruled-out witness classes are listed under `lifted-thompson-t-is-a-t-menable`, Attempts
2026-09-18: permutation representations on dyadic orbits, and virtual splittings.

- **2026-09-18 (swarm-0917-w9-w9-nv-break, reframing): dilation-tower reduction. The node stays
  OPEN.**
  - *Structure (proved).* `lifted-thompson-t-quotients-are-rotation-centralizers` shows
    `T̄/⟨z^{2^k}⟩ ≅ C_T(r_k)`, via `ι_k(g) = p(2^{-k} g(2^k ·))`, with `z ↦ r_k`.
  - *Reduction (proved).* `lifted-thompson-t-relative-t-forces-dyadic-twist-gap` puts the question
    in terms of a twist-cost function `c` on `R/Z`. It is lower semicontinuous, symmetric and
    subadditive, satisfies `c ≥ |e(θ)−1|/L`, and vanishes only at `0`.
    - `inf_{θ≠0} c = 0` refutes this node, by an explicit weighted sum of matrix-coefficient cnd
      functions.
    - The dyadic part of `c` is exactly `Gap_T`. This is a uniform spectral gap *inside Thompson's
      T* for the level-`k` copies `ι_k(S)`, on vectors with no `r_k`-fixed part.
  - *What this changes for a breaker.*
    - To refute this node it is enough to produce, from representations of `T` itself, vectors
      that are almost invariant under the `2^{-k}`-periodic copies of the generators and have no
      `r_k`-fixed part. Every representation of `T`, restricted to `C_T(r_k)`, is a candidate.
    - To prove this node, one needs `Gap_T` and also a way to handle non-dyadic twists, which is
      open. Subadditivity is useless for that, because `c` is only lower semicontinuous and
      `c(θ) ≳ |θ|`.
  - *Classes checked against `Gap_T` (heuristic kills, not full proofs).*
    - *Koopman representation on `L²(S^1)`, with Fourier vectors `e_n` for fixed `n`.* On each arc
      of length `2^{-k}`, `e_n` is within `O(n 2^{-k})` of a constant. So the defect of
      `ρ(ι_k(f̃)) e_n` tends to the *self-similar constant* `‖ρ(f)1 − 1‖²`, which is
      `∫ (√((f^{-1})') − 1)² > 0` for `f ≠ 1` in `F`. These vectors die at the rescaled-cell
      defect.
    - *Sums `Ψ = Σ a_k ψ_k ∘ ι_k` of pulled-back cnd functions of `T`.* Each summand is
      `2^k`-periodic along `z`, so an unbounded `Ψ` needs infinitely many levels. For Farley's
      `ψ`, recalled as comparable to caret count and not rechecked, both `ψ(r_k^M)` and
      `ψ(ι_k(t_1)) = ψ(r_{k+1})` are `≍ 2^k`. So finiteness on `S` forces `Σ a_k 2^k < ∞`, which
      bounds `Ψ` on `z`.
    - The invariant that kills this class is *rotation domination*:
      `sup_M ψ(r_k^M) ≤ C · Σ_s ψ(ι_k(s))` uniformly in `k`. Any family of cnd functions on `T`
      with this property is dead for this purpose.
    - *Induction from `λ(T̄) = C_{T̄}(t_1)`.* It halves twists, since
      `min(c(θ/2), c(θ/2+1/2)) ≤ √|S| Λ c(θ)` with `Λ = max_s |λ(s)|_S`. But inducing back up
      loses almost-invariance, because the subgroup has infinite index. So it gives no net descent.
  - *Next falsifiable step.* Test `Gap_T` on Jones' Pythagorean / planar-algebra representations of
    `T`, where rotations act by explicit unitaries. Either find rotation domination there, or find
    `r_k`-nonfixed vectors with defect `o(1)` under `ι_k(S)`.
- **2026-09-19 (swarm-0917-w14-w14-nv-break, group-rings / census-computation): finite
  hermitian-square certificates are dead for this node; it stays OPEN.**
  - *Attempt.* A Kaluba–Nowak–Ozawa style semidefinite certificate in `R[T̄]`:
    `Δ_S Δ_z − λΔ_z ∈ Σ²R[T̄]` with `λ > 0`. Since `z` is central, this would give
    `Δ_S ≥ λ` off the `z`-invariant vectors, i.e. this node, and hence refute
    `brin-thompson-groups-nv-are-a-t-menable`.
    - Code: `experiments/lifted-thompson-t-sos-2026-09-17/tbar.py`, exact PL arithmetic in `T̄`
      with `c̃^3 = z^{-1}` checked.
    - Code: `experiments/lifted-thompson-t-sos-2026-09-17/sos.py`, the SDP.
    - Radius 2, generators `x_0, x_1, c̃, z` and their inverses, `|B_2| = 51`: SCS reports
      `λ* ≈ 0.0033`, with PSD-projected ℓ¹-residual `≈ 5·10^{-4}`
      (`run-rel-R2-withz.log`).
  - *Result (ESTABLISHED).* `sos-certificates-cannot-see-an-infinite-central-subgroup` shows
    that this value is solver error. Every sum of hermitian squares in `ker(z ↦ 1)` equals
    `Δ_z` times a sum of hermitian squares.
    - So `Δ_z^m(Δ_S − λ) ∉ Σ²` for every `λ > 0`, at every radius and for every generating set.
    - `Δ_z^m(Δ_S² − λΔ_S) ∈ Σ²` would give (T) for `T̄`, which is false.
    - Fixed-support twisted certificates in `C[T̄]/(z − e(θ))` have optimal `λ → 0` as `θ → 0`.
  - *Invariant.* The trace of `R[T]` (the image under `z ↦ 1`) together with cancellation of the
    central non-zero-divisor `Δ_z`.
  - *Where every member dies.* The certificate maps to `0` in `R[T]`. So every square root lies
    in `(1 − z)R[T̄]`, and `Δ_z` cancels.
  - *Consequence for breakers.* A proof of this node cannot be a finite computation of this type.
    It needs an argument uniform in the support radius, such as `Gap_T` proved by representation
    theory, or a non-central pair. The kill does not reach non-central normal subgroups, such as
    the coordinate-mixing `Z² ⋊ F_2` of `brin-thompson-2v-is-not-a-t-menable`. The same kill
    applies verbatim to `cantor-integer-maps-central-direction-has-relative-t`.

- **2026-09-19 (swarm-0917-w16-w16-nv-follow, reframing): Brieskorn-lattice covering. Node stays
  OPEN; one class of proofs killed.**
  - *Structure (ESTABLISHED, `lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice`).* The
    Ptolemy generators `α` (rotation by `1/4`) and `β` (order-3 Farey rotation) generate `T`. Their
    lifts satisfy `α̃^4 = β̃^3 = z` and `(β̃α̃)^5 = z^3` exactly.
    - So `T̄ = Λ/N̂`, where `Λ = ⟨x,y | x^4 = y^3, (yx)^5 = x^{12}⟩` is a perfect cocompact lattice
      in the universal cover of `PSL_2(R)` (recalled: `π_1 Σ(3,4,5)`).
    - The centre generator `c = x^4` maps to `z`, and `N̂ ≅ ker(Δ(3,4,5) → T)` meets `⟨c⟩`
      trivially.
  - *Kill (proved).* `Λ` is Haagerup, so `(Λ, ⟨c⟩)` fails relative (T). Every argument for this node
    that uses only relations holding in `Λ` is dead.
    - This includes the torsion data, the rotation numbers `1/4`, `1/3`, `3/5`, and anything
      derived from them.
    - A proof must use elements of `N̂`. In the Lochak–Schneps presentation these are lifted
      disjoint-support commutations, which lift with exponent `0`.
    - Relative (T) of the centre, if true, is created entirely by the quotient `Λ → T̄`.
  - *Next falsifiable step.* The Seifert/magnetic reformulation: induce a representation `σ` of
    `T̄` from `Λ` to the universal cover.
    - Prove that `c_{T̄}(θ)²` is comparable, with constants independent of `σ`, to the bottom of the
      spectrum of a magnetic Laplacian with field `∝ θ/n`. This is on Hermitian orbibundles over
      `S^2(3,4,5)` whose monodromy kills `N̂`.
    - Then test whether a uniform lower bound on the lowest Landau level can survive the
      constraint that the bundle's monodromy kills `N̂`.
