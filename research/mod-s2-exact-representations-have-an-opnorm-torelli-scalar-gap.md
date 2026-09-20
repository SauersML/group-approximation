---
rg: 2
id: mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap
kind: claim
title: Exact finite-dimensional representations of Mod(S_2) never put the whole spectrum of a separating twist near a primitive cube root of unity
distinct_from:
  mod-s2-exact-representations-have-a-torelli-scalar-gap: that asks for a uniform normalized Hilbert-Schmidt gap; this asks only for an operator-norm gap, which that claim implies because the operator norm dominates the normalized HS norm, so this is strictly weaker.
  deligne-torelli-character-counts-separating-twists: its (ST5) excludes an exact cube-root scalar; this asks for a uniform operator-norm distance from those scalars.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that concerns all point-norm asymptotic models; this restricts to honest representations of Mod(S_2), and it is a necessary condition for that gate.
---

**OPEN.** There is `delta_0 > 0` such that every finite-dimensional unitary representation `rho` of
`M = Mod(S_2)` and every separating Dehn twist `t_s` satisfy

```text
|| rho(t_s) - omega^(+-1) I ||_op  >=  delta_0 ,        omega = exp(2 pi i/3).
```

Since `rho(t_s)` is unitary, this is a spectral statement: the spectrum of `rho(t_s)` never lies in
the open arc of radius `delta_0` around `omega` or around `omega^2`. Equivalently, `1/3` does not lie
in the closed subgroup

```text
Z_hon = { alpha : inf_rho ||rho(t_s) - exp(2 pi i alpha) I||_op = 0 }  <=  Z_op
```

of `mod-s2-real-untwisting-identifies-deligne-norm-parameters`. It is closed and a subgroup by the
same diagonal, tensor and conjugate argument as (U2).

## Position in the graph

- **Necessary for the flagship.** An honest `rho` is an asymptotic homomorphism with zero defect,
  so `Z_hon <= Z_op`. If this claim fails, then `1/3` lies in `Z_op`, so `1/3` lies in `P_op` by (U4).
  Then `Rad_MF(E_3) != C_3`, which refutes both `deligne-triple-cover-exact-mf-radical` and
  `deligne-nontrivial-maslov-opnorm-sectors-are-empty`. This is not filed as a route into this
  node, to keep the graph acyclic.
- **Sufficient with stability.** Together with `mod-s2-is-point-norm-matricially-stable`, it proves
  the gate: `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability`.
- **Implied by the HS version.** `mod-s2-exact-representations-have-a-torelli-scalar-gap` implies
  it, since `||X||_op >= ||X||_2` for the normalized HS norm.

## Known partial information

- *Pointwise.* `delta(rho) > 0` for each single `rho`, by (ST5) and (TS4).
- *Finite image.* If `rho` factors through `M/N` with `N` of finite index, then
  `||rho(t_s) - omega^(+-1) I||_op >= sqrt(3)/l(N)`, with `l(N)` as in (E4) of
  `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors`. This follows from (E4) because
  the operator norm dominates the normalized HS norm. It is not uniform in `N`.
- *Quantum representations.* In the SU(2) level-`k` representations the separating twist is far
  from every scalar. The tabulated normalized-HS distances squared run from `0.36` at `k = 2` up
  towards `1` at `k = 400` (`research/artifacts/hl-nh-quantum-reps-2026-09-13.md`, section 3). The
  operator norm is at least as large, so the tabulated levels stay away from the cube-root scalars.
- *Heuristic about locality.* The graph's class kill
  `deligne-flexible-subgroup-restrictions-carry-exact-sector-models` suggests the same thing here: an
  argument that only uses relations generating a Deligne-flexible subgroup will not see the
  cube-root mark. This is not transported rigorously here.

## Attempts

- **2026-09-18, swarm-0917-w9-w9-deligne-follow: algebraic scalarization and
  determinant tests both die.**
  - *Scalarization (sketch).* Suppose `rho(t_s)` is exactly scalar. Then its value is
    a separating-twist character value (TS4, ST5), which excludes the cube
    roots. Passing from near-scalar to scalar would require an algebraic
    quotient of `rho(M)` in which `t_s` becomes central.
    - Let `Q = rho(M)`, and divide by the normal closure of `[t_s, Q]`. By
      the Margulis normal subgroup theorem the result modulo the image of
      `t_s` is either finite or `Sp_4(Z)` modulo a finite group.
    - In the finite case the quotient is finite, residually finite and
      virtually cyclic, so the value of `t_s` is a tenth root of unity by
      Deligne's residual. In the other case the quotient is a central
      quotient of `M/[K,M]`, which is circular.
    - Either way the metric information `||rho(t_s) - omega|| < epsilon` is
      lost, because the quotient kills a non-small subgroup.
  - *Determinant.* `det rho` is a character of `M`, so `det rho(t_s)` is a
    tenth root of unity. If every eigenvalue is `omega e^(i eta_j)` with
    `|eta_j| < epsilon`, the product `omega^d e^(i sum eta_j)` can reach
    every tenth root once `d epsilon >= 2 pi/30`. So the test dies for
    `d >= C/epsilon`.
  - *Invariant for both.* Any test that factors through a finite quotient
    of `M` or through a one-dimensional character is bounded by the (E4)
    floor, which is not uniform in the quotient. A uniform proof needs
    information from representations with infinite image.
- **2026-09-18, swarm-0917-w10-w10-deligne-pull: split into a Torelli-abelian arithmetic part and an
  infinite-image reduction (reframing).**
  - *Dictionary (ESTABLISHED).* `mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers`:
    - Decompose `rho|_(K/[K,K])` into Torelli eigencharacters. Mess's free basis makes `K/[K,K]` the
      permutation module `Z[X]`.
    - One orbit is an exact projective representation of its finite-index stabilizer `Gamma'`, with class
      `Phi_(Gamma')(h) - (alpha/r)[b]`, where `|h| <= epsilon/4`.
    - Induction reverses this.
  - *Finite image is Torelli-abelian (ESTABLISHED).*
    `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`: a dimension-free Frobenius commutator
    lemma shows that `||rho(t_s) - omega I|| < 1/2` with finite image forces `rho(K)` abelian.
  - *Decomposition.* Route `mod-s2-opnorm-torelli-gap-via-finite-index-multipliers` needs two OPEN inputs:
    - the infinite-image reduction `mod-s2-near-scalar-reps-reduce-to-torelli-abelian`;
    - the arithmetic statement `sp4-shifted-maslov-multipliers-stay-far-on-finite-index`, a floor uniform over
      all finite-index subgroups.
    Given the reduction, the target is equivalent to the arithmetic statement.
  - *Where uniformity dies.* Corestriction by tensor induction to `Sp_4(Z)` sees only `n(alpha + m(h))`, where
    `n` is the index and `m(h)` the mean of `h`. That is non-uniform in `n` and empty when `3 | n`, like the (E4)
    floor. A proof must use classes of `H^2(Gamma';R)` that are not restricted from `Gamma`.
- **2026-09-18, swarm-0917-w10-w10-deligne-follow: a uniform Deligne-only
  floor dies at Gamma(3).** Result:
  `sp4-mess-classes-are-non-profinite-off-the-maslov-line` (ESTABLISHED).
  - *Idea.* For a Torelli-abelian finite-image model at level `Gamma'`, the
    multiplier is `(alpha/r) res b + sum_D h_D v_D`, where `v_D` are the
    pushouts of the Torelli extension along Mess orbit counts. The multiplier
    must be profinite. Hope: modulo profinite classes only the Maslov line
    survives, with Deligne's kernel `(1/2)Z`. Then `alpha/r` would be pinned
    to `(1/2)Z + O(|h|)`, uniformly in `Gamma'`, which would give (B) on this
    class.
  - *Where it dies.* On normal `Gamma'`, the conjugation symmetry of the
    orbits, together with `sum_D v_D = -(10/a) res b`, forces `m | 20/a`, where
    `m` is the number of orbits, whenever some `v_D/m` has a Maslov
    coordinate. At `Gamma(3)`, `m = 45`, so `iota(v_D/45)` is non-profinite
    and off the Maslov line. The same holds at every deeper normal level,
    with `h = 1/m -> 0`.
  - *Invariant.* The quotient `H^2(Gamma'; Q/Z) / (beta(Q) + H^2_fin)` is
    nonzero. Any proof of (B) must control all of it.
  - *By-product.* `a | 20`.
- **2026-09-18, swarm-0917-w11-w11-deligne-break (calibration): the Jones
  rectangular family, which has infinite image, is computed. It kills
  spectral-spread arguments and proves the gap on the family's tensor
  closure. The node stays OPEN.** See
  `mod-s2-jones-rectangular-separating-twist-spectrum`, ESTABLISHED.
  - *Closed-form spectrum.* In Jones' 5-dimensional TL_6 representations
    `rho_x` (`|x| < pi/8`), the eigenvalues of `rho_x(t_s)` are
    `zeta e^(96ix/5)` (multiplicity 1) and `zeta e^(-24ix/5)` (multiplicity 4),
    with `zeta` in `mu_5`.
  - *Near-scalar with infinite image.* The distance from `rho_x(t_s)` to the
    scalars is `2 sin(gamma/4)`, where `gamma` is the distance from `24x` to
    `2 pi Z`. So infinite-image honest representations put `t_s` arbitrarily
    close to a scalar: near `x = 0` (the `S_6` point) and near `x = pi/12`.
    - The "quantum representations" evidence above holds only for the SU(2)
      level-k family.
    - *Class kill.* Any proof that lower-bounds `dist(rho(t_s), T I)` on
      infinite-image representations dies at that step.
  - *Sharp gap on the family.* `||rho_x(t_s) - omega^(+-1)|| >= 2 sin(pi/15)`,
    which is the distance from `mu_5` to the cube roots. On all direct sums of
    tensor words in the family, its conjugates and the characters, the bound is
    `2 sin(pi/24)`, uniform in dimension `5^n`, where the w9 determinant test is
    void. The mechanism is scalar-locus attraction: the drift of the nearest
    scalar from `mu_5` is at most `0.3` times the angular spread.
  - *Proposed invariant.* The attraction constant `C(rho)`. The gap node
    follows from `sup C < infinity` on honest representations whose `t_s` is
    near-scalar, together with (ST5).
  - *Where a counterexample must live.* Assume the closure of `rho_x(M)`
    contains `SU(5)` (sketch, not cited). Then Schur modules also satisfy
    `C <= 0.6`, so a counterexample must mix unrelated families whose `t_s`
    eigenvalue steps are incommensurable.
- **2026-09-18, swarm-0917-w11-w11-deligne-pull (census-computation): on the Torelli-abelian class the gap
  is an exactly computable congruence limit, and it does not decay through level three.**
  - *Reduction (ESTABLISHED).* See `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`.
    - For `rho` with `rho(K)` abelian, split `rho|_K` into Torelli characters `chi`.
    - Each eigenspace is a projective representation of a finite-index `Gamma_chi`. By Malcev it becomes
      linear on a finite-index `Gamma''`, so `chi` extends to a character `psi` of `pi^(-1)(Gamma'')`.
    - Hence the infimum of `||rho(t_s) - omega^(+-1) I||` over this class is exactly `2 sin(pi d_inf)`, where
      `d_inf = lim_N d(Gamma(N))` and `d(Gamma')` is the `l_inf` distance from `(1/3)1` to the annihilator
      of the relation lattice `W(Gamma')` of the separating-twist classes in `H_1(pi^(-1) Gamma')`.
    - Monomial representations `Ind psi` attain `d(Gamma')`.
  - *Census.* Reidemeister-Schreier with the Birman-Hilden presentation computes `d` exactly (matching
    certificate and exact feasible point) on 29 finite-index subgroups.
    - Values: `d(Sp_4 Z) = 1/15`, `d(Gamma(2)) = 1/30` (index 720, `b_1 = 9`), `d(Gamma(3)) = 1/15`
      (index 51840, `b_1 = 24`, `rank W = 21`).
    - Mixed levels 6 and 15 give `1/15` or `1/30`. So the Torelli-abelian gap is at most `2 sin(pi/30)`.
  - *Invariant / obstruction.* Transferred level-one certificates have augmentation `5 [Gamma : Gamma']`,
    and `3 | |Sp_4(F_p)|` for every `p`, so they die at every congruence level.
    - Surviving lower bounds need sparse relations (bounded `l1` norm, augmentation prime to 3).
    - At `Gamma(3)` these exist, with `l1 = 5`. They are the 27 point stars of `GQ(2,4)` on the 45
      symplectic splittings mod 3, and they generate `W(Gamma(3))` over `Z` (`gq24_check.py`).
  - *New necessary condition.* `mod-s2-torelli-abelian-census-limit-is-positive` (OPEN): `d_inf > 0`. It is
    implied by this node and necessary for the flagship. `d_inf = 0` would refute the flagship.
  - *Consistent with* the Jones/TL_6 calibration by swarm-0917-w11-w11-deligne-break, where the gap is
    `2 sin(pi/15)` on the whole unitary arc.
- **2026-09-18, swarm-0917-w12-w12-deligne-break (cohomology-index): Maslov line established, the central class
  killed, and the Torelli-abelian class reduced.** See `mod-s2-torelli-characters-have-a-metaplectic-maslov-line`.
  - *Maslov line.* Push commutator lifts through the real untwisting. This gives `F(K cap [H,H]) = 5 m Z` for every
    `H = pi^-1(Gamma')`, where `m` in `{1,2}` is the order of `z` in `H_1(Gamma~')`. It also pins `r = +-1/5`.
  - *Class kill.* If `rho(t_s)` is central in `rho(M)`, then `rho(t_s)^10 = I`. So the distance to `omega^(+-1)` is at
    least `2 sin(pi/30)`, and this is sharp. Every member dies where `alpha F` must vanish on `K cap [H,H]`.
  - *Census explained.* The census values `1/15` and `1/30` are exactly `1/(15m)`.
  - *Reduction.* Torelli-abelian monomial models can beat `2 sin(pi/(15m))` only through a small positive torsion
    character, since no real character is positive on all separating twists (transfer). The matching lower bound is
    filed OPEN as `mod-s2-maslov-line-is-optimal-for-torelli-characters`. A failure of it along a family would refute
    this claim.
  - *Where it stops.* Representations where `rho(t_s)` is not central and that are not Torelli-abelian monomial are
    untouched. This includes every representation with nonabelian Torelli image.
- **2026-09-20, swarm-0917-w21-w21-deligne-break (reframing): TQFT/Galois class kill.** See
  `mod-s2-tqft-twist-spectra-obey-the-cube-root-gap` (ESTABLISHED for (T1)--(T4), unreviewed).
  - *Result.* Suppose the spectrum of `rho(t_s)` is `lambda {theta_a : a in L}`, where `L` is a Galois-stable set of
    labels of a modular category. Then `rho(t_s)` is scalar, or `||rho(t_s) - mu I|| >= sin(pi/24)` for every `mu`.
    - The constant comes from the sharp bound `max_j ||k j^2/n|| >= 1/24` over units `j`.
    - The proof uses the Dong--Lin--Ng relation `theta_(sigma^ a)/theta_(sigma^ b) = sigma^2(theta_a/theta_b)`.
  - *Scope.* Closing under characters, tensor products and finite direct sums, and applying (ML3) to the scalar
    summands, gives the cube-root gap `sin(pi/24) ~ 0.1305` for this whole class.
  - *Galois-stable labels.* `Irr(C_ad)` is Galois-stable for pseudounitary `C`, by Gelaki--Nikshych `C_ad = (C_pt)'`.
  - *Invariant.* The `sigma^2` action on eigenvalue ratios.
  - *Where every member dies.* "Spectrum near a point" forces "spectrum exactly a point", and that point lies in
    `mu_10`.
  - *Survivors.* A witness must have a separating-twist spectrum that is not a Galois-stable set of modular twists. The
    options are:
    - transcendental eigenvalues, as in the Jones deformation;
    - irreducible RT summands that see only part of the channels;
    - non-modular origin.
  - *Open point.* The RT reading needs the channel set `{a <= x tensor x*}` to equal `Irr(C_ad)`. This is checked for
    `SU(2)_k`, pointed and Ising-type categories, but it is not proved in general.
  - *Status.* This node stays OPEN.
