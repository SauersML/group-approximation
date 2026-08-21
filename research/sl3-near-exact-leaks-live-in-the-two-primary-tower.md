---
rg: 2
id: sl3-near-exact-leaks-live-in-the-two-primary-tower
kind: claim
title: SL3 near-exact-vertex leaks are confined to the two-primary congruence tower
distinct_from:
  odd-congruence-vertex-sector-admits-no-exact-leak: that is the SL_2 statement and needs the Serre amalgam plus Gerasimova-Shchepin vertex stability, and it leaves the enormous non-congruence representation wilderness of the virtually free vertex group uncovered; this is the SL_3 statement, where CSP plus superrigidity abolish the wilderness entirely, at the price of making near-exactness a hypothesis rather than a theorem.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that is the transfer inequality on exact representations of the whole group; this is the sector confinement for leak configurations whose VERTEX restriction is near-exact, using that inequality's mechanism through the odd factor of the level.
---

Let `Gamma = SL_3(Z[1/2])`, `Lambda = SL_3(Z)`, and let `(U_m, K_m)` be
microstates realizing an exact quasi-regular leak `(EQL1)` for this
pair.  Suppose the vertex restriction is near-exact: `U_m|_Lambda` is
within `eta_m -> 0` (normalized HS, on generators) of exact
finite-dimensional unitary representations `rho_m` of `Lambda`.  Then:

1. Each `rho_m` factors through a congruence quotient `SL_3(Z/N_m)` —
   unconditionally, by Margulis superrigidity (finite image of
   finite-dimensional unitary representations of the higher-rank
   lattice) and the congruence subgroup property of Bass--Milnor--Serre.
   There is NO non-congruence sector at `n = 3`, in stark contrast to
   the virtually free `SL_2(Z)`.
2. Write `N_m = 2^(a_m) m'` with `m'` odd and split
   `SL_3(Z/N_m) = SL_3(Z/2^(a_m)) x SL_3(Z/m')` by CRT.  On the odd
   factor, conjugation by `diag(2,1,2^(-1))` is defined and inner, the
   images of `Lambda` and `Gamma` coincide, and the doubled/(T)
   squeeze of the exact transfer gap forces the leak energy carried by
   the odd factor to vanish with `eta_m`.
3. Hence the entire leak profile concentrates on the `2`-primary
   factor: asymptotically, the enemy's commutant witness, its
   uncorrelated conjugates, and its whole `(EQL1)` structure live in
   the multiplicity data of the tower `SL_3(Z/2^a)` — the same
   two-adic solenoid direction as the SL_2 far sector, now with no
   alternative home.

Combined with the recorded uniform-outlier bound, the SL_3 enemy is
therefore EXACTLY one of two things: a uniform outlier from all exact
representations, or a two-primary congruence-tower configuration.  The
`SL_3` pair thus has the fully described enemy that `SL_2` cannot
offer, while also carrying property (T), the Hecke contraction, and no
amalgam construction surface: it is the correct battlefield for the
refutation, and this claim makes the reduction precise.

## Attempts

- **The two-primary enemy is a computable feasibility sequence.**
  Inside the tower sector, the regular restricted trace forces the
  level to grow (`a_m -> infinity`: any fixed level has
  `(1/d) Tr rho(lambda)` bounded away from `0` on the congruence
  kernel).  At a fixed level, the (T) conjugation squeeze pins the
  witness into the multiplicity algebra with dimension-free error, so
  the leak constraints reduce to BRANCHING data: define `delta(a)` as
  the minimal total defect of a leak configuration over
  `G_a = SL_3(Z/2^a)` — a finite representation-theoretic
  optimization, because the `h`-conjugation map is defined on the
  parahoric image `P-bar` and DESCENDS ONE LEVEL (`P-bar -> G_(a-1)`;
  two lifts of a mod-`2^a` point differ after conjugation by a
  mod-`2^(a-1)` element), making each instance a two-level tower
  coupling.  Refuting the tower sector is exactly
  `liminf delta(a) > 0`.  Two design subtleties, caught before
  probing: the constraint list must be a FIXED set of elements of `P`
  (e.g. `e_12(2), e_13(4), e_23(2)` and the three lower elementaries)
  — the enemy only owes vanishing defect on fixed relators, and it
  evades the seemingly fatal moving constraint
  `phi(e_13(2^a)) = e_13(2^(a-2))` by level spreading; and the
  instances at `a = 1, 2` are DEGENERATE (the fixed upper generators
  reduce to the identity), so honest machine-checkable instances
  start at `a = 3`, where the regular representation is too large
  (`|SL_3(Z/8)| ~ 1.1e7`) and the natural permutation representation
  on `(Z/8)^3` (`d = 512`) is the right probe carrier.
- **Probe v1 and the spectral floor (2026-08-21,
  `experiments/sl3_delta3_tower_probe.py`,
  `experiments/sl3-delta3-tower-probe.json`).**  A first optimization
  run under-converged (defect `~23.5` of max `24` — descent stalled;
  gradient formulas need finite-difference validation on a toy
  instance before a rerun).  The failure analysis produced the sharper
  tools: (i) by Hoffman--Wielandt, the per-pair defect floor is
  EXACTLY the squared optimal-transport distance between the spectral
  measures of `rho(lam)` and `rho(phi lam)`, computable from cycle
  structure for permutation models — any honest `delta(a)` must
  subtract this analytic floor and measure only the beyond-spectral
  (eigenvector/joint) obstruction; (ii) the generator constraints say
  the unipotent spectral measure is approximately DOUBLING-INVARIANT
  (`e_12(1)^2 = e_12(2)`), which is precisely
  `parabolic-spectrum-is-doubling-invariant`; exact invariance at
  finite two-levels forces `mu = delta_1` (all mass cascades to `1`
  in `a` doubling steps), and the enemy survives only because
  doubling has Lipschitz constant `2`, so the cascade amplifies the
  per-step defect by `2^a` and telescoping fails — the quantitative
  form of the recorded fact that single-map rigidity is false.
  (iii) Honest instances must also carry DEPTH: the fixed elements
  `h^j` all demand exact orthogonality (`psi(h^j) = 0` for every
  fixed `j`), and the `phi^j`-dictionary degenerates when
  `2j + 1 >= a`, so the true wall shape is `delta(a, J)` with depth
  `J ~ a/2` — the level/depth coupling is where a cross-level
  coherence argument would have to bite.
- **Probe v2: a large per-level leak cost (2026-08-21,
  `experiments/sl3_delta3_tower_probe_v2.py`,
  `experiments/sl3-delta3-tower-probe-v2.json`).**  With
  finite-difference-validated gradients (the harness caught four real
  bugs; all terms now match to eight decimals) and the exact spectral
  floor `2.732` subtracted: the unconstrained intertwining optimum at
  the `(a = 3`, permutation-representation`)` instance has raw defect
  `~6.97` and NATURALLY retains leak correlation `~0.23-0.32`;
  forcing the exact-leak orthogonality (`|<VKV*, K>| < 0.004`) raises
  the optimum to `~20.1` — a `+13.1` cost on a `24`-scale, consistent
  across restarts.  First numerical evidence that the tower sector
  has a genuine PER-LEVEL obstruction at fixed constraint lists:
  orthogonality of a `Lambda`-commuting unitary from its own
  `V`-conjugate is very expensive when `V` must intertwine the
  parahoric dictionary.  Caveats: local optimization (an upper-bound
  signal on infeasibility, not a proof), one representation choice,
  soft `K`-centrality.  The mechanism hunt is now the priority: both
  `K` and `VKV*` live in small commutant algebras (`rho(G)'` and its
  `phi`-twist), and the orthogonality demand plays against unitarity
  inside that small algebra — a provable per-level floor here, with
  (T)-uniform constants in `a`, would eliminate the tower sector
  entirely and leave the SL_3 enemy as uniform outlier only.
- Proved below by assembling established inputs; see the proof route.
  The one step that is a HYPOTHESIS here and a theorem at `SL_2` is
  vertex near-exactness: `SL_3(Z)` HS-stability is open (it is the
  Dogon--Vigdorovich program), so this claim describes the near-exact
  sector rather than eliminating the complementary outlier sector —
  matching the lane's standing division of the battlefield.
