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
- **Exact character data for the `delta(3)` instance (2026-08-21,
  corrected; `experiments/sl3_branching_overlap.py`,
  `experiments/sl3-branching-overlap.json`).**  Getting this
  computation honest reproved the node's own lesson twice: the
  dictionary `phi = Ad(h^{-1})` is NOT well-defined at level `2^a` —
  the simple-root entries divide by `2` (one level down) and the long
  root `e_13` divides by `4` (TWO levels down, since `h` has weight
  `4` on the long root) — so the only well-defined character pairing
  couples the level-`8` source with the level-`2` twist.  Validated
  integers (brute-force-checked kernel formula): over the source
  parahoric `Q_0` of order exactly `2^18`,
  `||chi_8||^2 = 265`, `<chi_8, chi_2 o phi> = 53`,
  `||chi_2 o phi||^2 = 19`, correlation `53 / sqrt(265 * 19) = 0.747`.
  These are the branching-correlation constants any per-level floor
  argument consumes, and the two-level descent with the long root
  twice as fast is the exact root-weight anatomy of the level
  compression.  (Earlier figures quoted from ill-defined single-level
  pairings were wrong and are superseded by these; the fractional
  norms were the tell.)
- **Floor mechanism candidate: phase locking in multiplicity-one
  blocks (2026-08-21).**  Structural restatement of the instance: with
  `A = rho(Q_0)''` and `B = rho(phi Q_0)''` one has `A v B = rho(G)''`
  (the two parahorics jointly contain all elementaries), so the
  witness `K in rho(G)' = A' cap B'` and its transport `VKV*` BOTH lie
  in `B'`, and the leak inner product lives inside `B' = ⊕ M_(mtilde)`.
  `V`'s residual freedom is an independent unitary per `B'`-block, so
  blocks with `mtilde >= 2` can usually be zeroed — but every
  MULTIPLICITY-ONE block contributes a PURE PHASE of fixed weight
  `d_sigma/d`, and these phases are not free: they are the phases of
  `K`'s `rho(G)'`-components `k_pi`, so blocks fed by the same
  `G`-irrep are LOCKED together on both the transported and the
  untransported side.  A floor theorem follows whenever the
  multiplicity-one pairing weight of some `pi*` exceeds the total
  cancellation capacity of the free blocks — a purely combinatorial
  condition on the two branchings `G -> Q_0` and `G -> phi(Q_0)`
  (`Q_0` is a `2`-group of order `2^18`, so its representation theory
  is monomial and the required tables are computable).  This is the
  designated route to a proved per-level `delta`-floor.
- **Exact commutant anatomy of the prototype (2026-08-21,
  `experiments/sl3_orbit_algebra.py`,
  `experiments/sl3-orbit-algebra.json`).**  Union-find on the 262144
  pairs and generic-element spectra give the full Wedderburn data.
  Witness algebra `rho(G)'`: dimension `37`, NONcommutative;
  generic-spectrum profile (irrep-dim : total multiplicity):
  `1:4, 6:3, 21:2, 28:2, 84:2, 112:2` (checks: `sum dim*mult = 512`,
  and `sum m^2 = 37` forces either the 6-dim slot as one irrep with
  `m = 3` plus two of the four large dims split `1+1`, or the 6-dim
  slot split `2+1` with all four large dims at `m = 2`).  So `K` is a
  unitary in a 37-dimensional algebra with a `4x4` block on the
  orbit-level wire (trivial isotypic: the four divisibility orbits)
  and small rotational blocks elsewhere.  Twisted commutant
  `rho(Q_1)'`: dimension `265` (independently matching
  `||chi_8||^2_(Q_0) = 265` — transpose symmetry — validating the
  whole pipeline), profile `1:26, 2:15, 4:18, 8:12, 16:10, 32:4`.
  The floor analysis now needs only the pairing weights: for each
  `G`-isotypic block, its `Q_1`-decomposition (computable by
  compressing the `Q_1`-orbit algebra to `G`-isotypic projectors and
  reading generic spectra again).  Multiplicity-one `Q_1`-blocks fed
  by multiplicity-one `G`-blocks are the phase-locked channels the
  mechanism predicts must carry an irreducible leak floor.
- **Full branching tables and the corrected floor picture
  (2026-08-21, `experiments/sl3-pairing-weights.json`).**  Compressing
  a generic twisted-commutant element to every `G`-isotypic cluster
  gives the complete `Q_1`-branching of each `G`-irrep in the
  prototype, all rows arithmetic-checked: `21 = 5*1 + 2*4 + 8`,
  `6 = 4*1 + 2`, `28 = 4*2 + 3*4 + 8`, `84 = 2*2 + 4*4 + 2*16 + 32`,
  `112 = 4*8 + 3*16 + 32`, with identical profiles across isotypic
  copies (cross-validation).  The naive per-channel floor FAILS by
  weight counting (phase-locked dim-1 channels carry far less weight
  than the rotatable blocks); the real mechanism, matching the
  measured `+13.1`, is that the rotation freedom is per
  `Q_1`-ISOTYPIC block and each such block is fed jointly by many
  `G`-irreps — one `W_sigma` must serve all of them at once, so
  zeroing every block simultaneously against the locked `K`-phases is
  an overdetermined joint problem.  With all tables in hand the leak
  minimum reduces to an EXACT small optimization in
  `37 + 265`-dimensional coordinates (`K` in its Wedderburn blocks,
  one `W_sigma` per twisted block), faithful to the true structure —
  the designated next computation, and if its minimum is robustly
  positive the prototype floor becomes finite linear algebra.
- **The floor is a 37-dimensional spectral question (2026-08-21,
  compressed-conjugation frame).**  Since `K` and the trace pairing
  both live in `Z = rho(G)'`, the leak factors through the compressed
  conjugation map: `<VKV*, K> = <Phi(K), K>` with
  `Phi = E_Z o Ad(V) restricted to Z`, a unital trace-preserving
  completely positive map on the 37-dimensional orbit algebra.  The
  per-level floor therefore reduces to the joint numerical range of
  the compact family `{Phi_V : V near-dictionary}` on trace-zero
  unitaries of `Z`, with the clean sufficient criterion: if the
  Hermitian part of `Phi_V` is positive definite on the trace-zero
  subspace with gap `gamma`, then `|leak| >= gamma` for every witness.
  `Phi` is Hecke-species — the same animal as the established
  `hecke-averaging-realizes-commutant-expectation` — so the
  uniformity-in-level question becomes a spectral-gap statement about
  compressed conjugation operators on commutant algebras along the
  two-primary tower, exactly where the (T) technology lives.  Next
  computation: extract `Phi` (a `37 x 37` matrix) at the probe's
  optimal `V` and read its Hermitian spectrum on trace-zero.
- **Negative results that sharpen the floor (2026-08-21,
  `experiments/sl3-phi-spectrum.json`,
  `experiments/sl3-delta3-probe-v3.json`).**  (i) At the
  control-optimal dictionary the Hermitian part of the compressed
  conjugation map `Phi` on trace-zero is INDEFINITE (21 positive, 15
  negative eigenvalues, extremes `-0.249` and `+0.592`): the simple
  positivity criterion fails, so the floor cannot come from the
  quadratic form alone.  (ii) The reduced probe with `K` parametrized
  in the 37-dim algebra but unitarity only penalized drove the leak
  to `~1e-4` at control defect — with unitarity violation `0.58-0.74`:
  off the unitary manifold the leak is cheap.  Together these
  localize the mechanism exactly: the per-level floor, if real (and
  the `+13.1` of the honest unitary probe v2 says it is), lives in
  the interplay of the INDEFINITE form with the UNITARITY of `K` —
  trace-zero HS-null directions of `Phi` exist but are not unitary
  elements of `Z`.  Next: v4 with exact Wedderburn-block-unitary
  parametrization of `K` (block isomorphism via generic-element
  eigenprojections) and a reported split of the `+13.1` cost between
  `K`-centrality and `V`-dictionary terms.
- **v4 scope gap and the v5 design (2026-08-21).**  v4 measures the
  leak floor over exact block-unitary `K` at the FIXED control
  dictionary `V_0` (early sweep: floor `~0.149`, `unit_err = 0`).
  But the low-defect dictionary manifold is the coset
  `V_0 * U(rho(Q_1)')`-approximately (the residual freedom commutes
  with the six target generators, and the per-instance conjugation
  gap of the fixed 512-dim representation gives the squeeze even
  though `Q_1` is a 2-group with no uniform Kazhdan constant), and
  since `Z = rho(G)' subset rho(Q_1)'`, the honest floor is the JOINT
  minimum over `K in U(Z)` and `W in U(rho(Q_1)')`:
  `min |<E_Z(V_0 W K W* V_0*), K>|` — precisely the joint-rotation
  problem of the phase-locking mechanism, now in fully reduced
  coordinates (`37`-dim witness blocks and `265`-dim torsor blocks).
  v5 = v4 plus the `W`-coordinates; if the joint minimum stays
  positive the prototype floor is real against ALL low-defect
  dictionaries, and the remaining escape is only the defect-budget
  tradeoff already charted by v2 (`+13.1`).
- Proved below by assembling established inputs; see the proof route.
  The one step that is a HYPOTHESIS here and a theorem at `SL_2` is
  vertex near-exactness: `SL_3(Z)` HS-stability is open (it is the
  Dogon--Vigdorovich program), so this claim describes the near-exact
  sector rather than eliminating the complementary outlier sector —
  matching the lane's standing division of the battlefield.
