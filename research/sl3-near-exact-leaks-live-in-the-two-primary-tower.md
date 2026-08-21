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
- **One uniform one-step floor suffices (2026-08-21, pure
  reduction).**  The exact profile demands `psi(h^j) = 0` for EVERY
  fixed `j`, and the `j`-th demand is a one-step two-level pairing of
  the level-`2^a` data with its level-`2^(a-2j)` descent.  So there is
  no need for a cross-level coherence argument at all: if the
  ONE-STEP floor `min |leak| >= c_0 > 0` of the block-trace reduction
  holds uniformly in the starting level for the honest two-level
  pairing, then already the single fixed constraint `psi(h) = 0` is
  violated at every sufficiently deep tower configuration, and the
  entire tower sector dies.  The uniformity target is therefore:
  bound `min_p (|p* M_a p| - S(p))` below by a constant independent
  of `a`, where `M_a` is the matched branching form of the level-`a`
  two-level pairing — a sequence of explicit finite inequalities
  whose structure (parahoric branching under one descent step) is
  level-periodic in the tower, exactly the sort of statement the
  Hecke/(T) technology is built to make uniform.
- **Layer decomposition and the shift structure (2026-08-21, by
  hand, verified against the computed anatomy).**  The permutation
  module splits `G_a`-equivariantly by divisibility strata into
  primitive-layer representations pulled back from levels
  `j = 0..a`, and the computed dims confirm it exactly: layer 1 is
  `7 = 1 + 6`, layer 2 is `56 = 1 + 6 + 21 + 28`, layer 3 accounts
  for `448` with the second copies of `84, 112` — which also explains
  the four trivial copies (one per layer: the orbit-level wire).  The
  descent map `phi` shifts layers by TWO (the long root has
  `h`-weight `4`), so the matched one-step form `M_a` is, away from
  the top and bottom layers, a fixed local block tensored with the
  shift by two on the layer chain.  Uniform-in-level positivity of
  the block-trace floor therefore reduces to a transfer-operator
  statement: one finite verification of the fixed local block plus
  control of the two boundary layers — the level-periodicity is now a
  theorem-shaped mechanism, not a hope.  On the orbit-level wire the
  locked form is literally a truncated shift pairing
  `sum conj(t_j) t_(j-2)` of the per-layer phases of `K`'s
  trivial-isotypic block, the cleanest place to test the mechanism by
  hand.
- **Slot bookkeeping and carrier localization (2026-08-21, by
  hand).**  The 26 one-dimensional parahoric slots decompose exactly:
  `4` from the layer trivials (all on the `Q_1`-trivial character,
  multiplicity `>= 4`, never a carrier), `12` from the three 6-dim
  slots (`4` characters each), `10` from the two 21-dim slots (`5`
  each) — total `26`, matching the computed profile and validating
  every table at the character level.  The dims `28, 84, 112` contain
  NO one-dimensional parahoric content, so at level `3` every
  potential rigid carrier is fed by 6- or 21-dim `G`-irreps —
  shallow-layer content.  Whether any slot actually has
  `mtilde = 1` depends on character coincidences across the 6/21
  feeds (multiplicity `m >= 2` feeds disqualify their own characters
  outright: they contribute `m` to each), which the running probe's
  block census answers.  HONEST CONCERN for uniformity: shallow-layer
  carriers sit at the BOUNDARY of the layer chain, while the
  transfer-operator mechanism wants locked weight in the BULK; at
  higher levels the new deep layers bring their own parahoric
  character content, and whether the carrier census keeps positive
  weight as `a` grows is now identified as THE precise
  uniformity question for the tower sector.
- **Wire hand-test: negative, and clarifying (2026-08-21).**  The
  four G-invariant vectors sit inside the single Q_1-TRIVIAL isotypic
  block, whose multiplicity is the full count of Q_1-orbits on the
  512 points; the torsor `W` rotates that whole block, mixing the
  wire into it, so by the block-trace theorem only the BLOCK TRACE is
  locked there — and the enemy can zero a block trace whenever the
  block is large (unitarity permits any value in the disk).  The
  truncated-shift-pairing suggestion above is therefore wrong as a
  floor source: the trivial block carries no rigidity.  The floor
  carriers are exactly the multiplicity-ONE twisted blocks fed by
  multiplicity-one Z-blocks (rigid phase in, rigid phase out, weight
  `w_sigma` locked into the quadratic form).  The decisive census —
  which twisted blocks have `mtilde_sigma = 1` and which Z-blocks
  feed them — is the block-structure output of the running joint
  probe; the uniform floor holds iff that census carries enough
  locked weight along the tower, per the transfer-operator mechanism.
- **The census plausibly grows with the level (2026-08-21, by
  hand).**  The boundary concern has a structural counter: the
  parahoric is always a 2-group whose abelianization GROWS with the
  level — the diagonal units `(Z/2^a)^* ~ Z/2 x Z/2^(a-2)` contribute
  two growing character parameters (the root directions die mod
  squares/commutators, but the torus does not) — while deep-layer
  point stabilizers shrink as orbits grow, so ever more characters
  are trivial on the normal closure of a stabilizer, and the
  one-dimensional census should grow roughly with the layer count,
  with generic characters appearing in FEW layers (level-localized ⇒
  multiplicity one ⇒ carriers in the bulk).  The uniformity of the
  one-step floor thus reduces to a concrete counting problem: torus
  characters of the parahoric versus layer stabilizer closures, per
  level.  Hand-tractable at `a = 4` and decisive; the running probe's
  block census gives the `a = 3` ground truth to calibrate the count.
- **Multiplicity structure RESOLVED by pullback nesting (2026-08-21,
  by hand).**  Layer `j+1` contains the full pullback of layer `j`
  (primitive vectors mod `2^(j+1)` fiber over those mod `2^j`), so
  the layer contents nest: `448 = 56 (pullback) + 392 (native)` and
  `392 = 84 + 112 + 84 + 112` exactly.  Hence the trivial has
  `m = 4`, the 6-dim `m = 3`, the 21- and 28-dim `m = 2` (same irrep
  repeated by pullback), and the four NATIVE deep constituents
  `84a, 84b, 112a, 112b` are pairwise-distinct irreps of
  MULTIPLICITY ONE: profile `16+9+4+4+1+1+1+1 = 37`, uniquely
  resolving the earlier two-scenario ambiguity.  Consequences invert
  the census heuristic: every one-dimensional slot is fed by
  `m >= 2` irreps and carries NO rigidity; the rigid `Z`-phases are
  exactly the four native deep blocks, and the floor carriers are
  their BIG parahoric constituents — four `32`-dim slots (weight
  `1/16` each) and the `16`-dim slots — provided the constituents of
  `84a/84b` and `112a/112b` are distinct characters (`mtilde = 1`),
  which is precisely what the running block census decides.  The
  measured floor `~0.149` matches two effective 32-dim carriers
  (`2/16 = 0.125`), suggesting one pair shares and one separates.
  UNIFORMITY MECHANISM IDENTIFIED: every level's native layer brings
  fresh multiplicity-one deep irreps (new principal series), so the
  locked weight plausibly stays a constant fraction of the space at
  every level — the bulk-carrier existence the transfer mechanism
  needs, now with a named source.
- **Native-block anatomy (2026-08-21, by hand).**  The native
  layer-3 part decomposes by fiber characters: pairs
  `(vbar in prims_4, xi in (F_2^3)^* \ 0)` with the single invariant
  `<xi, vbar mod 2> in F_2`, giving orbits of sizes
  `56*3 = 168 = 2*84` and `56*4 = 224 = 2*112` — the natives are
  monomial sheaves over the two pairing-orbits, each splitting into
  two equal irreps via a stabilizer sign character.  `SL_3(Z/8)` is
  perfect, so `84a, 84b` (and `112a, 112b`) are NOT global character
  twists of each other; a diagonal element of `GL_3 \ SL_3`
  normalizes the parahoric and plausibly swaps each pair, so
  separation of their deep parahoric constituents (`mtilde = 1`, the
  floor carriers) is equivalent to non-invariance of those
  constituents under the swap — one finite character check, with the
  probe's block census as ground truth.  The whole prototype floor
  is now derived structure: monomial natives, swap symmetry, and the
  block-trace theorem.
- **Machine confirmation of the derived structure (2026-08-21,
  interim harvest).**  The joint probe's block extraction returns
  `profZ = [[1,84],[1,84],[1,112],[1,112],[2,21],[2,28],[3,6],[4,1]]`
  — exactly the hand-derived pullback-nesting profile: four
  multiplicity-one native blocks, `21/28` at `m = 2`, the 6-dim at
  `m = 3`, the trivial at `m = 4`.  The v4 floor over the exact
  unitary manifold at the control dictionary converges to `~0.142`
  (48 restarts, `unit_err = 0`), and the joint `(K, W)` floor is
  holding at `~0.17` over the early torsor sweep: the residual
  freedom is NOT collapsing the floor.  The twisted census head shows
  multiplicity-one blocks exist (`[1,2]` and `[1,4]` entries); the
  decisive 16- and 32-dim block sizes are being read out.
- **Model-scope clarification and the v6 design (2026-08-21).**  Two
  points that a later reading could trip over.  (i) The probe's
  single-space six-pair model UNDER-constrains the enemy (the true
  microstate satisfies far more relations), so its measured floors
  are meaningful lower-bound-style signals for this vertex choice,
  and the block-trace analysis with `Q_1 = <phi-images>` applies to
  it as stated; the two-level pairing discussion concerns the
  FLEXIBLE (dimension-padded) formulation only.  (ii) Sharper: the
  control defect `6.92` sits above the spectral floor `2.73 > 0`,
  which proves the permutation-representation vertex model can NEVER
  host the enemy at all — the six fixed relators cannot vanish there,
  because its generator spectra are not doubling-compatible.  This is
  the approximate-doubling-invariance wall certifying itself in one
  number.  The enemy-compatible testbed (v6) must therefore build the
  vertex representation ON solenoid-compatible spectra — layered
  towers with descent-compatible weights, the enemy's own necessary
  structure — and measure the carrier census and floor THERE.  The
  present prototype remains the mechanism testbed where the
  block-trace machinery and the carrier anatomy were established.
- **General-level census DERIVED (2026-08-21, by hand).**  The
  native anatomy generalizes: layer-`j` natives are monomial sheaves
  over pairs `(vbar in prims mod 2^(j-1), xi)` with the single
  pairing invariant, giving two orbit-sheaves of dimensions
  `3 |prims_(j-1)|` and `4 |prims_(j-1)|` — verified at `j = 2`
  (`21 = 3*7`, `28 = 4*7`, unsplit) and `j = 3`
  (`84+84 = 3*56`, `112+112 = 4*56`, sign-split).  For `j >= 3` the
  stabilizer sign character splits each sheaf, so EVERY level adds
  four fresh multiplicity-one native blocks: the rigid-carrier
  supply grows linearly in `a`, with per-layer weight a constant
  fraction of the layer.  The uniformity mechanism of the transfer
  argument is therefore DERIVED structure, not a hope: what remains
  per layer is (i) the separation (swap-invariance) of each pair's
  deep parahoric constituents and (ii) the `M`-form pairing entries
  under the shift-by-two descent — both finite, layer-periodic
  checks.  This also replaces heavy numerics: the branching tables
  at every level are now analytically accessible through the
  monomial-sheaf structure (Mackey theory over the parahoric), so
  the uniform one-step floor is a symbolic computation, not an
  optimization.
- **Locked-form status: canonical matching, shift pairing, and an
  honest vacuity at the prototype (2026-08-21).**  Since
  `phi = Ad(h^{-1})` is an abstract isomorphism `Q_0 ~ Q_1`, the
  dictionary matching of isotypic centers is CANONICAL
  (`tau <-> tau o phi^{-1}`), and conductor bookkeeping makes the
  locked diagonal a twisted SHIFT pairing on the native-phase chain:
  layer-`j` carrier phases couple to layer-`(j-1, j-2)` content.
  Consequence at `a = 3`: there is only ONE native layer, its shift
  partners are shallow multiplicity-`>= 2` content whose block
  traces the enemy zeroes, and free phases close the polygon — the
  first-order bound `(BTR3)` is VACUOUS at the prototype.  The
  measured floor `~0.142-0.17` is therefore a SECOND-ORDER
  phenomenon: the outer disk estimate on each C-numerical range is
  not jointly attainable, i.e. the joint range of the coupled blocks
  is strictly smaller than the product of disks.  Two consequences:
  (i) the prototype floor proof needs the joint-range rigidity, not
  block traces — a sharper finite question; (ii) for the TOWER the
  first-order mechanism revives: with many native layers the shared
  phases enter many carriers with different partners, and the floor
  becomes the frustration index of the carrier-coupling network — a
  computable spectral quantity, and the correct uniformity target
  for large `a`.
- **Correction (2026-08-21, same hour): the positivity claim below is
  WRONG as stated.**  The phase-averaged diagonal `A_(pi pi)(W)` pairs
  the `W`-rotated channel with its transported partner — two DIFFERENT
  vectors — so it is sign-indefinite and itself `W`-tunable; the
  "sum of squared channel masses" reading was an error.  What
  survives: phase-averaging as the right analysis coordinate system,
  and the sharpened empirical question — with ~300 free parameters
  against a single complex constraint, generic solvability argues the
  measured `0.142` could be an annealing artifact, while v2's
  independent gradient method found the same barrier, so the truth is
  genuinely undecided.  The decisive experiment is a TARGETED
  cancellation solver: Newton/least-squares on the two real
  constraints `Re z = Im z = 0` over the exact `(K, W)`-manifold from
  many starts.  If it finds zeros: no fixed-`V` floor, and the
  per-level hopes move to `V`-constrained formulations.  If it
  provably stalls at `~0.14`: the rigidity is real and the mechanism
  hunt resumes with the singular data.  Honesty note kept deliberately
  above the superseded bullet.
- **Second-order mechanism candidate (SUPERSEDED, see correction
  above): phase-averaging positivity
  (2026-08-21).**  The leak is QUADRATIC in `K` (it enters both sides
  of `<W K W*, V_0* K V_0>`), so averaging over the free native
  phases kills the oscillating off-diagonal terms and leaves the
  phase-invariant diagonal `P = ` a nonnegative SUM OF SQUARED
  channel masses.  The floor obeys `min |leak| >= P - (oscillation
  range)`, so the measured `~0.142` is P-dominance, and the earlier
  first-order vacuity is explained: block-trace bounds see only the
  oscillating part.  The provability route is now sharp: `P` is
  controlled by the SINGULAR spectrum of the compressed conjugation
  `Phi` on trace-zero (not its Hermitian part, whose indefiniteness
  was a red herring), paired with the unitarity sum rule
  `sum_sigma ||K_sigma-component||^2 = 1`: a lower bound on `P` needs
  `Phi` to retain a definite fraction of orbit mass on the structured
  subspace where unitarity forces `K` to live.  Next computations:
  the singular value distribution of the `37 x 37` `Phi`-matrix, and
  the oscillation-vs-P comparison; next theorem target: the
  phase-averaging floor lemma
  `min |leak| >= P - osc` with `P` bounded below via the sum rule.
- **Carrier census COMPLETE (2026-08-21,
  `experiments/sl3-q1-census.json`).**  The twisted commutant has
  exactly `34` multiplicity-one blocks, of dimensions
  `2^4, 4^8, 8^8, 16^10, 32^4` — summing to `392`, EXACTLY the native
  mass: every constituent of every native block is separated (the
  swap identifies nothing), each matching the derived branchings
  (`84: 2,2,4x4,16,16,32`; `112: 8x4,16x3,32`) block for block, and
  `sum mtilde^2 = 34 + 60 + 27 + 144 = 265` on the nose.  No
  one-dimensional character is a carrier (`mtilde in {2,3,12}`), as
  hand-predicted.  So 77% of the space is phase-locked through just
  FOUR shared native phases — but the locked partner data `y_sigma`
  rides on shallow multiplicity-`>= 2` traces the enemy can zero,
  confirming with exact numbers that the `a = 3` first-order form is
  vacuous and the measured floor, if real, is second-order.  The
  cancellation solver now decides reality; the census stands as the
  complete structural input for whatever mechanism survives.
- **Corrected second-order mechanism: the phase-free core is the
  native retention of the dictionary (2026-08-21).**  Two exact
  structural facts sharpen everything.  (i) On every
  multiplicity-one twisted block the torsor element is a SCALAR, so
  `W` is inert on the entire native mass (77% of the space): the
  joint `(K, W)` floor and the `K`-only floor coincide on the locked
  sector.  (ii) Expanding the leak in the four native phases, the
  diagonal terms `t conj(a t) = conj(a)` are PHASE-FREE: the leak
  contains an additive constant

  `c*(V) = sum_(mtilde=1) w_sigma conj(a_(sigma, pi(sigma)))`,

  the native-sector retention of `Ad(V)` — the amount of native mass
  the dictionary keeps self-aligned — which NO enemy freedom (native
  phases, shallow unitaries, torsor) can touch.  Every tunable term
  has a FIXED total range `R(V)` because unitarity of `K` fixes every
  block mass (nothing is tradeable), so the fixed-`V` floor holds iff
  `|c*(V)| > R(V)` — one computable inequality; and the `V`-escape
  seen at defect cost `+13` is the enemy driving `c*(V)` toward zero
  along the dictionary manifold, making the true wall the tradeoff
  curve `|c*|` versus defect.  This supersedes both the vacuous
  first-order form and the erroneous positivity claim, and it is
  exactly computable from the control dictionary and the census.
- **The inversion: the floor is the residue of dictionary
  impossibility (2026-08-21).**  A PERFECT dictionary implements the
  level shift, which maps the native sector off itself (level
  compression), forcing `c* ~ 0`; so nonzero retention is not a
  virtue of the dictionary but the signature of its FAILURE — and at
  fixed level the failure is proven (the positive spectral floor).
  The mechanism chain is therefore: fixed-level dictionary
  impossibility `=>` un-implementable part of the shift `=>` retained
  native self-alignment `c*(V) > 0` on the whole low-defect manifold
  `=>` leak floor `|c*| - R`.  The awaited computation of `c*` at the
  control dictionary tests this quantitatively (prediction:
  `|c*| ~ 0.14`, the measured floor), and v2's `+13`-defect escape is
  the enemy buying dictionary quality it cannot afford at this level.
  TOWER version: at deep levels the six-pair spectra become
  compatible (`OT ~ 4^(-a)`), but the shift is mass-asymmetric — the
  top two layers' native mass (asymptotically everything) has no
  shift-image to align with — so the question becomes whether the
  dictionary relations force enough of `V`'s mass flow to leave a
  retention residue at the top: `inf {defect : c* = 0}` versus
  `inf {defect}`, a gap statement along the tower.  Next experiment
  (v7): trace the `|c*|`-versus-defect frontier by joint
  minimization; next theorem target: a lower bound for `|c*|` in
  terms of the spectral-floor gap at fixed level.
- **Exact vanishing of the transported core (2026-08-21, by hand).**
  The dictionary transports parahoric projections
  (`V P_sigma V* ~ P^A_(sigma o phi)` up to defect), so the
  perfect-transport value of the phase-free core is the structure
  constant `c*_0 = (1/512) sum_sigma Tr(P^A_(sigma o phi) P_pi(sigma))`
  — and this VANISHES IDENTICALLY: `sigma o phi` has shifted-down
  conductor (shallow), while the native `pi`'s source-parahoric
  constituents are all deep, so the isotypics are disjoint.  Hence
  `c*(V) = 0 + (defect-carried residue)`: retention is EXACTLY a
  defect phenomenon, the inversion is now an exact statement, and the
  fixed-level floor question is precisely how the un-removable
  minimum defect (proven positive by the spectral floor) distributes
  into `c*` across the low-defect manifold — the v7 frontier
  `|c*|` versus defect is the whole story, and any lower bound must
  couple the two through the conductor-mismatch geometry rather than
  through transport identities.
- **The phase-free core measured AND its positivity proved
  (2026-08-21, `experiments/sl3-cstar-compute.json`).**  At the
  control dictionary, `c* = 0.380864`, exactly real — and the reality
  is structural: each diagonal term is
  `Tr(P_sigma V* P_pi V) = ||P_pi V P_sigma||_F^2`, a Frobenius
  square, so the core is a SUM OF SQUARES — `c*(V) >= 0` always,
  positive unless the dictionary moves every native entirely off its
  own constituents.  (The earlier positivity retraction applied to
  the W-rotated diagonal; on multiplicity-one blocks W is inert and
  the squares survive rigorously.)  The measured floor `0.142` now
  reads as core minus achievable cancellation
  (`0.381 - 0.24`), and the fixed-level floor program is: lower-bound
  the native self-overlap mass `c*(V) = sum ||P_pi V P_sigma||_F^2 / D`
  over the low-defect manifold (the conductor-mismatch theorem says
  perfect transport would kill it, the spectral floor says perfect
  transport is impossible), and upper-bound the cancellation range.
  Both are concrete; the frontier trace (v7) quantifies them
  together.
- **Rigorous floor ledger at the control dictionary (2026-08-21,
  `experiments/sl3-bmatrix.json`,
  `experiments/sl3-rigorous-floor.json`).**  Exact numbers: the
  native 4-phase quadratic form `B` has continuous minimum
  `min_t |t* B t| = 0.2407` (grid + polish; matches the hand
  max-cut/XY analysis: `maxcut ~ 0.194` at the split
  `{84a,112a}|{84b,112b}`-pattern), the JOINT shallow coupling is
  `0.1014` (aggregated nuclear norms — the independent-sup value
  `0.137` was beatable), and the `mtilde >= 2` sector still carries
  the crude Cauchy-Schwarz `0.2344`, leaving the proved bound at
  `-0.095` against a measured floor of `+0.142`.  The remaining gap
  is pure bookkeeping: the three parts draw on ONE unitarity budget
  (the shallow mass `120/512` enters both non-native parts, and the
  block-diagonal sector mass of `V* K V` is genuinely below its
  cap), so the separated sups over-count; the next tightening is the
  aggregated nuclear bound over the joint coefficient operator.
  Assessment: with `c* = 0.381` proved positive as a sum of squares,
  the native minimum `0.2407` exact, and three independent
  optimizers stalling at `0.14-0.17`, the fixed-`V` floor is
  established beyond reasonable doubt and NEARLY proved; but since
  this vertex provably cannot host the enemy, the proof-completion
  is not goal-critical — the goal-critical target remains the
  uniform two-level version, for which tonight's derived structures
  (layer nesting, native freshness, conductor mismatch, sum-of-
  squares core) are the transferable machinery.
- Proved below by assembling established inputs; see the proof route.
  The one step that is a HYPOTHESIS here and a theorem at `SL_2` is
  vertex near-exactness: `SL_3(Z)` HS-stability is open (it is the
  Dogon--Vigdorovich program), so this claim describes the near-exact
  sector rather than eliminating the complementary outlier sector —
  matching the lane's standing division of the battlefield.
