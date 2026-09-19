---
rg: 2
id: lambda-exact-face-closes-at-p-three
kind: claim
title: Open p-three Lambda-exact closure from metaplectic flux
distinct_from:
  lambda-exact-face-of-the-collapse-closes: that closed the regular-type sectors at p = 2 and drove the enemy to the unique flat profile with the flux as the terminal decision; this decides the flux for p = 3 (mod 4) and closes the WHOLE Lambda-exact face for the (SL_3(Z), SL_3(Z[1/3])) pair, flat profile included.
  odd-congruence-lambda-exact-sector-collapses: that closes levels coprime to p by the Weyl slot evaluation; this closes the complementary p-power and mixed levels at p = 3 by the Weil-Rao flux obstruction — the two mechanisms partition all levels for the p = 3 pair.
  sl3-pair-relative-commutant-route: that is the p = 2 instance of the collapse; this moves the lane's decided face to the p = 3 instance, where the metaplectic arithmetic is favorable, and leaves p = 2 as the constructive-side probe (trivial flux there, exact Gauss-sum computation).
---

OPEN CLAIM. For `p = 3 (mod 4)` and the pair
`Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`, there is NO enemy of the
collapse `(RC3)` with `Lambda`-exact microstates at ANY levels: the
`Lambda`-exact face of `(RC3)` is closed for the `p = 3` pair.

The current assembly does not prove this claim. Its fixed-shift-to-flat
step is invalidated by
`fixed-shift-invariance-does-not-force-flat-profile`, and the independent
identification of the actual parahoric transport loop with the normalized
Weil--Maslov loop remains open. The flux computation below is therefore a
candidate terminal obstruction after those two seams are closed, not a
completed closure theorem.

There is now a sharper repair and a sharper obstruction.  Full flatness is
unnecessary: `one-shift-folner-mass-is-depth-parity-balanced` proves that
one-step shift invariance alone puts asymptotic mass `1/2` on odd conductor
depth.  Hence an authenticated alternating `p=3` holonomy would already
close the spread profile by the elementary bound `(PBF3)`.

Moreover `p3-minus-flux-is-cancelled-by-pauli-multiplicity` gives an exact
finite-dimensional countermodel to the bare flux inference, and
`p3-full-parahoric-interlock-enforces-inverse-mackey-cocycle` shows that the
full finite parahoric table does not repair it.  Clifford factorization makes
the multiplicity transports carry the inverse oscillator cocycle; the finite
twisted regular representation realizes that cancellation exactly.  Hence
Stone--von Neumann uniqueness, the scalar Gauss computation, and all
single-packet Weyl/opposite-root multiplication relations do not obstruct a
finite packet.  Steps 4--5 below are invalid for general multiplicity
packets.  The remaining flux route would need a capacity bound, genuinely
noncohomologous packet classes on one authenticated reservoir, or cocycle rank
growing beyond the model.  Two native Weyl/opposite-root charts do not supply
the second option: `two-native-p3-weyl-charts-have-the-same-mackey-class`
computes equal restricted classes, canceled by one twisted-regular gauge.
Nor does a fixed three- or six-chart cycle repair it:
`finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge` constructs one
inverse twisted-regular groupoid functor canceling all native transition
loops exactly.  Only a capacity-growing or non-groupoid global incidence can
revive the flux route.
The naive depth-capacity version also fails on the canonical regular blocks:
`regular-p3-parahoric-bands-have-twisted-gauge-surplus` computes `dim(pi)`
copies of the full inverse twisted-regular module inside every oscillator
band.  Folner/parity depth mass is a direct sum of already cancellable bands;
it does not make their cocycle ranks act on one reservoir.
A fixed denominator/Weyl transition also fails to make the reservoir
stationary.  By
`denominator-transport-only-conjugates-p3-multiplicity-reservoirs`, every
matched transition is `W_a tensor V_a` with arbitrary `V_a`; the gauges can
be removed along the depth tree and recycled on growing Folner boxes with
word-square defect `O(1/N)`.  The remaining input must be a raw mixed-root
incidence which is not merely packet normalization or depth transport.
The first such-looking raw incidence also remains blind:
`p3-denominator-steinberg-word-is-multiplicity-blind` shows that
`[h x_12(1)h^(-1),x_23(1)]=x_13(3)` cancels the multiplicity gauge before
the root commutator is evaluated.  The needed relation must expose a named
same-object selector/global building coordinate, rather than another
Chevalley triangle.

Assembly of the proof, every piece prime-generic or computed here:

1. Levels coprime to `p`: closed by the Weyl slot evaluation
   (`odd-congruence-lambda-exact-sector-collapses`, coprimality-only
   form).
2. Regular-type `p`-power and bounded-gauge levels: closed by the
   Kazhdan floor (`lambda-exact-face-of-the-collapse-closes`,
   prime-generic).
3. All remaining profiles: forced FLAT by the shift-invariance
   theorem (min-overlap bound in all coweight directions), hence
   carrying equal asymptotic mass on the deep oscillator bands,
   which have density one among deep constituents (orbit-method
   genericity for the congruence duals).
4. **Invalid at unrestricted multiplicity.** On oscillator bands the canonical transport is pinned by
   Stone--von Neumann uniqueness to the finite Weil intertwiner, and
   its composition flux for the pair `(h, h')` equals the Hilbert
   symbol `(p, p)_p` by the Weil--Rao index identity together with
   the root-data pairing `h = alpha_1-vee(p) alpha_2-vee(p)`,
   `h' = alpha_2-vee(p)`, whose BLS commutator exponent is the
   off-diagonal Cartan entry: `<h, h'> = (p,p)^(+-1) = (p,p)_p`,
   convention-proof since the symbol is `+-1`-valued.
   `(p, p)_p = (-1 | p) = -1` for `p = 3 (mod 4)`.
5. **Invalid at unrestricted multiplicity.** A nontrivial flux band cannot carry conjugator mass (the
   transports cannot be made consistent on it), so the flat
   profile — which must place its share of mass there — admits no
   conjugator: the flat tower dies, and with it the last
   `Lambda`-exact habitat.

CONSEQUENCE.  For the `p = 3` pair, any enemy of `(RC3)` — hence the
only obstruction on this lane to the finitely presented
non-hyperlinear group `G_3 = < SL_3(Z[1/3]), t | [t, SL_3(Z)] = 1 >`
through the established reduction — must consist of UNIFORM OUTLIERS:
`Lambda`-microstates at uniform positive distance from every genuine
finite-dimensional representation of `SL_3(Z)`.  The correctability
hole, instantiated at `p = 3` with any congruence targets (all
levels now usable), is exactly equivalent to `(RC3)` for this pair.

DEPENDENCIES, honestly listed: classical (Weil--Rao index identity;
Gauss-sum evaluations; Stone--von Neumann uniqueness; BLS/Matsumoto
torus pairing for simply-connected groups) — literature-solid;
in-graph theorems (items 1-3) — established today; the orbit-method
density of generic bands in congruence duals — standard but cited at
statement level; and the identification of the canonical flat-tower
transport with the Weil intertwiner on oscillator bands via
Stone--von Neumann — the one step whose formal write-up is the
route's charge and whose failure mode (a non-canonical normalization
evading the pinning) is explicitly what the route excludes.

## Attempts

- **Weak-u.c.p. exactification reaches exactly this face, not an exact
  ambient finite-representation theorem (2026-08-21 audit).**  Apply
  `kazhdan-subgroup-weak-ucp-exactifies-microstates` to a hypothetical
  hyperlinear approximation of

  ```text
  G_3=<Gamma,t | [t,Lambda]=1>,
  Lambda=SL_3(Z),   Gamma=SL_3(Z[1/3]).                  (P3F1)
  ```

  Assuming `sl3-z-weakly-ucp-stable`, after an `o(1)` change and
  `1+o(1)` dimensional adjustment one obtains finite matrices with

  ```text
  sigma_n:Lambda -> U(d_n)       an EXACT representation,
  k_n in sigma_n(Lambda)'        EXACTLY,
  V_n=phi_n(h)                   only an approximate parahoric
                                  intertwiner,                  (P3F2)
  ```

  while all fixed `Gamma` relators have defect `o(1)` and
  `tr(phi_n(g))->delta_e(g)` for every fixed group word.  Superrigidity and
  CSP factor `sigma_n` through some `SL_3(Z/N_n)`, with completely arbitrary
  isotypic multiplicities.  Thus the weak-u.c.p. theorem eliminates the
  lattice-outlier sector for this HNN argument, but it neither exactifies
  `V_n` nor turns `phi_n|_Gamma` into a genuine representation of `Gamma`.

  This distinction is necessary.  A uniform theorem about one arbitrary
  exact finite representation `sigma` is false: the trivial representation,
  and more generally every constituent factoring through a common shallow
  quotient of the two parahoric actions, has an exact twisted intertwiner.
  The regular trace condition excludes the trivial representation only as a
  whole limiting model; it does not forbid moving shallow constituents whose
  mass is spread across growing levels.  This is precisely the
  general-weight/Folner profile left alive by
  `fixed-shift-invariance-does-not-force-flat-profile`.

  Therefore the remaining assertion has the following sharp finite-matrix
  SEQUENTIAL form, not a single exact-representation form: for every exact
  congruence sequence `sigma_n` with pointwise regular limiting character,
  every sequence `V_n` satisfying the fixed denominator/parahoric relations
  with defect `o(1)`, and every `k_n in sigma_n(Lambda)'`, one must have

  ```text
  ||[k_n,V_n]||_2 ->0.                                  (P3F3)
  ```

  The coprime-to-`3` part of this statement is already
  `odd-congruence-lambda-exact-sector-collapses`.  The regular-type
  `3`-primary part has the direct floor proved in the next bullet.  The
  unresolved input in `(P3F3)` is arbitrary scale-spread `3`-primary
  isotypic weight (including the general-weight form of the bounded-gauge
  reduction).
  Consequently weak-u.c.p. exactification is a correct preprocessing theorem
  and makes this claim sufficient for the root goal, but supplies no new
  control on its invalidated flatness step or on the parahoric-to-Weil flux
  dictionary.

  There is also a route-level consequence of the newly established
  `kazhdan-weak-ucp-stability-is-flexible-stability`: because `Lambda` has
  property `(T)`, the hypothesis `sl3-z-weakly-ucp-stable` already gives the
  flexible correction needed by the thin co-dense HNN route
  `non-hyperlinear-from-sl3-z-weak-ucp-stability`.  Thus this p-three face is
  no longer needed for the SHORTEST conditional route that assumes weak-u.c.p.
  stability.  It remains a genuine independent theorem about `(RC3-p3)` and
  would still be needed for any route that avoids stability of `SL_3(Z)`.

- **The regular-type p-three Kazhdan floor is exact.**  The proof of
  `lambda-exact-face-of-the-collapse-closes` was written at `p=2`, but its
  finite kernel calculation extends directly to the present prime.  Put

  ```text
  h=diag(3,1,1/3),
  A=(e_21(3),e_31(9),e_32(3),e_12(1),e_13(1),e_23(1)),
  B=hAh^(-1)=(e_21(1),e_31(1),e_32(1),e_12(3),e_13(9),e_23(3)).   (P3F4)
  ```

  `Lambda_0=<A>` has finite index in `SL_3(Z)`, hence a Kazhdan pair
  `(A,epsilon_3)`.  At level `3^a`, `a>=3`, the image in the `A`-side
  quotient of the `B`-kernel is exactly the upper-unitriangular packet with

  ```text
  (12),(23) entries in 3^(a-1)Z/3^aZ,
  (13) entry          in 3^(a-2)Z/3^aZ.                 (P3F5)
  ```

  It has order `3*3*9=81`; transpose-inverse identifies the sizes of the
  `A`- and `B`-side quotients.  Therefore, on a regular-type module, the
  common Schur-support fraction of the two twisted representations is
  exactly `1/81`.  Projecting a unitary onto the intertwiner space has
  operator norm at most one, so its normalized HS distance from that space
  is at least `sqrt(80/81)=4 sqrt(5)/9`.  Property `(T)` gives the uniform
  finite-level floor

  ```text
  max_i ||V sigma(A_i)V^*-sigma(B_i)||_2
     >= epsilon_3 * 4 sqrt(5)/9.                         (P3F6)
  ```

  Hence regular-type pure `3`-power towers cannot support `(P3F2)`.  This
  proof uses neither the invalid flatness assertion nor the Weil-flux
  dictionary.  It does not extend to arbitrary isotypic weights: those may
  concentrate in the common shallow quotient, exactly the scale-spread
  escape described above.

- **The optimal weighted Kazhdan bound is only total variation; no Hardy
  gap survives deep scale spread.**  Let the `A`- and `B`-side restrictions
  of an exact `Lambda`-representation have normalized dimension weights
  `alpha_theta,beta_theta` on their common irreducible `Lambda_0`-types.
  Schur orthogonality gives, for every unitary router `V`,

  ```text
  ||P_Inv(V)||_2^2 <= sum_theta min(alpha_theta,beta_theta)
                    =1-TV(alpha,beta).                  (P3F7)
  ```

  Hence the Kazhdan argument gives exactly

  ```text
  max_(s in A)||sigma_A(s)V-V sigma_B(s)||_2
     >= epsilon_3 sqrt(TV(alpha,beta)).                 (P3F8)
  ```

  This dependence is order-sharp at the abstract isotypic-router level.
  Match subspaces of dimension `min(alpha_theta,beta_theta)` inside every
  common type, map them by exact intertwiners, and complete the resulting
  partial isometry arbitrarily to a unitary on the unmatched mass.  The
  matched part has zero generator defect and the complement has mass
  `TV(alpha,beta)`, so every generator defect is at most
  `2 sqrt(TV(alpha,beta))` (up to rational rank rounding).  Thus property
  `(T)` cannot improve `(P3F8)` to a positive floor without additional
  information on the type-transition graph.

  In the scale-shift situation take the deep triangular profile

  ```text
  mu_N(N+j)=2(j+1)/((N+1)(N+2)),   0<=j<=N,             (P3F9)
  ```

  and zero elsewhere.  It has total mass one,

  ```text
  TV(mu_N,S mu_N)=max_j mu_N(N+j)=2/(N+2)->0,           (P3F10)
  ```

  while for every fixed shallow cutoff `L`,
  `sum_(j<=L)mu_N(j)=0` once `N>L`.  Consequently all constraints obtainable
  from finitely many fixed kernel/regular-trace tests are compatible with
  vanishing shift energy.  Product triangular profiles give the same escape
  simultaneously for every fixed finite set of the two coweight shifts.

  This is an exact NO-GO for a weighted Hardy/Kazhdan proof based only on
  isotypic weights and fixed shifts; it strengthens the earlier failure of
  flatness by showing that the best possible Kazhdan modulus itself vanishes
  on profiles which have already escaped every fixed shallow level.  Scope:
  the matched-router construction is an exact finite Schur-module model, not
  yet a model of all `Gamma` denominator relations.  Promoting it to an
  actual enemy requires the branching dictionary to realize those common
  type blocks coherently.  Conversely, closing the face now requires a
  relation which the Schur-module model cannot satisfy: the normalized
  Weil--Maslov loop/flux, or another genuinely non-Folner matrix-coordinate
  transition.  No scalar Hardy inequality remains available.

- **Audit correction (2026-08-21).** Fixed coweight-shift invariance on a
  growing scale lattice is only a Folner/delocalization statement.
  Triangular product profiles are invariant under every fixed shift and
  have vanishing atoms but stay total-variation distance `1/4` from Haar;
  see `fixed-shift-invariance-no-flat-profile-proof`. In addition,
  Stone--von Neumann uniqueness leaves edge scalars whose closed product is
  the flux being claimed, so the parahoric-to-Weil normalization dictionary
  recorded in `artifacts/flux-identification-lemma-protocol-2026-08-21.md`
  is still required. Neither correction refutes the target RCC statement.

- **Two-sided closure of the fork.**  At `p = 2` the same arithmetic
  gives flux `+1` (all 2-power symbols trivial), which is exactly
  why every closure mechanism failed at `2`: the lane's inability to
  close the `p = 2` tower was the metaplectic triviality speaking.
  The `p = 2` flat tower is now the CONSTRUCTIVE target: if its
  remaining Behr-relation obstructions also vanish, `G_2`-side
  hyperlinearity phenomena follow — the fork is decided prime by
  prime, exactly as the Hilbert symbols dictate.
- **What remains for the goal at p = 3.**  Only the uniform-outlier
  sector: microstates far from all genuine representations.  Every
  instrument of the lane now aims at one target for one pair.
- **Arithmetic engine operationally confirmed; instrument autopsies
  absorbed (2026-08-21, sioux, witness-clean).**  Two naive
  instruments were VOID by their own witnesses and are recorded in
  `artifacts/svn-pinning-derivation-2026-08-21.md`: the plain-DFT
  loop was algebraically trivial (F^4 = 1 — no anomaly without
  quadratic phases), and no Levi SL_2 exists in the SL_3 unipotent
  frame (Weyl elements leave the upper triangle), which also
  exposed that the hexagon's double-weight direction ROTATES
  (h: e_13, h': e_23, h'': e_12) — the flux's correct formal home
  is the Lion--Vergne / Maslov triple index.  The corrected
  instrument (verified primitives only, phase-free witnesses
  against Weyl-symmetrized Heisenberg operators at 1e-15) then
  measured the canonical anomaly classes on l^2(Z/p^k):
  A(1) = (F_0 mult(1))^3 P = (2|q) eps_q exactly at seven levels,
  and the quotient A(+1)/A(-1) = (-1|q) exactly — the capstone's
  (p,p)_p class realized as a canonical operator holonomy,
  alternating per tower level at p = 3 and trivial at p = 5, with
  F_0^4 = 1 as the no-anomaly control.  The flux-identification
  dependency is now one precisely-shaped lemma: the DICTIONARY
  expressing the S_3 hexagon of parahoric band transports as a
  Maslov triple of an explicit quadratic form built from two
  coweight legs (artifact, section C).
