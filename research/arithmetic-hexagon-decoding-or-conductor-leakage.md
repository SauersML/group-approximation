---
rg: 2
id: arithmetic-hexagon-decoding-or-conductor-leakage
kind: claim
title: Arithmetic root microstates decode one A2 hexagon carrier or pay conductor leakage
distinct_from:
  six-edge-holonomy-energy-ledger-is-scale-free: that proves the analytic energy inequality after carriers and transitions are supplied; this is the matrix-coordinate extraction of those objects from growing congruence and periodic root spectra.
  affine-leavitt-boundary-shear-payment: that charges boundary expansion in the Leavitt coefficient system; this is the arithmetic SL3 root-depth version using the six-chamber Coxeter holonomy.
  same-orbit-closure: that prevents rectangular enlargement for paired Leavitt quotients; this permits enlargement but requires every escaped piece to descend in conductor depth and enter a fixed-depth mass recurrence.
---

OPEN.  Fix a depth `N`.  For canonical normalized-HS microstates of

```text
C=SL_3(Z) < A=SL_3(Z[1/2])
```

with the balanced commuting-conjugate lamp projections `P,Q`, decode for the
first `N` dyadic conductor layers:

1. six rounded Heisenberg chamber packets;
2. carrier projections `R_(k,w)` for the six Weyl chambers;
3. supported chamber transitions on their common surviving carrier; and
4. first-exit projections measuring failure of a transition to stay in that
   carrier,

so that for constants depending on `N` but not matrix dimension,

```text
sum_(k<N,w) edgeEnergy_(k,w)
  <= C_N (def(U)+sep_(F_N)(U)),                          (AHD1)
```

and escaped mass either is orthogonal first-exit mass or enters the next
shallower conductor layer.  There must be a fixed `kappa>0`, independent of
depth and dimension, for which the marked interior-overlap mass `m_k` obeys

```text
m_(k+1) <= (1-kappa)m_k
           + C_k (def(U)+sep_(F_N)(U)).                 (AHD2)
```

The mechanism required for `(AHD2)` is now finite and explicit.  On the mass
which does not leak, `six-edge-holonomy-energy-ledger-is-scale-free` makes a
role-rotating four-atom sector pay at least `m_k/8`; vanishing word energy
therefore forbids that sector.  On the leaked mass, the Weyl orbit of the
directionwise kernel-join packets generates the full principal layer two
levels down; the fixed `Lambda_0` property-T gap must charge or descend it.

Iteration gives

```text
m_N <= (1-kappa)^N m_0
       + C'_N (def(U)+sep_(F_N)(U)).                    (AHD3)
```

Constants `C'_N` may grow arbitrarily with `N`.  Taking the canonical
microstate limit first and `N->infinity` second is therefore sufficient for
the fixed-depth nonhyperlinearity criterion.

## Attempts

- **The exact deep-root budget is a finite dyadic square function.** For a
  root unitary with `P^(2^N)=1`,
  `finite-dyadic-square-function-detects-deep-root-mass` proves

  ```text
  D_>1 <= (1/4)sum_(j=1)^(N-1)|P^(2^j)-1|^2
        <=(N-1)D_>1,
  ```

  where `D_>1` is the spectral projection onto root order greater than two.
  It also gives `||P^2-1||_2^2<=4tr(D_>1)`. Together with
  `bottom-a2-dyadic-face-obeys-denominator-transfer`, this makes the
  post-bottom-face escape precise: a target leak forces positive deep mass
  in at least one opposite chamber, modulo the explicit local errors.
- **One dyadic edge cannot pay that budget, optimally.**
  `cyclic-doubling-matching-hides-full-deep-root-budget` takes the diagonal
  clock of all `2^N`-th roots. Its deep mass is `1-2/2^N`, yet the optimal
  permutation matching to its squared clock has defect exactly
  `2 sin^2(pi/2^N)`. Thus no depth-independent inequality can charge deep
  mass to one scaling edge. This exact finite counterpacket identifies the
  missing synchronization: several root directions must be compared on one
  shared reservoir so that the already established six-wall seam, rather
  than a single cyclic covariance defect, pays the budget.
- **One transverse root on the same primitive reservoir is already enough.**
  `same-reservoir-weyl-pair-has-fixed-depth-doubling-gap` supplies the
  minimal multi-root seam. If `[P,Q]=zeta I` with `zeta` primitive of order
  `d=2^N`--or, more generally, the common carrier is a direct sum of
  primitive central-character fibers--no unitary `V` can simultaneously approximate
  `P->P^2` and `Q->Q^2` without

  ```text
  ||VPV^*-P^2||_2^2+||VQV^*-Q^2||_2^2
   >=2/(2^(N-1)+1)^2.
  ```

  Indeed the commutator of `P` with `Q^(d/2)` is `-I`, whereas after
  doubling it is `I`. This is a positive constant for every fixed decoded
  depth and is independent of multiplicity. Thus the analytic deep-band
  problem needs only a primitive central-character fiber with two
  transverse roots on one carrier. The still-open six-chamber work is the
  matrix-coordinate extraction which prevents their individually cheap
  cyclic matchings from living in different rectangular reservoirs.
- **The Weyl gap survives rectangular transport as a defect/leakage
  dichotomy.**  `half-period-weyl-band-transport-is-defect-or-leakage`
  allows distinct source and target root packets and a partial isometry `W`.
  If its source lies in the negative half-period commutator sector and `F`
  is the positive target sector, then, with `m=2^(N-1)`,

  ```text
  ||RW-WP||_2+m||SW-WQ||_2+||(1-F)W||_2>=||W||_2,
  m||RW-WP||_2+||SW-WQ||_2+||(1-F)W||_2>=||W||_2.
  ```

  Thus arbitrary rectangular multiplicity does not weaken the fixed-depth
  Weyl obstruction: it only exposes one explicit wrong-sector leakage term.
  The remaining arithmetic step is now sharply localized. One must identify
  that wrong half-period sector with a shallower-conductor/first-exit atom
  while constructing each of the six separate chart PVMs; after that,
  `finite-tree-first-exits-extract-an-equal-rank-global-pvm` synchronizes
  their ranks and carriers.
- **The wrong half-period sector is already inside the two-level exit
  ledger, sharply.**  For an exact `2^N`-torsion central clock `T`,
  `half-period-sector-sits-inside-two-level-exit`
  identifies

  ```text
  F_<=N-1=(1+T^(2^(N-1)))/2,
  F_<=N-2=(1/4)sum_(j=0)^3 T^(j*2^(N-2)).
  ```

  The negative half-period projection is exactly `F_=N`, while
  `F_<=N-1-F_<=N-2=F_=N-1`. Hence for every transported piece `X`,

  ```text
  ||(1-F_<=N-2)X||_2^2
   =||(1-F_<=N-1)X||_2^2+||F_=N-1 X||_2^2.
  ```

  Therefore the existing two-level first exit pays the Weyl wrong-sector
  term with constant one. The reverse comparison is false on a scalar clock
  of exact order `2^(N-1)`, and tensoring independent `42`-atom coordinate
  PVMs leaves this entire identity unchanged. Thus the local spectral
  bookkeeping is complete, but it cannot itself construct the six chart
  PVMs; root-chart covariance remains the exact extraction input.

- **Fixed odd clock packets close.**  For every fixed odd quotient packet,
  finite-group exactification plus the literal six-edge holonomy gives the
  no-leak branch with a dimension-independent modulus; this is
  `six-chamber-a2-holonomy-closes-fixed-clock-sector`.
- **Growing periodic clocks do not break the ledger.**  Their local stability
  constants may deteriorate with period, but the six-edge telescoping and
  four-atom floor do not.  A countermodel must therefore hide in the carrier
  extraction or move mass between conductor levels, not in a long holonomy
  word.
- **Moving Haar bins do not extract the carrier.**  Keeping a single circle
  coordinate under doubling has order-one total PVM transport energy, while
  moving to the conjugate solenoid coordinate gives exact covariance but
  leaves the cross-chamber multiplicity gauges unrelated.  The exact coset
  Bernoulli model passes every such tracial root/PVM test while retaining
  overlap `1/4`; see
  `moving-solenoid-bins-do-not-close-gallery-multiplicity`.
- **Pairwise walls are insufficient.**  Exact regular wall rotations from
  `adjacent-a2-chambers-share-only-commuting-wall` satisfy every pairwise
  shared-root moment.  Closing the six-edge carrier, rather than improving
  one-wall rounding, is essential.
- **Edge rounding after exact band recovery is complete.**  On any band on
  which the two endpoint `SL_3(Z)` actions are genuine representations,
  `kazhdan-polar-rounding-produces-supported-gallery-edges` turns the raw
  almost intertwiner into an exact partial intertwiner.  Its source/target
  trace loss is at most `(eta/kappa)^2` and its HS displacement is at most
  `2 eta/kappa`, uniformly in dimension and multiplicity.  Thus property
  `(T)` solves the analytic edge-rounding step, but cannot be invoked before
  compatible genuine band representations have been extracted.
- **One selected corner is not easier to correct.**  Canonical mixed trace
  tests make every positive native four-atom/parahoric corner carry the
  regular lattice trace.  Moreover a correction theorem using only one
  approximately reducing selector would imply full regular-microstate
  correction for `SL_3(Z)` by tensoring an arbitrary microstate with one
  external bit; see
  `selected-corner-correction-contains-regular-correction`.
  The needed theorem must therefore correct the six corners and their
  transitions jointly, rather than exactifying them independently.
- **Even a flat six-corner corrector can keep overlap `1/4`.**  Reduction of
  the `A_2` coweight lattice modulo two gives a nonconstant affine corrector
  satisfying every inverse, Weyl, triangle, and closed-hexagon equation with
  zero holonomy; its finite lamp model retains independent half projections.
  See `coxeter-hexagon-admits-flat-affine-corrector`.  Thus the open decoder
  must use a mixed root outside each directional parahoric and charge the
  affine tail `(FAC10)` to conductor exit.  Raw or corrector hexagon closure
  alone is insufficient.
- **The actual parahoric atlas kills every abelian flat gauge.**  The toy
  affine escape uses substitute vector stabilizers.  On the true `42`-point
  atlas, the `C`-orbit of the signed triangle relation is an integral
  unimodular basis; hence every covariant commuting corrector collapses with
  a dimension-independent HS modulus.  See
  `actual-parahoric-triangle-kills-abelian-correctors`.  The remaining mixed
  tail is therefore genuinely nonabelian, not another conductor torus.
- **Periodic conductor plateaux pay a constant seam.**  A truncated dyadic
  shift makes every fixed root-depth test have squared defect `O(C_N/L)`,
  but independent root clocks fail the first adjacent-root Steinberg
  triangle with squared defect exactly `2`.  Replacing each chamber by an
  exact finite Chevalley packet merely moves this constant failure to the
  literal shared-root identities between adjacent chambers.  On arbitrary
  block-diagonal mixtures, target overlap `1/4` forces some one of the six
  wall defects to have square at least `1/3`; see
  `periodic-conductor-plateaux-pay-a-shared-root-seam`.  Thus the open enemy
  is non-block-diagonal rectangular multiplicity transport, not a long flat
  conductor band.
- **There is no residual nonabelian common-carrier gauge.**  If one supported
  corrector `Z` is invariant under the native parahoric and satisfies the
  ordered Weyl triangle, translating that triangle by `x_32(1)` and
  `x_21(1)` and cancelling its fixed factors shows that `Z` is also invariant
  under `x_23(1)` and `x_12(1)`.  These roots generate the whole actor, and
  the triangle then gives `Z=Z^2`.  The same calculation yields the
  dimension-free estimate `||Z-I||_2<=9 epsilon_tri+10 epsilon_D`; see
  `native-parahoric-triangle-kills-all-corrector-gauges`.  Thus the current
  hole is solely the common-carrier/rectangular-leakage extraction, not
  corrector holonomy after extraction.
- **Partial cancellation itself loses only first-exit mass.**  Left or right
  cancellation through a partial isometry is isometric on its actual source
  or range.  On a larger carrier `R`, the squared uncontrolled error is at
  most four times the trace of the missing source/range projection.  Applying
  this to the two translated native triangles gives a supported estimate
  `||R(Z-I)||_2^2 <= C edgeEnergy+C sum(firstExitMass)` with a fixed constant;
  see `partial-isometry-translate-cancel-charges-first-exit`.  Therefore the
  analytic cancellation endpoint no longer requires globally unitary
  correctors.  The open step is solely to extract the supported factors and
  route their actual support loss into the conductor recurrence.
- **Raw words canonically supply the partial transitions once bands exist.**
  For equal-trace band projections `P,Q`, polar-decompose `QUP`, where `U`
  is the raw actor word.  Its source loss, range loss, and squared polar
  displacement are all bounded by the single leakage
  `||(1-Q)UP||_2^2`.  Products of these polar transitions differ from the
  raw gallery word by at most the sum of square roots of the edge leakages;
  see `polar-compression-turns-band-mismatch-into-first-exit`.  Hence neither
  property-(T) exactification nor a separate common-gauge rounding theorem is
  needed after equal-trace conductor projections have been found.  The sole
  analytic gate is now constructing those projections and assigning their
  cross-band leakage to the depth recurrence.
- **A finite rectangular leakage ledger cannot itself contract.**  Every
  fixed family of coweight shifts admits exact finite-rank Schur atlases
  built from triangular Folner multiplicity profiles.  All chamber carriers
  have equal trace, all partial intertwiners are coherent, and their total
  first-exit mass is `O_F(1/N)`, while tensoring an independent four-atom
  lamp leaves positive interior overlap on asymptotically the whole common
  carrier.  See
  `folner-multiplicity-atlases-have-vanishing-first-exit`.
  Therefore the fixed `kappa` in `(AHD2)` cannot come from rank balancing,
  Schur matching, or conductor descent alone.  The actual mixed-root packet
  must make the marked scale graph non-Folner (or furnish an equivalent
  same-reservoir multiplicity payment).
- **The full affine-Weyl apartment plus the native triangle still does not
  authenticate support.**  The six Weyl-conjugate denominator translations
  generate `Q^vee semidirect S_3`, hence a virtually `Z^2` action.  Exact
  finite torus models have one `S_3`-invariant trace-`1/42` hexagonal cutoff
  with total six-shift covariance energy `O(1/M)`.  Tensoring this cutoff
  with the trivial forty-two-chart corrector makes every native translated
  parahoric triangle exact.  Thus the triangle kills every gauge once it is
  supported on the decoded carrier, but cannot identify that carrier; see
  `affine-weyl-folner-cut-survives-native-parahoric-triangle`.  The remaining
  input in `(AHD1)` is exactly raw denominator-section source/range
  authentication, after which the established partial-isometry cancellation
  charges only first-exit mass.
- **The first literal root-parahoric edge is still rectangular.**  For
  `u=x_12(1)`, the relation `huh^(-1)=u^2` acts on the actual forty-two-point
  shell with a base two-cycle and a native four-cycle.  The `u`-flip on the
  two-cycle is exactly intertwined with the `u^2`-flip on one parity pair of
  the four-cycle.  Hence the compressed relation has an exact rank-two
  Morita lift with different source and range; see
  `first-root-parahoric-incidence-has-a-two-to-four-morita-lift`.  It would
  pay the fixed gap `2/21` only after a second raw path identified those two
  carriers.  The remaining incidence must therefore be a same-atom return,
  not another one-way root-scaling edge.
- **No integral root/Weyl word supplies that return.**  Ordered pairs of
  `D`-cosets retain their `D backslash C/D` orbital type under every diagonal
  `C`-word.  The preceding source pair has type `D x_12(1)D`, while its
  rectangular target has type `D x_13(2)D`; modulo two the latter lies in
  `Dbar` and the former in the disjoint cell
  `Dbar x_12(1) Dbar`.  The shortest A2 commutator path is
  `[x_12(1),x_23(2)]=x_13(2)`, but its two section words differ by
  `x_23(2) in D`.  Their endpoint projections agree, while their internal
  relative holonomy is the canonically trace-zero corner unitary
  `P x_23(2)P`.  The two-path Gram identity would charge normalized leakage
  `1/2` if a raw unitary compression were forced to equal their average;
  the section word alone does not impose that linear incidence.  See
  `first-root-parahoric-target-has-a-distinct-double-coset-type`.  The next
  incidence must either authenticate this two-path average on the same
  corner or contain a second denominator/cross-chart type change; no bounded
  collection of diagonal integral root triangles returns the target pair.
- **The native row does not already authenticate the two-path average.**
  Its trace-zero holonomy would give normalized source leakage `1/2` for the
  contraction `K=(A+B)/2`.  But after multiplying by one path, realizing
  `K` as the compression of a group word would require
  `P g P=(P+dP)/2`.  The left side has support in one lamp double coset
  `<c>g<c>`, while the right side has nonzero coefficients in the two
  distinct cosets `<c>` and `d<c>`.  See
  `native-a2-two-path-average-is-not-an-ordinary-word-compression`.  Thus the
  exact surviving scalar is known, but exposing it requires a noncentral
  additive two-path wordization plus control of the complementary Julia
  leakage; another monomial arithmetic section word cannot do it.
- **The shortest second-denominator return closes only the type.**  After
  changing `x_13(2)` back to the `12` root coordinate, exactly two of the six
  denominator directions rescale it to `x_12(1)`: the literal backtrack
  `h^(-1)` and `h_(s_12)=diag(1,2,1/2)`.  Their relative returned holonomy is
  the ordinary arithmetic word
  `diag(2,2,1/4)`, which centralizes `x_12` but translates the conductor
  carrier by coweight `(1,1,-2)`.  See
  `shortest-second-denominator-return-has-coweight-holonomy`.  Every fixed
  such translation has squared cutoff leakage `O(1/M)` on the joint
  affine-Weyl Folner model.  Thus this loop identifies the root packet type,
  not the raw atom; its product word remains inside the amenable conductor
  action and gives no fixed payment.
- **Amenable holonomy classifies root-type loops, not parahoric returns.**
  Any loop returning one exact root subgroup has relative word in its
  normalizer.  For `x_12(*)`, that normalizer preserves the image line and
  kernel plane of `E_12`, hence lies in a solvable Borel and is amenable.
  But the weaker parahoric statement is false already for the shortest A2
  section loop: its holonomy `x_23(2) in D` does not normalize `x_12(*)`, and
  `D` is finite-index nonamenable in `SL_3(Z)`.  See
  `root-type-loops-are-solvable-but-parahoric-loops-are-not`.  This does not
  close the decoder: the base projection commutes with `D`, so the
  nonamenable holonomy is an internal corner unitary until two paths are
  forced to interfere on the identical carrier.
- **The smallest internal finite-Hecke wordization fails three times.**
  Take `c=diag(-1,-1,1) in D` and `q=(1+c)/2`.  Although `c` inverts the
  desired holonomy `d=x_23(2)`, every literal `qgq` has either four distinct
  support words or two whose relative word is a finite involution, never the
  two A2 paths with infinite relative word `d`.  Its trace is `1/2`, not
  `1/42`, and the exact section-covariance floor is
  `||dqd^(-1)-q||_2^2=1/2`.  See
  `native-c2-hecke-corner-cannot-wordize-the-a2-average`.  Thus the first
  finite character idempotent cannot expose the trace-zero holonomy without
  abandoning the raw section interface.
- **Trace alone closes every finite arithmetic Hecke source.**  For any
  finite `K<D` and projection `q in C[K]`, canonical trace is
  `rank(lambda_K(q))/|K|`.  Since every finite subgroup of
  `SL_3(Z[1/2])` has order at most `24`, it can never equal `1/42`; see
  `no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace`.  Thus no
  finite character idempotent can simultaneously rank-match the shell,
  preserve the section covariance, and wordize the `x_23(2)` two-path
  holonomy.  The first surviving source is necessarily an unbounded-depth
  Borel/matrix-coordinate projection, noncentral relative to a second chart;
  this exact remaining target is
  `unbounded-noncentral-hecke-corner-wordizes-a2-average`.
- **Moving finite Borel packets centralize or pay exactly `1/84`.**  In the
  level-`2^n` image `F_n` of `D`, a projection in `C[F_n]` retaining every
  `D` section correction lies in `Z(C[F_n])`; property `(T)` makes the same
  statement uniform for approximate covariance.  Even granting trace
  `1/42`, the A2 average has global Julia leakage
  `tau(q)(1-Re tau_q(x_23(2)))/2`.  Retaining canonical trace-zero holonomy
  makes this tend to `1/84`, while making it vanish forces the holonomy to
  become the identity on the packet.  See
  `parahoric-covariant-congruence-packets-pay-one-over-eighty-four`.
  Hence the remaining unbounded source cannot lie in a moving left
  congruence/Borel group algebra; it must occupy a larger relative
  commutant and couple noncentrally to another chart.
- **Full-conductor adjoint regularity does not repair that failure.**  This
  follows by an exact tensor test, not an asymptotic heuristic.  Let
  `(K_N,(R_g),(V_(h,g)))` be any of the rectangular atlases from
  `folner-multiplicity-atlases-have-vanishing-first-exit`, and fix

  ```text
  Q_a=SL_3(Z/2^a Z),   L_a=M_(|Q_a|)(C)
  ```

  with the normalized Hilbert--Schmidt structure.  Tensor the entire atlas
  with `L_a`, letting `Ad(lambda_(Q_a))` act on the second factor and putting

  ```text
  Rtilde_g=R_g tensor 1,       Vtilde_(h,g)=V_(h,g) tensor 1. (AHD4)
  ```

  Normalized carrier traces, all intersection traces, and every first-exit
  mass in `(FSM2)` are unchanged by `(AHD4)`.  The adjoint action commutes
  exactly with every first-factor carrier and transition.  Nevertheless
  `finite-regular-adjoint-retains-full-conductor` gives

  ```text
  Ad(lambda_(Q_a)) ~= |Q_a| lambda_(Q_a),                     (AHD5)
  ```

  so the second factor is faithful and retains every depth of the dyadic
  conductor.  Tensoring also with the independent four-atom lamp leaves its
  interior overlap fixed while the conductor first exits are `O_F(1/N)`.

  Hence there is no dimension- and depth-independent inequality

  ```text
  kappa * markedMass
    <= C (conductorFirstExit + adjointConductorDefect)         (AHD6)
  ```

  based only on exact full-conductor adjoint blocks, coherent rectangular
  transitions, and depth shifts: in this tensor test the adjoint defect is
  zero, the first-exit term tends to zero, and the marked mass does not.
  This pushes the residual after `(PRT5)--(PRT7)` to one precise place.
  Any proof of the required cross-overlap estimate `(FGP6)` must make the
  **mixed-root words couple the conductor representation factor to the
  multiplicity reservoir**.  Merely knowing that the adjoint lift retains
  the full conductor supplies no such coupling.  Scope: the tensor test is
  not a representation of the full arithmetic packet, so it does not refute
  `(AHD2)`; it proves that the missing mixed-root/same-reservoir term is
  logically indispensable and cannot be replaced by adjoint conductor
  exactness.
- **Pure Steinberg mixed-root words still do not couple the reservoir
  (exact Gram countertest).**  The first adjacent-root word one would try is

  ```text
  [x_12(a),x_23(b)] x_13(-ab)=1.                            (AHD7)
  ```

  It cannot control the cross-overlap scalar in `(FGP6)`.  Indeed, for
  arbitrary finite-dimensional spaces `V_1,V_2,V_3` and rectangular maps
  `a:V_2->V_1`, `b:V_3->V_2`, block multiplication gives

  ```text
  [1+aE_12,1+bE_23]=1+(ab)E_13,                            (AHD8)
  ```

  with no equality among `dim V_1,dim V_2,dim V_3`.  By associativity the
  same is true for every finite pasting of Steinberg triangles, distant-root
  commutations, and their Hall--Witt reassociations; this is the finite
  Morita model of
  `mixed-steinberg-loops-admit-morita-rectangular-model`.

  Here is a literal countertest to deriving `(FGP6)` from that word language.
  Take the left regular unitary representation of the finite block group in
  the Morita model, tensor it with `K=C^4`, and let all root words act on the
  first factor.  On `K`, let `p_1=p_2` be the rank-one projection onto the
  first coordinate and let the other forty candidate branch projections be
  zero.  Put `P_i=1 tensor p_i`.  Then

  ```text
  sum_i rank(P_i) <= dim(H),
  Omega=sum_(i!=j) tr(P_iP_j)=1/2,                         (AHD9)
  ```

  whereas every word in the pure mixed-Steinberg language has zero defect.
  Taking the carrier to be the whole space and its transitions to be the
  identity also makes the abstract first-exit term zero.  Thus no inequality

  ```text
  Omega <= C (pureSteinbergEnergy + firstExitMass)
  ```

  is valid, even with dimension-dependent `C`, unless the branch projections
  are tied to the root representation by an additional relation.

  This proves the next sharp reduction after `(AHD6)`: a successful mixed
  word must contain a **same-object return after a net refinement**.  In the
  Morita test it must compare `1_E` with `1_(E direct_sum E)`, or,
  equivalently in the native gallery, identify an externally transported
  branch selector with the identical internal root reservoir.  More
  multiplication triangles cannot do this because they preserve source and
  target sorts.  Scope: the free commutant projections in this countertest
  are precisely the datum the full arithmetic packet still has to forbid;
  hence this is not a countermodel to `(AHD2)`, but it rules out the entire
  pure-Steinberg route to the required conductor-to-multiplicity
  synchronization inequality.
- **A denominator-conjugated Steinberg word is still gauge-covariant.**  At
  `p=3`, the literal relation

  ```text
  [h x_12(1)h^(-1),x_23(1)]=x_13(3)
  ```

  looks stronger because it crosses adjacent conductor charts.  On an
  oscillator isotypic block, however, `rho(h)=W_h tensor V` and every root
  is `pi(x) tensor I`; the `V,V^*` cancel inside the conjugated root.  The
  relation is exactly the oscillator Chevalley identity tensored with the
  multiplicity identity.  A two-dimensional swap can move a half projection
  by squared HS distance one while the word defect remains zero; the full
  inverse twisted-regular groupoid gauge extends this to every finite native
  transition table.  See
  `p3-denominator-steinberg-word-is-multiplicity-blind`.  Thus inserting raw
  denominator conjugations into pure Steinberg triangles still does not
  create the same-object return isolated after `(AHD9)`.
- **Bounded conductor width does pay uniformly.**  The converse estimate
  `bounded-conductor-width-pays-uniform-first-exit` shows that a multiplicity
  profile supported on at most `B` root-depth bands loses at least `1/B`
  under one unit conductor shift.  Hence the rectangular escape above is
  possible only through genuinely unbounded scale spread, and its `O(1/N)`
  triangular construction is sharp up to constants.  After a common atlas
  has been decoded, every bounded-width portion already has the required
  positive first-exit payment; only the scale-spread tail remains.
- **The non-Folner endpoint is already available once one global PVM is
  decoded.**  The full coset/building orbit `A/C` has a fixed bottom gap
  (equivalently, use the property-`(T)` Hecke contraction), and
  `infinite-schreier-pvm-transport-kills-finite-mark` turns covariance of one
  finite-support PVM over that orbit into
  `markedMass <= C HeckeCovarianceEnergy`, uniformly in matrix dimension.
  The native expanding double coset has exactly `42` branches by
  `expanding-double-coset-degree-is-p-times-flags`.  Thus the target should
  no longer be phrased as contraction of six arbitrary band projections:
  it is to show that the six root packets are restrictions of one
  same-basis PVM for the `42`-branch building shell, with its covariance
  energy bounded by word defect plus the already-defined first exits.  Once
  that dictionary is proved, the established Schreier PVM inequality
  supplies the missing fixed `kappa`.
- **Common-PVM rounding is one scalar Gram estimate.**  Given the `42`
  labelled candidate branch projections with total rank at most the ambient
  dimension, `forty-two-branch-gram-polar-rounding` simultaneously
  orthogonalizes them by polar decomposition of their block-column synthesis
  map.  The total squared movement is at most four times
  `Omega=sum_(i!=j)tr(P_iP_j)`, and the rounded PVM covariance energy is at
  most `3 E_raw+24 Omega`.  Thus no further same-basis rounding theorem is
  needed after proving `Omega<=C(mixedRootEnergy+firstExitMass)`.  This
  cross-overlap inequality is now the exact algebraic content of the common
  `42`-branch extraction; bounded local jointness alone cannot supply it.
- **Current unresolved step.**  Prove that separately rounded growing-period
  root packets either share enough multiplicity space for `(HEL11)` or that
  their mismatch is first-exit mass controlled by the two-level conductor
  join; in the sharp formulation above, assemble those shared pieces into
  one finite-support PVM for the native `42`-branch building shell.  The
  descent itself is not a contraction for arbitrary isotypic
  weights (`weyl-kernel-joins-descend-two-levels-without-mass-contraction`),
  so the fixed `kappa` in `(AHD2)` must come from a matrix-only same-reservoir
  return or multiplicity payment, not from property `(T)` alone.  No
  dimension-independent proof of this extraction is currently in hand.
- **Closing the literal root gallery saturates the actor.**  Once both simple
  roots and their opposites are identified in one genuine `A_2` reservoir,
  adjoining `h=diag(2,1,1/2)` generates every elementary root over
  `Z[1/2]`, hence all of `SL_3(Z[1/2])`; see
  `closed-a2-dyadic-packet-saturates-the-sl3-actor`.  Exact odd-congruence
  models calibrate all of these actor relations, while the native triangle
  already supplies the dimension-free common-carrier inequality `(NPC15)`.
  Therefore there is no intermediate closed-gallery relation packet left to
  add.  The unresolved content is exactly the matrix-only support statement
  that the rectangular chamber pieces belong to one carrier; without it the
  regular-HNN/Bernoulli lamp remains a firewall.
- **The canonical Jones carrier authenticates fixed depth but its atom
  vanishes with depth.**  Intersecting all six depth-`N` Weyl parahorics
  forces every off-diagonal entry to be divisible by `2^(2N)`.  The Jones
  projection onto this common subgroup therefore has trace at most
  `2^(-2N)`; see
  `closed-weyl-iwahori-jones-carrier-has-vanishing-depth-mass`.  Its coset
  conjugates do give an exact common PVM at every fixed depth, so the basic
  construction correctly identifies the desired support object.  But no
  single positive-mass spectral atom survives all depths.  Restoring total
  mass requires the entire coset PVM, returning exactly to the open
  coordinatewise covariance/Gram estimate rather than bypassing it with one
  Iwahori projection.
- **Six simultaneous Hecke gaps still do not control the Gram scalar.**  Put
  the six shell PVMs on the six independent coordinates of `Omega^6` and
  let `C` act diagonally.  Every chart covariance and every lattice/root
  relation is exact, but each of the five star deficits is `41/42`, for
  total mismatch `205/42`; see
  `six-shell-hecke-gap-is-blind-to-cross-chart-gram-energy`.  Tensoring with
  deep regular congruence representations makes the lattice character
  canonical without changing the mismatch.  Thus property `(T)` only mixes
  within diagonal-action orbitals and cannot select the diagonal matching
  orbital.  The sole remaining scalar input is the raw denominator
  incidence `(RDI11)`, transferred from raw lamp conjugates to decoded joint
  atoms with first-exit control.
- **Equal-rank first exits perform the raw-to-decoded transfer directly.**
  For decoded atoms `E_i,F_i` of equal trace and the actual section
  transition `T_i=rho(b_i)^*rho(a_i)`, one has the exact identity
  `||T_iE_iT_i^*-F_i||_2^2=2||(1-F_i)T_iE_i||_2^2`.
  Comparing `T_i` with the section correction `rho(d_i)` gives the
  dimension-free star-link estimate `(EDA13)` in
  `equal-rank-denominator-edges-authenticate-decoded-atoms`.  Thus the
  impossible pointwise decoded-to-raw comparison is unnecessary.  The sole
  remaining construction problem is now sharper: produce equal-rank joint
  atoms whose section leakage is the existing first-exit mass and whose
  `d_i`-relabeling is paid by the decoded full-PVM lattice covariance.
- **A finite spanning-tree core makes all decoded atom ranks coherent.**
  On the `6*42` chart-label vertices, take `41` lattice-label edges in one
  root chart and all `5*42` denominator star edges.  Two-sided leakage first
  balances ranks; intersecting the pulled-back polar source projections and
  propagating that intersection produces equal-rank subatoms in every chart
  while losing at most a fixed multiple of the total two edge energies; see
  `finite-tree-first-exits-extract-an-equal-rank-global-pvm`.  Non-tree
  lattice covariance remains controlled after trimming.  Therefore neither
  rank balancing nor common-source synchronization is still open.  The sole
  preceding input is construction of the six separate decoded chart PVMs
  with their root-chart covariance and denominator first exits controlled.
- **Exact one-hot decoding and exact raw incidence still tensor-separate.**
  `raw-incidence-and-one-hot-pvms-tensor-separate` puts an exact balanced
  Bernoulli raw branch family and two exact one-hot/Fourier chart PVMs on
  three finite coordinates. The same transitive actor covaries all three systems, every
  section identity `a_i=b_i d_i` and raw deficit is exact, and both decoded
  charts have equal atom ranks. Yet their saturation deficit is `41/42`.
  The first quantity which sees the separation is precisely

  ```text
  sum_i ||(1-Q_i)T_iP_i||_2^2=41/42,
  ```

  the atomwise mixed section leakage `(EDA11)`. Therefore separate
  one-hot/Fourier construction plus the raw denominator lemma cannot produce
  one shell PVM. The smallest remaining Gram input is irreducibly mixed:
  prove that the actual section transition applied to each decoded root atom
  has leakage controlled by the conductor/root ledger. No marginal or raw
  factor estimate can substitute for it.
- **Carrier-level first exit still does not pay atomwise section exit.**
  `independent-chart-refinement-forces-eda-leakage` starts with any
  equal-trace conductor edge `(R,S,V)` of mass `mu` and base first exit
  `L=||(1-S)VR||_2^2`. Refining its endpoints by two independent `q`-atom
  coordinate PVMs gives equal-rank decoded atoms with the exact identity

  ```text
  sum_i ||(1-F_i)(V tensor 1)E_i||_2^2
   =mu(1-1/q)+L/q.
  ```

  At `q=42`, even a perfect carrier edge has atomwise EDA leakage
  `41mu/42`. Tensoring preserves every old conductor/root defect and raw
  incidence scalar. Thus the surviving target cannot be an inequality
  deriving `(EDA11)` from the carrier-level ledger: the independent-label
  tensor packet refutes it sharply. The six chart PVMs must instead be
  constructed inside a section-functorial label algebra so their atomwise
  leakages are literal summands of the decoder's ledger. This is a new
  structural input, not a constants problem.
- **One injective chart phase is the smallest sufficient mixed Gram row.**
  `one-phase-chart-tag-pays-atomwise-leakage` assigns the `42` decoded atoms
  the distinct phases `zeta^i` and forms partial tags `A=sum zeta^iE_i`,
  `B=sum zeta^iF_i`. If `T` is the actual denominator section, carrier exit
  is `L`, and `K=||BTR-TA||_2^2`, then

  ```text
  sum_i||(1-F_i)TE_i||_2^2
   <=L+(K-L)/(4 sin^2(pi/42)).
  ```

  This follows from an exact block decomposition, not rounding, and feeds
  directly into `(EDA13)`. Hence the frontier is now one explicit mixed-root
  construction: wordize or otherwise control a section-covariant injective
  phase tag built from each chart's one-hot/Fourier atoms. The independent
  refinement countermodel proves that no collection of marginal phase or
  carrier energies can replace this cross-section covariance row.
- **The injective tag cannot be an actor group-algebra word.** On the
  transitive `42`-point module, every linear combination of lattice actor,
  root, Weyl, and section-correction words preserves the constant line.
  The diagonal tag using all `42`nd roots sends that line orthogonally away
  from itself. `actor-algebra-cannot-wordize-shell-phase-tag` computes

  ```text
  inf_(X in actor algebra)||sum_i zeta^iP_i-X||_2^2>=2/42=1/21.
  ```

  Thus increasing the degree of a fixed actor polynomial cannot supply the
  phase covariance row above. Any successful wordization must use actual
  lamp/selector coefficients, an enlarged off-shell crossed-product
  window, or conductor-dependent nonlinear spectral cuts. The native shell
  lamps do not give the first option by Boolean Fourier expansion because
  they retain exact graph-product nonedges. Hence the fixed-shell
  actor-only phase-tag route is closed, not merely quantitatively weak.
- **The minimal off-shell return still defeats every fixed window.**
  `finite-shell-window-cannot-wordize-returning-tag` first extends the
  constant-line estimate to any finite union of lattice shell orbits: an
  injective diagonal tag has squared distance at least
  `(2/Q)sum_r(1-|meanPhase_r|^2)` from the actor algebra. Granting the full
  diagonal coefficient algebra only moves the obstruction to the shortest
  second-denominator return. Its holonomy

  ```text
  k=diag(2,2,1/4)
  ```

  has no finite orbit on `SL_3(Z[1/2])/SL_3(Z)`. Every nonempty fixed window
  `F` therefore satisfies

  ```text
  ||kA_Fk^(-1)-A_F||_2^2>=1/|F|.
  ```

  This positive term is not presentation defect because `k` is a genuine
  coweight word, not a relator. Hence the two-cycle/four-cycle Morita edge,
  shortest A2 path, and one alternative denominator return cannot produce a
  fixed finite-window covariant phase tag. Only growing affine-Weyl Folner
  windows evade the bound; a closing incidence must make that off-shell
  direction nonamenable rather than enlarge the window by a fixed amount.
- **A global Schreier PVM is stronger than action soficity and would already
  close the route.** `global-schreier-pvm-is-stronger-than-action-soficity`
  formalizes the exact output needed from the HNN microstates. If finite-
  support orthogonal atoms over `A/C` have total mass `mu`, their transport
  energy is at least `2 gamma mu` by the existing Schreier gap. This is a
  window-independent normalized-HS inequality. But soficity supplies only
  local orbit charts, not a global label map into `A/C`; nonamenable regular
  actions of sofic groups show the distinction is strict.

  The exact Bernoulli crossed product is the firewall. Its raw lamp
  projections are perfectly covariant but have pair overlap `1/4`, and any
  exactly covariant orthogonal `A/C`-PVM of positive invariant mass would
  push trace forward to an invariant probability on `A/C`, impossible by
  non-coamenability. Thus no further Poincare estimate is missing. The live
  arithmetic theorem is a genuinely nonlinear Cartan/PVM extraction from
  overlapping raw lamps; proving or disproving soficity of the arithmetic
  set action does not substitute for it.
