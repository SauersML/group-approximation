---
rg: 2
id: skeleton-relative-hs-stability-for-sl2
kind: claim
title: SL2(Z[1/2]) is HS-stable relative to its two exact parabolic skeletons
distinct_from:
  approximate-doubling-invariant-joint-measure-is-atomic: that is the target common-odd-model statement; this is the residual gluing problem after Levit--Vigdorovich exactifies both parabolic BS(1,4) skeletons, and it is strictly smaller than raw stability because the remaining freedom lives in compact centralizer torsors of exact finite-order data.
  iwahori-outlier-repair: that is the far-sector endpoint in square-root form; this isolates the one new stability ingredient the skeleton synthesis needs, with the alignment steps and the odd-collapse endgame already supplied by finite arguments and established nodes.
  odd-congruence-vertex-sector-admits-no-exact-leak: that consumes a common odd model to kill the leak by co-density; this produces the common odd model from the skeletons.
---

Let `pi` be an asymptotic finite-dimensional representation of
`SL_2(Z[1/2])`.  By Levit--Vigdorovich (arXiv:2206.02268, Cor D(3);
`BS(1,4)` is HS-stable), each parabolic skeleton
`(pi(u), pi(h))` and `(pi(l), pi(h))` is HS-close to an EXACT
`BS(1,4)` pair whose base unitary has finite ODD order.  CLAIM: the
two exact skeletons can be corrected further, with dimension-free
loss, so that ALL of the following hold exactly on a common model:
a single `h`-component shared by both skeletons; an intertwiner
implementing the Weyl swap; and the Weyl element expressed as its
defining word in the two parabolics.  Equivalently: `SL_2(Z[1/2])` is
HS-stable RELATIVE to exact skeleton data.

Why this is strictly smaller than raw HS-stability: after the two
skeletons are exact, the remaining freedom is (i) the relative
position of two exact finite-odd-order structures — spectra align by
Hoffman--Wielandt, a finite problem — and (ii) gluing corrections
ranging over the CENTRALIZER TORSORS of the exact skeletons, which
are compact groups; the obstruction theory is an alignment/cohomology
problem over compact torsors rather than a stability problem over all
of `U(d)`.

Consequence chain if established:
`skeletons exact (LV) + this claim` gives the common finite ODD model
of `approximate-doubling-invariant-joint-measure-is-atomic`; on an
odd model conjugation by `diag(2, 1/2)` is INNER, co-density applies,
and the leak collapses by the mechanism of
`odd-congruence-vertex-sector-admits-no-exact-leak` — the far sector
closes, `iwahori-outlier-repair` resolves, and the goal follows
through the Iwahori route.  The two-adic content that obstructs
everything elsewhere is absent here by construction: the
Levit--Vigdorovich skeletons are odd, and multiplication by four is
an automorphism on odd spectra, so the conductor-box escape mechanism
never activates.

## Attempts

- **The torsor reduction is the designed attack.**  Fix the exact
  `u`-skeleton `(V_0, W_0)`.  The second skeleton's `h`-part `W_0'`
  satisfies `||W_0' - W_0|| = o(1)`; correcting `W_0'` to `W_0`
  within exact `BS(1,4)`-pairs is a RELATIVE stability question for
  `BS(1,4)` over its `<h>`-subgroup — plausibly accessible by the
  same dense-periodic-measure technique, conditioning the Marcus
  argument on the `h`-component.  Then the Weyl word
  `s = e_12(1) e_21(-1) e_12(1)` is DETERMINED by the exact data, and
  the final consistency (that the determined `s` approximately
  implements the swap it must) is a closed condition on the compact
  torsor of gluings — a fixed-point/averaging problem on a compact
  group, where dimension-free tools (Gowers--Hatami on the finite odd
  model's image, the (tau) squeeze) are available.
- **Proof-plan and its precise load-bearing step (2026-08-21, same
  day).**  The natural plan: (1) extend Levit--Vigdorovich from
  `BS(1,4)` to the full solenoid group `Q = Z[1/2] rtimes_4 Z`
  (their own mechanism should carry: characters of `Q` are
  `x4`-invariant measures on the compact solenoid, where hyperbolic
  specification makes periodic measures dense — Sigmund, as the far-
  sector node already records); (2) align the exact structures; (3)
  finite Steinberg rank-one bookkeeping: with both towers exact and
  the Weyl word determined, the presentation of `SL_2(Z[1/2])` closes
  and the tuple is an exact representation.  Steps (1) and (3) are
  standard-shaped.  The load-bearing step is (2), and the naive
  argument FAILS precisely here: Folner averaging aligns two close
  exact representations only with loss (generator closeness) x
  (Folner diameter), and `Q` has exponential growth, so
  small-boundary Folner sets have huge diameter.  What (2) actually
  needs is LOCAL HS-RIGIDITY of the exact representation spaces of
  `BS(1,4)`/`Q`: two exact finite-dimensional representations that
  are HS-close on generators are conjugate by a small unitary.  This
  is a strengthening of stability (stability = approximate implies
  near SOME exact; local rigidity = the exact variety has no
  HS-nearby disconnected sheets), plausibly attackable by the same
  periodic-measure technology since close representations have close
  weights on periodic characters.  If local rigidity fails, the
  gluing may genuinely branch, and the route dies here — a clean,
  falsifiable crux.
- **Second correction: step (3) is not bookkeeping (2026-08-21,
  same day).**  Rank-one Steinberg presentations have NO commutator
  formula between opposite root groups; the `w(u)`-conjugation
  relations for a generating set of units are INDEPENDENT axioms.
  For `Z[1/2]` the units are generated by `2` (and `-1`), so the
  aligned tuple must satisfy TWO swap constraints — the `w(1)`-swap
  and the `w(2)`-swap — and the second is not implied by the first
  plus the towers.  The gluing crux is therefore the SIMULTANEOUS
  small-conjugacy of the two exact odd towers under both Weyl words
  at once; their ratio `w(2) w(1)^{-1} = h` is exactly the Iwahori
  square-root object, so this route lands on the classical hard core
  in new coordinates: two exact odd solenoid towers, two swap
  alignments over compact centralizer torsors, all two-adic escape
  disabled.  The coordinates are sharper than any prior form of the
  far sector (local HS-rigidity of the solenoid variety plus a
  two-swap simultaneous alignment, both clean compact-space
  questions), but the difficulty is conserved, as it must be.
- **Leg (1) closed; the tower exactifies top-down (2026-08-21).**
  `bs14-exact-representation-variety-is-hs-locally-rigid` is
  established, and with it the solenoid tower needs NO new stability
  theorem: exactify the DEEPEST level required by the relator family
  via Levit--Vigdorovich, then define the whole tower downward by
  fourth powers of that single exact pair — an exact solenoid
  representation sharing one `h`, with errors amplified by `4^depth`
  but depth is fixed per relator, which is all an asymptotic
  representation owes.  So per-relator solenoid exactification holds
  with fixed-depth constants, full uniform `Q`-stability is not
  needed, and BOTH parabolic towers exactify with shared internal
  `h`-components.  The claim's entire remaining content is the
  TWO-SWAP SIMULTANEOUS ALIGNMENT: correct the relative position of
  the two exact odd towers so that the `w(1)`- and `w(2)`-Weyl words
  act exactly at once — the Iwahori square-root core in exact-odd
  coordinates, now provably the LAST piece of this route.
- **Leg (2) attack: the swap-transport reduction (2026-08-21).**
  Two failed shapes first: Gowers--Hatami on the finite model
  `SL_2(Z/N)` via bounded Bruhat width (stable rank one gives width
  `<= 5` over the two full abelian subgroups) FAILS because the swap
  defect at residues `x ~ N` amplifies linearly (`||A^x - B^x|| <= x
  delta_1` with `N_m delta_1(m)` uncontrolled); and exact-conjugacy
  of the transported tower fails generically because the discrete
  invariant multisets differ by small transports.  The living move:
  DEFINE the lower tower BY the swap, `L(y) := s pi-upper(-y) s^{-1}`
  — then the lower tower is exact and the `w(1)`-swap relation holds
  EXACTLY by construction, at the price of moving all defect into
  two UNAMPLIFIED fixed-word residuals: the transported tower's
  `h`-relation (`s^{-1} W s` versus `W^{-1}` times the exact torus,
  Weyl inversion) and the `w(2)`-relation.  The obstruction to
  correcting both at once over the compact centralizer torsors is a
  cohomological cycle over the relation triangle {upper-`h`, swap,
  torus inversion}: its class vanishes on every exact finite model,
  and the claim is exactly that the microstate's approximate class
  converges to the vanishing one — an `H^2`-comparison over exact
  structures, uniform in odd `N`, with Selberg/(tau) the expected
  control.  Compared to every previous form of the far sector: all
  towers exact, one swap exact, NO amplified defects anywhere, and
  the whole problem is two fixed words on compact torsors.
- **The torus-inversion residual is a twisted-coboundary equation
  with a spread/degenerate dichotomy (2026-08-21).**  Write
  `e := W s^{-1} W s` for the `(R1)` defect; chasing the exact
  square (upper tower, swap, transported tower) shows `e`
  almost-commutes with the exact upper tower, so after a clustering
  squeeze `e` lies in the tower's commutant, and correcting
  `s -> s c` with `c` in the compact torsor `U(commutant)` turns
  `(R1)` into the twisted-coboundary equation `psi(c) c^{-1} = e`,
  where `psi` composes the solenoid shift with the swap transport.
  Along each shift-cycle of commutant blocks the equation propagates
  freely and closes iff a single holonomy `H(e)` lies in the twisted
  commutator set `{M_0 g M_0^{-1} g^{-1}}` of the cycle's exact
  monodromy `M_0`.  DICHOTOMY: if `M_0` is spectrally spread, the
  commutator map is a quantitative submersion and every holonomy
  `delta`-close to `1` is EXACTLY absorbable — `(R1)` solves and the
  block is done; if `M_0` is nearly scalar, the block is close to a
  scalar multiple of a smaller exact model and the multiplicity
  tensor factor splits off — recurse on the smaller model.  The
  proposed proof of the whole claim is this dichotomy-plus-induction
  on every cycle, with `(R2)` (the `w(2)`-word) entering as a second
  holonomy on the same cycles after `(R1)` is exact; the remaining
  bookkeeping risks are the accumulation of losses along the
  induction and the joint treatment of the two holonomies, both
  compact-space accounting questions with no dimension entering.
- **Induction accounting (2026-08-21, terminal layer).**  The
  absorbable part of a holonomy is its component orthogonal to the
  cycle monodromy's centralizer, with modulus `delta / gap` — the
  differential of the twisted commutator map is `Ad(M_0) - 1`, so
  absorption is a quantitative submersion exactly off the resonant
  (centralizer) directions.  The resonant residue lives in the
  refined structure given by `M_0`'s spectral clusters, where the
  monodromy is near scalar and the classification descends one level
  in `(cycle, omega)`-data: the induction is a SECOND multiscale
  clustering argument of the same species as the local-rigidity
  proof, with geometrically chosen cluster gaps and a Holder total
  modulus, dimension-free.  After `(R1)` is exact the residual
  freedom is the `psi`-invariant torsor, and `(R2)`'s holonomy meets
  the same dichotomy one level deeper — a two-step filtration of one
  induction.  TERMINAL OPEN POINT, stated exactly: the two resonant
  residues define a class in the cohomology of the solenoid shift on
  the commutant tower; the class vanishes on every exact finite
  model, and the claim needs its CONTINUITY under multiscale
  refinement — a statement about a concrete compact dynamical
  system, the true bottom of the SL_2 far sector after tonight's
  reductions.
- **Syzygy computation, done (2026-08-21): the pair lies on the
  joint-coboundary variety, with one honest residual.**  Rank-one
  Steinberg for `SL_2(Z[1/2])` on `e_+(x), e_-(x), h` has, as its
  defining identities beyond the two abelian additivities: (A) the
  Weyl relation `w e_+(x) w^{-1} = e_-(-x)` with
  `w = e_+(1) e_-(-1) e_+(1)`, and (B) the torus action
  `h e_+(x) h^{-1} = e_+(4x)`, with `h = w(2) w(1)^{-1}` where
  `w(t) = e_+(t) e_-(-t^{-1}) e_+(t)`.  The KEY SYZYGY is the
  Steinberg cocycle identity `w(s) w(t)^{-1} = h(s/t)` (diagonal
  `diag(s/t, t/s)`), a relation among the `w`-words ALONE.  Applied
  to the two microstate holonomies `e_1` (from the `w(1)`-swap) and
  `e_2` (from `w(2)`), it forces `e_2 = (transport of e_1 under the
  x4 map) + delta(h-defect)`: the two holonomies are NOT independent
  — `e_2` is the `x4`-pushforward of `e_1` up to the ALREADY-EXACT
  `h`-relation defect.  So the single unknown `c` absorbing `e_1`
  simultaneously absorbs `e_2` UP TO the commutator of the correction
  with the exact torus, `[c, h_exact]`, which is itself a twisted
  coboundary in the SAME cycle system and closes by the cascade.  Net:
  the two-equation obstruction reduces to ONE plus an exact-torus
  commutator term, and the joint-variety placement HOLDS.  Honest
  residual: the `x4`-pushforward step loses the `h`-defect modulus,
  which the top-down exactification bounds at fixed depth — so the
  constant depends on the relator depth, uniform in dimension but not
  yet shown uniform in the depth needed as the microstate accuracy
  improves.  That depth-uniformity is the single remaining
  quantifier, and it is a statement about the fixed BS(1,4) modulus,
  not about SL_2 — the smallest the crux has ever been.
- **The depth concern dissolves on the odd model (2026-08-21).**
  On the EXACT odd skeleton the base has odd order and `z -> z^4`
  permutes its spectrum bijectively (4 is a unit mod odd order), so
  every `x4`-pushforward in the syzygy is a LOSSLESS automorphism:
  the depth-`4^k` amplification only ever afflicted APPROXIMATE
  towers, and leg (1) has already moved us onto the exact odd model
  before the syzygy is applied.  The `h`-defect term is not an extra
  loss either — the single torus `h` acts as `x4` on `e_+` and `x/4`
  on `e_-`, so the lower `h`-relation IS the swap-torus residual
  `(R1)` we already track, not a new quantity.  Net: after leg (1),
  all `x4` maps are exact, the two holonomies collapse to one by the
  syzygy, and the ONLY analytic content left is the convergence of
  the single-holonomy absorption cascade — the exact same species as
  the PROVED local-rigidity theorem `bs14-exact-representation-
  variety-is-hs-locally-rigid`.
- **Honest terminal assessment (2026-08-21).**  With the depth
  concern gone, this claim reduces to exactly two technical lemmas
  ATOP the proved local-rigidity core: (a) the solenoid-group
  extension of local rigidity (recorded follow-on; same multiscale
  proof with the joint solenoid spectrum), and (b) rigorous
  Holder-modulus convergence of the absorption cascade (argued of the
  proved theorem's species, not yet written line by line).  If both
  hold, the skeleton claim holds, and the whole chain to the goal
  closes.  This is a plausible proof ARCHITECTURE for
  `SL_2(Z[1/2])` HS-stability, which is the Dogon--Vigdorovich open
  problem: difficulty is CONSERVED, as it must be for a genuine open
  problem, but it is now localized in two named same-species lemmas
  over a proved base rather than diffused across the whole stability
  question.  Not landed; sharply reduced.  A rigorous write-up of
  (a) and (b) is the work; nothing here claims those are automatic.
- **The two named lemmas reduce to one (2026-08-21).**  Lemma (a),
  the solenoid-group extension, is not a separate obligation: the
  solenoid group `Z[1/2] rtimes_4 Z` is literally `BS(1,4)` (the roots
  `t^{-k} a t^k` are words in the two generators), and the skeleton
  `<u, h> <= SL_2(Z[1/2])` is exactly this group, so the proved
  `bs14-exact-representation-variety-is-hs-locally-rigid` already
  covers the whole tower.  What remains is (b), which in structural
  terms is the shared-`h` matching of two exact `BS(1,4)`
  representations into one exact `SL_2(Z[1/2])` representation.  In
  the Serre picture `SL_2(Z[1/2]) = SL_2(Z) *_(Gamma_0(2)) SL_2(Z)`
  the matching is an edge condition, and it coincides with the
  already-isolated half-parabolic square-root edge of
  `far-sector-vertex-handled-edge-is-square-root`: this route and the
  Iwahori route meet at the same edge, now carrying two inputs the
  edge lacked before -- odd-tower local rigidity and the syzygy
  collapse of the two swap holonomies to one.
- **Where the obvious attack could die.**  If the torsor fixed-point
  problem has an obstruction class that grows with the odd order,
  the loss would not be dimension-free; the analogue at the level of
  finite models is a cohomology comparison for
  `SL_2(Z/m)`-extensions, uniform in odd `m` — Selberg/(tau) should
  control it, but this is exactly the step that must be written.
