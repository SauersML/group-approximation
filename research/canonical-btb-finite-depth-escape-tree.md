---
rg: 2
id: canonical-btb-finite-depth-escape-tree
kind: claim
title: Complete the binary-tetrahedral detected finite adaptive tree by one oriented return
distinct_from:
  finite-depth-adaptive-selected-atom-escape-tree: That uses the original Pauli quarter and leaves payload-to-root detection inside its open escape row; this uses a fresh canonical central half, has already detected every source root, and asks only for the return from the conditioned E5 packet.
  canonical-bcs-root-detection-via-binary-tetrahedral-bridge: That supplies positive mass on each actual source root; this must place a fixed fraction of the resulting spectator-trivial fiber outside its current carrier.
  hs-steinberg-morita-trace-additivity-on-adaptive-blocks: That asks for a globally additive mass on all named diagonal blocks; this permits an unoriented analytic return along only the actually reached finite branch.
---

**OPEN ORIENTED-RETURN GATE.**  The literal extended presentation
of `canonical-bcs-root-detection-via-binary-tetrahedral-bridge` cannot be
used unchanged: `binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign`
shows that its initial packet-reducing hull already fills the whole
`J=-1,ell=-1` sector.  The required seed-protected version is now supplied
by `protected-adaptive-btb-wordization-preserves-canonical-budget`: its edge
two-group contains the context packet, `J`, and `B`; all source and range
projections commute with `B`, while the arrow itself may switch `B`-sectors.
At each
reached node choose a maximal forbidden type and put

```text
A_sigma=Q_sigma P_(i(sigma)).                          (CBR1)
```

The established binary-tetrahedral bridge and the two-pair E5 cell retain,
after fixed finite-packet correction, a canonical conditioned fiber
`F_sigma<=A_sigma` with

```text
tau(F_sigma)>=(1/18)tau(A_sigma)-C sqrt(E_pres).       (CBR2)
```

Prove that the stabilized three-line arrow, or any fixed ordinary-group
word with the same source, has a corrected marked-sector range `D_sigma`
such that

```text
tau(Q_sigma D_sigma)
 <=tau(F_sigma)-eta tau(A_sigma)+C' sqrt(E_pres)       (CBR3)
```

for one `eta>0`, only along the finitely many reached carriers.  Equivalently
it is enough to transport a fixed fraction of `F_sigma` outside `Q_sigma`.
The next carrier is the common reducing hull for the shared BCS tuple and all
attached finite packets containing `Q_sigma join D_sigma`.

For these seed-protected adaptive amalgams, the common reducing
hull stays below the central `J=-1,ell=-1` sector; the seed has canonical
trace `1/8`, that sector has trace `1/4`, and the maximal-atom BCS gap would
supply the same supercritical recurrence once `(CBR3)` holds.  Thus the
required fixed depth still satisfies

```text
(1+eta beta/M)^N>2.                                   (CBR4)
```

The missing row may be proved either by orienting the three-line Morita table
on the actual parent carrier or by an unoriented word whose analytic range
has the overlap loss `(CBR3)`.  No payload-to-root estimate, finite-root
spectral splitting, seed-density argument, or perfect-model extension
remains in this modified route.

## Attempts

- **Use the three-line arrow without an additional orientation row.**  Its
  stabilized source and range are conjugate and its spectator-trivial fiber
  now has positive mass by `(CBR2)`.  But the conjugating word may return that
  fiber to the same parent multiplicity reservoir.  Equality of root spectra
  and Murray--von Neumann source/range size does not control
  `tau(Q_sigma D_sigma)`; this is the multiplicity gauge isolated in
  `literal-prefix-three-root-swap-retains-typed-carriers`.
- **Take an independent finite exit tag.**  This produces an orthogonal
  address cylinder only by paying the same character fraction at the source,
  so the capacity ledger is trace-neutral.  The obstruction is
  `independent-address-capacity-cannot-drive-selected-atom-growth`.
- **Use the reducing hull itself as the mixer.**  The hull supplies the next
  valid BCS carrier after an overlap loss, but it cannot create that loss;
  exact isotropic mixing gives only logistic approach to capacity by
  `isotropic-mixing-has-only-logistic-carrier-growth`.
- **Replace the adaptive return by finitely many static packet conjugates.**
  `canonical-btb-static-packing-has-capacity-ceiling` separates the two
  projections involved.  A literal BTB-detected character is a fixed
  group-algebra projection, but canonical trace already bounds separate and
  simultaneous packing by `3M/beta` and `3/beta` on the BTB Pauli seed.
  The projection on which `(CBR2)` is representation-uniform instead contains
  the analytic reducing hull `Q_sigma`; an HNN relator cannot name it without
  precisely the missing payload-conditioned carrier compiler.  Finite
  Heisenberg refinements only partition the same source trace.
- **Graft the complete affine-Leavitt signed Whitehead occurrence system.**
  `full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark` proves that
  this really removes the isolated `UT_4`/rectangular countermodel in every
  *exact* finite-dimensional representation: the active kernel ideal kills
  all three Whitehead factors and the odd controlled-Pauli row then kills the
  central mark.  The proof does not promote to normalized HS microstates.
  Its load-bearing step intersects exact root kernels to obtain a finite
  coefficient quotient; an HS-small error may have full rank.  Hence the
  full occurrence graft does not yet imply `(CBR3)`.  It replaces the local
  gauge by the same dimension-uniform kernel-ideal/MF-radical gate as the
  affine-Leavitt route itself.  In fact
  `whitehead-clifford-graft-hyperlinear-iff-base`
  proves that this finite cyclic graft is hyperlinear exactly when its
  affine-Leavitt vertex group is hyperlinear.  Its regular representation
  satisfies every occurrence row while retaining typed-support leakage
  `1/16`.  Thus no finite-tracial spectral-gap or square-function promotion
  of this graft can prove `(CBR3)`; the missing step must be genuinely
  finite-coordinate.

- **Use only edgewise protected BTB/three-line returns.**
  `btb-three-line-tree-retains-multiplicity-return-gauge` puts the full
  conditioned `1/18` fiber in Schur form.  Every separate three-line edge
  still has an arbitrary multiplicity unitary, and on a finite tree those
  gauges can be aligned independently so the returned fiber stays inside
  the reached carrier.  A complete root-controlled reflection packet can
  force one outer-type escape, but its finite orbit then saturates and
  cannot be reused; fresh copies pay the independent-address capacity.
  Therefore the return needs a cross-edge or payload-sensitive two-cell
  with nonzero multiplicity charge.

  The path-specific qualification is now closed for the
  **seed-support-preserving** part of this edge-local class, not merely for
  arbitrary reducing subcarriers.
  `canonical-btb-tree-local-returns-have-stationary-reached-carrier` starts
  with the full protected seed `e_0`, aligns the first edge gauge so its
  return lies below `e_0`, and observes that the prescribed minimal reducing
  hull is then again exactly `e_0`.  Induction gives the same full reached
  carrier at every node and an exact finite-dimensional stationary
  specialization of all such tree-local packet/covariance/return rows.  The
  hypothesis is essential: the complete irreducible `S_3` outer action can
  move the selected protected-sign type before the multiplicity gauge is
  chosen and hence forces one genuine outer-type escape.  Its orbit then
  saturates, as recorded in
  `btb-three-line-tree-retains-multiplicity-return-gauge`.  Thus a reusable
  successful finite gadget must contain a genuine cross-edge or
  payload-multiplicity row, or a non-prepaid renewal mechanism for such an
  outer-type escape; another seed-support-preserving edge actuator cannot
  exploit canonical reachability.

- **Couple two complete `S_3` outer escapes by a finite projective
  holonomy/two-cell.**
  `finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape` closes this
  finite two-level class.  After the first genuine outer escape, the
  prescribed packet hull contains the complete irreducible local `S_3`
  type.  A relation between the two edge gauges restricts on its stabilizer
  to a projective multiplicity relation.  Whenever that holonomy factors
  through a finite quotient, the inverse-twisted regular module cancels the
  packet multiplier and induces to an exact finite-dimensional orbit-sum
  model.  Stabilizer returns have full overlap with the post-escape carrier.
  A return moving to another packet type can escape again, but each such
  move consumes one equal finite-orbit summand; the initial type had only
  `1/|O|` of that orbit capacity.  Fresh palettes likewise either start with
  their full orbit or pay the primitive-line factor before use.  Thus a
  non-prepaid reusable cross-edge cell must instead have an infinite
  stabilizer twist with a quantitative finite-dimensional-radical floor, or
  be a genuinely nonautomorphic proper-corner incidence.  Finite
  Clifford/projective/triangle-face holonomy only synchronizes a prepaid
  finite orbit.

- **Replace the finite holonomy by a finitely presented infinite active
  stabilizer.**
  `reusable-s3-renewal-is-twisted-radical-or-proper-corner` classifies this
  residual.  If the return remains automorphic and supplies an indefinitely
  reusable supercritical recurrence, iteration followed by division by its
  growth factor makes the polynomial depth errors summable and yields a
  dimension-uniform HS-radical estimate on the active packet corner.  Clifford
  reduction then identifies the radical with the inverse twisted stabilizer
  character, while twisted-regular microstates would contradict that estimate.
  Thus this branch has already produced a non-CE twisted group algebra; it is
  not a weaker infinite-gauge trick.  If the return is instead genuinely
  nonautomorphic, equal-rank compression is trace-flat and unequal-rank
  compression is the existing trace-cyclic proper-corner gate.  A universal
  or tracially functorial implementation collapses its marked complement in
  the regular factor.  The sole remaining exception is therefore the
  matrix-coordinate source-Gram authentication asked for by the native
  proper-corner nodes.

  The central-extension step does not reduce this burden.
  `s3-projective-radical-central-extension-has-exact-robust-fork` constructs
  the finite central extension of the active stabilizer explicitly.  Exact
  projective invisibility merely kills its chosen central character in exact
  finite-dimensional representations, a condition known to occur in a
  finitely presented sofic group.  Once the indefinite recurrence supplies
  the uniform HS modulus, central spectral cutting immediately makes this
  extension nonhyperlinear.  Hence the robust stabilizer lemma is already a
  complete ordinary-group proof, while its exact endpoint is insufficient.

- **Use a fixed menu of compressed pairwise antiphase tests.**
  `compressed-antiphase-menu-implies-btb-escape` closes the matrix-capacity
  part of this idea.  For a fixed menu size `L` with
  `L beta/(18M)>=4`, opposite-phase estimates on the compressed contractions
  `T_k=Q_sigma u_k F_sigma` force one branch to lose at least
  `(1/36)tau(A_sigma)-O(sqrt(E))` from the current carrier.  Thus this
  hypothesis proves `(CBR3)` with `eta=1/36`, while remaining vacuous in the
  perfect marked model because `F_sigma=0` there.  The direct group
  implementation does not work: by
  `literal-antiphase-branches-recreate-regular-character-packing`, conjugating
  a pair tag into opposite characters on the whole Reynolds source makes the
  literal translates pairwise orthogonal in every tracial representation.
  Canonical trace then restores the ordinary finite-character packing ceiling
  (and too many branches collapse the source already in the regular model).
  The exact remaining two-cell must therefore impose antiphase only after
  compression by the reached carrier, or equivalently read a matrix-coordinate
  cross-Gram, without imposing full source conjugacy.

- **Localize pairwise phases by the cyclic-hull definition of the carrier.**
  `cyclic-hull-antiphase-has-propagation-or-radius-firewall` splits the two
  natural implementations.  A pair tag commuting with every reducer does
  preserve `Q_sigma`, but any phase fixed on a named seed propagates to its
  whole cyclic component and again gives literal packing rather than a phase
  on the proper contextual cut `F_sigma=Q_sigma e`.  A finite support or
  tight-frame formula cannot name the cyclic hull instead: dihedral cycle
  representations have full cyclic hull while every fixed word window has
  normalized support tending to zero.  Thus the missing path-specific cell
  must contain a mixed corner loop coupling the Reynolds atom to reducer
  transport; centralizer-plus-seed and finite-radius hull surrogates are
  excluded.

- **Use an exponent-balanced additive/Morita corner loop.**
  `btb-balanced-loops-stop-at-same-object-reflection`
  supplies the minimal exact countermodel.  Every finite pasting of
  rank-five/six Steinberg multiplication triangles is realized by separate
  finite source and target copies in the rectangular Morita model.  A fixed
  scalar projective phase on the closed pair is canceled by one inverse Weyl
  multiplicity module (with only `O(1/d)` remainder off complete blocks).
  The detected fiber can then return wholly inside the carrier.  The first
  row not absorbed by this model is the same-object support reflection
  `(1-2f)W(1-2e)W^*=1`; the present Clifford groupification evaluates its
  target reflection as `(1-2f) tensor V`, so the uncontrolled multiplicity
  involution survives precisely in that row.  Therefore the remaining
  mixed loop must authenticate this same-object reflection, or prove its
  support-leakage consequence by a genuinely matrix-only estimate.

- **Kill the Clifford twist with two coupled reflections, determinant, or
  mixed reducer covariance.**
  `coupled-reflections-reduce-to-the-active-gauge-profile` gives the complete
  Schur reduction.  On each authenticated packet type every normalizer is
  `C_j tensor V_j`, and every finite added row becomes a projective word
  relation on the `V_j`.  For a controlled reflection `C tensor V` and an
  identity-outer anchor `I tensor A`, the same-object row is exactly the
  residual equation `VA=1`.  Any exact or asymptotic matrix model of the
  resulting active gauge presentation with `VA` separated tensors back to a
  countermodel; fixed parity and projective checks have such models by Weyl
  block filling.  A dimension-uniform estimate for `VA` is therefore already
  the missing HS profile on the active gauge group.  The only local algebraic
  escape is a new row which forces `VA=1` while preserving the packet type;
  standard packet dressing and balanced loops do not.

- **Avoid the literal reflection and use one globally balanced HNN edge.**
  `balanced-hnn-conditional-gap-forces-carrier-escape` proves the exact
  support-leakage estimate.  If `Up_sU^*=p_t` and the reached carrier reduces
  both character projections, then the returned source obeys
  `tau(Q U(Qp_s)U^*)<=tau(Qp_t)`.  Hence any conditional imbalance
  `tau(Qp_s)-tau(Qp_t)>=eta tau(Qp_s)-O(sqrt(E))` proves `(CBR3)` directly,
  with robust HNN errors still only `O(sqrt(E))`.  The controlled-Clifford
  atoms `p_s=e z_+` and `p_t=f(z_++z_-)` are globally trace-balanced and admit
  the required regular-safe HNN edge, but their conditional gap is
  `(tau(Qz_+)-tau(Qz_-))/4`, which vanishes on the canonical balanced packet.
  Thus this removes the residual-`V` gate conditional on a payload-oriented
  character imbalance; finite balanced packet rows alone do not create that
  imbalance.

- **Manufacture that imbalance with a larger finite payload/orientation
  packet atlas.**
  `finite-packet-flow-keeps-payload-orientation-balanced` gives an exact
  stationary countermodel.  The common regular multiplicity vector is
  compatible with every finite restriction, central cut, conjugacy and
  balanced HNN edge, and on the full protected packet carrier it gives
  `tau(Q_reg p_s)=tau(Q_reg p_t)` for every globally balanced edge.  Tensoring
  this model with a structural shared BCS tuple leaves a positive forbidden
  Reynolds atom while every packet-only conditional gap remains zero.
  Balanced doubles, finite orientation permutations and the standard odd
  selector have the same stationary model.  Hence a finite packet flow cannot
  create the scalar gap: the adaptive construction must exclude this regular
  profile on the actual reached hull by a path-specific nonstationary
  coefficient relation or a proper-corner return.

- **Replace the finite atlas by a finitely compressed Baumslag first-hit
  tail.**
  `baumslag-binomial-prefix-centralizer`
  is a genuine positive advance: in the three-generator torsion Baumslag
  register, two centralizer rows force a translated transporter to commute
  with every earlier lamp, and the binomial expansion plus the quadratic Dehn
  bound gives polynomial HS word cost.  But
  `baumslag-address-geometric-stationary-profile` supplies exact
  finite-field affine quotients with arbitrarily long independent lamp
  prefixes.  On their regular blocks `tau(C_n)=2^(-n)` and
  `tau(X_n)=2^(-(n+1))`; tensoring with a positive structural forbidden atom
  leaves a geometric compensation tail.  Orthogonality and prefix transport
  are exact, but `(FHC1)` fails by macroscopic mass.  Hence infinite address
  compression does not replace the missing supercritical active-child or
  proper-corner incidence.

- **Use the two complementary coarse-to-controlled-sign HNN edges.**
  `two-orientation-hnn-packet-prepays-escape` shows that this attractive
  packet contains a real one-use estimate: on `Q<=z_+`, conjugating `Z_1` to
  `s=t` sends `A=QPe` to a target whose overlap with `Q` is at most
  `tau(A)/2`, and the `z_-`/`Js` edge is identical.  But the missing target
  rank is the sibling orientation's rank-three complement.  On the exact
  balanced module `S_+ direct-sum S_-`, the HNN letters can route each whole
  apparent exit into that sibling.  The orientation union therefore has no
  exit.  Preselecting one primitive type in each of `N` fresh packets makes
  the seed `2^(-N)` as large, and each packet hull merely releases its prepaid
  factor two.  Hence these edges do not form orthogonal first-hit layers and
  cannot prove `(CBR3)` without an additional payload-conditioned row that
  excludes the sibling companion.

- **Add a property-`(T)` actor, stable finite subgroups, or arbitrary finite
  cross-edge words.**
  `hyperlinear-fiber-cannot-orient-btb-return`
  substitutes the authenticated outer BTB--E5 matrices and studies the
  resulting presentation on the anonymous multiplicity factor.  If that
  active presentation has asymptotically exact finite-dimensional models,
  spectator amplification defeats any return estimate required uniformly for
  all reducing carriers.  It does **not** alone defeat `(CBR3)`: the canonical
  seed amplifies with the full spectator identity, and so do its prescribed
  minimal reducing hulls; the invariant half need not be a reached carrier.
  Kazhdan projection and finite-group stability still leave this local fixed
  algebra.  A mixed system may work either by giving the forbidden active
  fiber its own dimension-uniform HS floor, or by coupling cross-edge words to
  the fixed seed/minimal-hull recursion so that the active model cannot be
  installed block-diagonally on the actual reached carrier.

  The qualification is exact, not heuristic:
  `canonical-reached-hulls-tensor-amplify-fully` proves that the canonical
  carrier at every vertex amplifies as `Q_sigma tensor I`, whereas the usual
  spectator countermodel uses a proper invariant half.  Any path-specific
  no-go must therefore construct a model on the actual full reached hull, not
  merely exhibit an invariant reducing subprojection.

- **Name the actual hull by cyclic generators, finitely many normal
  conjugates, or a bounded successive-seed two-cell.**
  `finite-word-data-cannot-authenticate-canonical-cyclic-hull` gives an exact
  density-`1/8` permutation model.  Splicing two block cycles in only two
  coordinates changes the generator by `2/sqrt(d)` in normalized HS norm but
  changes the minimal reducing hull from the seed block to the identity.
  Every fixed bounded word menu sees only an `L`-neighborhood of the seed and
  has asymptotically identical defects and moments before and after the
  splice.  Therefore finite generation and finite normal generation do not
  themselves prevent block-diagonal active models, and a two-cell which only
  records bounded word membership cannot authenticate the parent hull.  This
  leaves open a two-cell with a genuine dimension-uniform spectral or typed
  payload estimate; that additional estimate, rather than cyclicity, would be
  the load-bearing theorem.

Thus the deferred attack is genuinely the one row `(CBR3)`, with the root,
spectator, and protected-commutation gates removed.  The finite relations
`[q_sigma,B]=[d_(sigma,i),B]=0`, their characteristic-three wordization,
the injected BTB edge groups, and the `1/8`-to-`1/4` canonical budget are
certified by `protected-adaptive-btb-wordization-preserves-canonical-budget`.
Only the return estimate remains uncertified.  A sufficient sharp form is the
compressed-antiphase estimate `(CAM4)` from
`compressed-antiphase-menu-implies-btb-escape`; full literal antiphase is
excluded by the regular-packing firewall above.  Equivalently, after the new
local-carrier no-go, one must either construct a payload-conditioned
cross-edge specialization satisfying `(CAM4)` or the uniform floor `(FHC4)`,
or exploit the canonical seed/minimal-hull path to forbid block-diagonal
alignment on its actual reached carriers.  A merely fiberwise hyperlinear
specialization cannot prove a return estimate quantified over arbitrary
reducing subcarriers.
