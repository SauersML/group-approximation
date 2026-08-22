---
rg: 2
id: first-cycle-signed-hecke-chord
kind: claim
title: Close the first non-tree BCS overlap without changing the join-tree context partitions
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  simultaneous-block-escaping-context-holonomy: that asks for the complete coupled construction on every cycle; this assumes the exact join-tree atlas and isolates one additional chord.
  signed-hecke-block-escaping-cycle-holonomy: that is the full balanced atlas target; this is its first irreducible cyclic step.
---

Start with the explicit atlas of
`join-tree-bcs-has-explicit-signed-hecke-atlas`.  Let one additional incidence
identify variable `x` between two contexts whose current signed marginals are
`X_x^(0)` and `X_x^(1)` with equal canonical trace and equal finite packet
ranks.  Enlarge the finitely presented group and alter the context corner
unitaries, without changing their already valid context partitions, so that

```text
X_x^(0)=X_x^(1)                                           (FCH1)
```

holds as an exact algebraic identity.  All previous overlap identities and at
least one non-root assignment projection must survive.

## Attempts

- **A stable letter gives only conjugacy.**  Equal ranks provide an algebraic
  corner unitary carrying one sign to the other, but adjoining it records
  `UX_x^(0)U^*=X_x^(1)`, not `(FCH1)`.
- **Regauge one endpoint: breaks its tree separator.**  Conjugating the whole
  endpoint context to close the chord generally moves the marginals used to
  attach it to its parent.
- **Centralize the tree separator: exact criterion known.**  The allowed
  endpoint regauges are the commutants of their separator tuples.
  `sequential-marginal-holonomy-is-conditional-rank-matching` decides whether
  one endpoint can install the chord sign while fixing its separator, and
  `free-phase-context-escape-criterion` describes which separator blocks can
  additionally move genuine assignment atoms.
  `chord-regauging-is-relative-commutant-feasibility` now proves that the two
  endpoint orbits meet exactly when their transported separator algebras have
  a common-commutant involution realizing both conditional rank tables.  In
  particular they cannot meet inside any finite root block where the two
  separators generate the full matrix algebra.  The open construction is to
  manufacture that involution with finite group-word support in the escaped
  corner.
- **Commuting-separator subcase: reduced to max flow.**
  `commuting-separator-chord-is-capacitated-transport` proves that if the two
  transported separator algebras commute, the common involution exists
  exactly when one finite integral transportation problem satisfies its cut
  inequalities.  Joint block dimensions are capacities and the two
  conditional rank tables are its demands.  A successful construction may
  therefore target commuting escaped separators with adequate joint block
  capacity; otherwise it must solve the genuinely noncommuting relative-
  commutant problem.
- **The general finite target is now algorithmic.**
  `finite-relative-commutant-chord-is-bounded-integer-feasibility` eliminates
  the unknown common involution and gives one bounded Wedderburn integer
  system, without assuming that the separators commute.  Equal total ranks
  alone fail already for the transverse Pauli separators in `M_2(C)`.
- **The acyclic ambient group cannot contain the finished answer.**
  `cycle-closure-cannot-remain-in-the-join-tree-group` proves that the direct
  product of the finite packet and the fresh free-phase groups is residually
  finite.  Completing every chord in that unchanged corner would create a CE
  trace on the no-CE BCS.
- **Finite-edge HNN transport is exact but globally dead.**
  `finite-character-idempotents-have-exact-hnn-transport` shows that matched
  finite-subgroup character pieces can be transported and assembled exactly.
  However `finite-edge-hnn-closures-cannot-finish-the-nonce-atlas` proves that
  finite iterations of these HNN extensions remain residually finite.  The
  decisive chord must use an infinite associated subgroup or another
  genuinely non-residual-finiteness-preserving extension.
- **A dense infinite-edge literalization collapses to a mapping torus.**
  `britton-support-traps-dense-free-phase-chord` proves the converse support
  rule for additive HNN transport: if `tXt^(-1)` returns to the base group
  algebra, every coefficient in `supp(X)` must lie in the associated
  subgroup.  A dense escaped free-phase marginal has support generating the
  whole effective packet group `K_D times L_D`.  Transporting two such
  marginals therefore forces a whole-base automorphism HNN, which is
  hyperlinear.  A live infinite-edge chord must be separator-block sparse,
  genuinely multi-piece/non-graphical, or non-HNN.
- **A standard sparse regauge only exposes a free factor.**
  `sparse-free-phase-support-is-a-free-factor` associates to the chord matrix
  its off-diagonal support graph and proves that the independent-phase
  difference subgroup is a free factor of rank `D-c`, where `c` is the
  number of graph components.  It may be proper and nonamenable, but a
  single termwise HNN between two such supports is residually finite by
  `free-factor-phase-graph-hnn-is-residually-finite`.  Thus sparsity remains
  live only when combined with nonprimitive labels, coupled pieces, or a
  non-HNN operation.
- **Pure transport between finitely many packet types is still matricial.**
  `finite-projective-sector-groupoids-have-conjugate-absorbers` identifies
  all type-changing intertwiners with a finite projective groupoid and
  cancels its cocycle by tensoring each arrow with its conjugate.  This covers
  arbitrary finite return holonomy and two inequivalent sectors.  Therefore
  the desired chord cannot be one sector bisection or a longer finite path;
  one block entry must be a coherent sum of multiple paths, the genuinely
  additive corner unitary already demanded here.
- **The smallest additive two-path cell is still gauge-free.**  In the
  two-dimensional `D_8` type, an order-three HNN automorphism of a Klein
  subgroup carries one rank-one type projection to its complement.  The
  element `V=t p_0+t^(-1)p_1` is an exact nonnormal corner involution, but on
  multiplicities it is `[[0,U^*],[U,0]]` and a block-diagonal gauge removes
  `U`.  Thus two paths are necessary but one isolated two-path cell does not
  close the chord.  The next target is a shared-block loop of at least two
  additive cells whose relative gauge is read by another corner polynomial.
- **Shared rank-one swap cycles only read ordinary isotropy.**  Two parallel
  `D_8` cells expose `U_u^*U_t` as
  `p_0u^(-1)t p_0`; an `A_4/V_4` triangle exposes
  `U_20U_12U_01` as `p_0t_20t_12t_01p_0`.  Leaving the return word free leaves
  arbitrary holonomy.  Equating the whole return word to its compatible
  finite label merely removes a graph-of-groups cycle.  Imposing only the
  compressed equality would be useful, but is exactly the unresolved
  algebraic corner term-pairing operation.  The next genuinely new finite
  cell must use transverse noncommuting source partitions so multiplication
  leaves a sum of at least two return paths.
- **One transverse `D_8` pair gives a sum, but unitarity collapses it.**  For
  Z- and X-basis additive swaps with multiplicity gauges `U,W`, the first
  two-return corner is `C=(W-W^*)U/2` and
  `1-C^*C=U^*((W+W^*)/2)^2U`.  Making `C` a corner unitary forces
  `W^*=-W`, at which point the X swap becomes one off-diagonal Z transport
  and the two paths coalesce.  The live transverse chord must therefore use
  a weaker positive-defect polynomial or couple several transverse sums;
  exact unitarity of one sum returns to the groupoid fence.
- **Abstract two-path payment is exactly corner leakage.**
  `two-path-holonomy-is-paid-by-corner-leakage` removes the special `D_8`
  coordinates.  If `A,B:q->p` are the two packet paths and
  `V=A^*B`, then for `K=(A+B)/2`,
  `q-K^*K=(q-V)^*(q-V)/4`.  Matching `K` to an authenticated corner unitary
  therefore controls `V` with a dimension-independent modulus.  But every
  such `K` is the compression of its exact Julia unitary, whose complementary
  leakage has precisely that Gram mass.  Hence two paths are analytically
  sufficient only after another relation forces the arithmetic word to
  preserve the selected corner (or pays its leakage); compression equality
  alone has an exact finite-dimensional escape.
- **A Hadamard selector commutator charges that leakage by one word.**
  `hadamard-selector-commutator-charges-two-path-leakage` uses the fixed
  two-dimensional `D_16` packet.  If one ordinary return `d` centralizes its
  `Z` selector and has blocks `A,B`, then the word `Y=H d H` has selected
  block `(A+B)/2` and complementary block `(A-B)/2`.  The single added
  relator `[Y,Z]=1` has squared HS defect exactly
  `||A-B||_2^2=||1-A^*B||_2^2`; it therefore supplies the missing positive
  leakage payment, while `d->1` retracts onto the packet and preserves every
  non-root packet projection.  The new minimal gate is purely syntactic:
  construct a selector-central **group word** `d` whose two blocks are the
  desired path holonomies.  Existing piecewise transport gives an algebraic
  corner sum, and controlled predication assumes rather than manufactures
  such a controlled word.
- **A wreath or semidirect product cannot manufacture the diagonal word.**
  `hadamard-does-not-semidir-independent-selector-blocks` proves the exact
  obstruction.  Hadamard conjugation sends `diag(A,B)` to the
  average/difference matrix and returns to the selector centralizer only
  when `A=B`.  Thus an HNN/semidirect action normalizing the selector-central
  subgroup identifies the branches before they are tested.  If the two base
  factors are instead adjoined freely, arbitrary representations do not
  localize them to opposite selector lines.  In the central-selector case,
  the universal corner equations for one group element force the two desired
  path words to differ by at most the central involution.  The remaining
  wordization must therefore be genuinely nonnormalizing/type-specific; a
  literal `G times G` base does not provide it.
- **The established q14 wall cannot charge the surviving common block.**
  `q14-literal-holonomy-charger-collapses-atlas-source` tests the direct
  synthesis.  If the q14 common frame is named by `u`, the second aligned
  transvection is `u t30 u^(-1)`.  Making the common D16 multiplicity word
  commute with `t30` turns q14 into `(t23 t30)^2=t20`; hence the quotient
  kills the simple A8 chart whose regular carrier is required by the wall.
  Without naming `u`, the frame remains analytic and tensor-separates from
  D16.  The D16 packet itself retracts and survives in both cases, but q14
  supplies no external multiplicity payment.
- **The degree-four common-corner separator is also blind to that block.**
  `s4-common-holonomy-charger-is-morita-blind` shows that appending powers of
  the common commuting holonomy `W` to four packet paths factors one unitary
  power out of every alternating monomial, leaving the `s4` norm unchanged.
  More strongly, a finite `M2` type, a two-qubit Pauli packet, and `W` coexist
  on `C^2 tensor C^4 tensor K` on one literal selector corner.  Demanding the
  stronger scalar-factor containment needed for Amitsur--Levitzki instead
  contradicts the exact Pauli model already at `W=1`.  Thus `s4` only helps
  after the missing non-Morita common-corner authentication has been proved.
- **The phase-rotated companion gives aggregate payment but kills
  completeness.**  Pairing `C_T=TU` with `C_S=SU` gives positive deficits
  `D_T+D_S=1` and squared HS energy at least `1/2` on one common carrier.
  Requiring both returns to be exact unitaries therefore annihilates every
  nonzero marked model.  If a selector chooses one return, the direct sum
  `W=i` on one sector and `W=1` on the other chooses the good branch
  everywhere.  The remaining chord must pin that selector by external
  incidence or derive the common carrier only after finite-matrix
  correction; the local two-cell algebra alone cannot orient the payment.
- **Pair opposite group-ring terms with new relators: circular.**  A single
  additive marginal equality can be forced by pairing its finite positive
  and negative support terms.  But
  `term-pairing-does-not-bypass-signed-hecke-holonomy` shows that a genuine
  tagged context projection has phase labels `h_i h_j^(-1)` satisfying the
  triangle cocycle.  Independent long tags destroy self-adjointness or
  idempotence; pairing those residuals reinstates the same cycle equations.
  General word-pairing quotients need not preserve the finite subgroup
  supporting `q` (even `xgx^(-1)=1` kills `g`).  Small cancellation is useful
  only if one proves relative injectivity for this specific coherent cycle,
  which is exactly the remaining chord theorem.
- **An infinite recursive tail is finitely compact for this target.**
  `finite-bcs-corner-diagram-is-finitely-witnessed` allows an arbitrary
  recursively presented ambient group and infinitely many auxiliary
  wrong-type or Bass--Serre relators.  Nevertheless the BCS algebra has a
  finite star presentation and the corner and generator images have finite
  group support.  Every required group-ring equality therefore uses only
  finitely many word-equality proofs, hence finitely many ambient relators;
  nonvanishing of the final corner persists on passing to that earlier finite
  subpresentation.  Thus a recursive tower can organize the search, but it
  cannot close the first chord only in the limit.  Some finite stage must
  already contain the load-bearing coherent holonomy while preserving the
  packet corner.
- **A feasible chord with a residual assignment collision is solved.**
  `feasible-chord-collision-has-free-phase-block-escape` first solves the
  exact finite relative-commutant integer system, then applies one Hadamard
  rotation inside a joint frozen-sign fiber and independent free phases.  It
  preserves every old separator and the new common chord sign while moving
  two genuine assignment atoms outside the finite root block.  The exact
  remaining first-chord cases are therefore: the integer system is
  infeasible, the frozen signs plus chord already separate every endpoint
  assignment, or several individually feasible cells cannot be realized by
  one context partition.
