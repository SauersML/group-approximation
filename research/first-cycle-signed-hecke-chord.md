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
