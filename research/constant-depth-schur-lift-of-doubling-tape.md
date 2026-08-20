---
rg: 2
id: constant-depth-schur-lift-of-doubling-tape
kind: claim
title: Lift only a constant initial segment of the BCS doubling tape through one fixed finite Schur packet
distinct_from:
  finite-dimensional-schur-lift-of-doubling-tape: that asks for one cell at every level and exactification uniform in an unbounded accumulated Clifford rank; this fixes the depth before the group is presented and exactifies the resulting finite packet as one fixed finite group.
  dimension-reported-schur-replica-halting-compiler: that chooses a challenge size from the witness dimension; this depth is chosen only from fixed marked-interface and contraction constants.
---

Choose a depth `m` satisfying the terminal absorption condition in
`finite-depth-contractive-computation-ladder`.  Construct a finitely presented
group `Gamma_m`, a nonidentity word `w`, and, from every finite-dimensional
tuple `V` with total squared normalized-HS relator energy `E(V)`, numbers

```text
0<=a_n(V)<=A                         (0<=n<=m)
```

such that fixed constants `a_*,K_0,C>0`, `0<lambda<1`, and a fixed
polynomial `p` obey

```text
a_0(V) >= a_*-K_0 sqrt(E(V)),
a_n(V) <= lambda a_(n+1)(V)+C p(n)sqrt(E(V))   (0<=n<m).          (CDS1)
```

The finite presentation may name all `m` cells separately.  It need not
contain a tape shift.  The entire nested packet chain is a single fixed
finite group, so ordinary fixed-group flexible HS exactification is
admissible even when its constant depends on the whole chain.  Fresh selector
families may be used at distinct levels, subject only to the finitely many
incidence relations actually required by `(CDS1)`.

The remaining construction problem is finite:

1. build a chain of `m` predicate rank gates with either literal inclusions
   `A_(n+1)=B_n` or fixed finite Morita bridges;
2. preserve the matrix-only oriented multiplicity current across each bridge
   without imposing global commutation of the fresh selector families;
3. derive the base marked floor and the `m` comparison inequalities with one
   fixed exactification/payment constant; and
4. retain an exact infinite-dimensional completeness representation in which
   `w` is nonidentity.

No assertion here says that finite depth automatically removes the selector
globalization obstruction.  It removes the **uniform-in-depth** and
**finite-presentation shift** obligations, leaving a bounded compatibility
problem.

## Attempts

- **Literal nested residual factors.**  Even for constant depth, assigning
  the next packet to the full residual multiplicity space forces its fresh
  selectors to commute with the preceding selector center.  Finite depth
  prevents this from becoming an infinite family, but does not by itself
  preserve the contextual marked model.
- **Branch-flip reset. Dead for every intermediate subgroup.**
  `flip-endpoints-cancel-schur-current` shows that every endpoint containing
  the flip either forgets the two child types on its kernel or fuses them into
  one orbit of doubled dimension.  The bounded search is therefore redirected
  to a one-sided proper-corner bridge which transports the child current
  before any balancing flip is adjoined.
- **Finite proper-corner chain. Active.**  Because `m` is fixed, it is enough
  to build and audit one finite sequence of corner bimodules and then
  exactify their union as a single finite packet.  The open point is an
  injective finitely presented group realization of those one-sided corners
  with the marked completeness representation intact.
- **Carrier-only center. Active and exact.**
  `fanizza-doubling-carriers-form-orthogonal-flag` proves that the derived
  carrier projections and first-hit projections in the source recurrence are
  a genuine orthogonal flag. Their reflection involutions commute and satisfy
  the group-word recursion `Z_(n+1)=Z_n X_nZ_nX_n^*`. Therefore a bounded
  chain may retain these carrier signs without globalizing the original BCS
  context selectors. The remaining nonlinear datum is exactly the positive
  overlap in `(FOF5)`. A valid one-sided bridge must discharge that overlap;
  imposing only the affine word recursion is insufficient.
- **Flip-free q-MASA reset. Interface solved, scale return open.**  The full
  q-MASA forgets the old selector subgroup and retains all corrected child
  signs.  However `q-masa-selector-bridge-is-scale-conservation` proves that
  an ordinary fresh-selector extension only trades spin dimension for scalar
  multiplicity.  The active finite search must therefore include a genuine
  proper-corner or two-dimensional holonomy relation; subgroup restriction
  matrices alone cannot close `(CDS1)`.
- **Controlled nested reset chain. Local model retained, promotion open.**
  Controlling the next packet on one selected child corner avoids the three
  literal endpoint failures in a distinguished two-level representation.  On
  the balanced ray its proposed current has `lambda=3/4` when `K_0=K_1=1`.
  The audit
  `research/artifacts/controlled-nested-reset-chain-audit-2026-08-20.md`
  isolates two missing implications.  First, `c u+(1-c)` is a group-algebra
  block rather than an ordinary word
  (`central-corner-block-is-not-a-group-word`), so the reported matrix model
  does not enumerate all representations of a group cell.  Second,
  `fixed-depth-rank-mesh-has-zero-hs-density` rules out obtaining `(CDS1)`
  merely by amplifying the integer rank quantum through a fixed number of
  corner normalizations.  The live form of this attack must give an explicit
  groupification and an amplification-stable positive-density functional.
  It cannot be a finite character-table theorem through the full depth:
  `finite-packet-cannot-realize-absorbing-contraction` evaluates that theorem
  on the negative regular summand and obtains an exact contradiction.  The
  needed strictness must come from joint ambient holonomy or contextual
  operator data absent from the finite restriction graph.
