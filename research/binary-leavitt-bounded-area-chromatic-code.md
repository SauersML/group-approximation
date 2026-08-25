---
rg: 2
id: binary-leavitt-bounded-area-chromatic-code
kind: claim
title: Compile the marked Leavitt root into a bounded-area infinite-chromatic commutator code
distinct_from:
  binary-leavitt-three-row-atomic-compiler: that returns three coefficient rows to one prescribed spectral atom and uses the Atomic Leavitt Gap; this bypasses projection decoding and instead asks for a uniformly bounded-area diagonal/off-diagonal commutator code.
  leavitt-steinberg-bounded-area-carmichael-lift: that seeks an order-three Carmichael family for a normalized-Hilbert--Schmidt obstruction; this seeks an operator-norm commutator table whose diagonal entry is the fixed involution z.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.**  In the fixed finite presentation of

```text
Delta=St_20(L_(F_2)(1,2)),             z=x_13(s_1t_1),
```

construct a graph of infinite chromatic number and words `c_v,h_v,a_v`
whose diagonal and edge discrepancies satisfy `(CCC1)--(CCC2)` with constants
independent of `v` and of the edge.

Finite orbit structure or two-transitivity alone is insufficient.  A choice
of an address representative is ambiguous by an element of the point
stabilizer, and commutation with finitely many stabilizer generators gives an
error proportional to the stabilizer word length.  Thus the compiler must
provide either a genuinely bounded-area orbit section or a finite-coordinate
coherence mechanism that does not telescope through an unbounded stabilizer.

Establishing this claim kills `z` by
`infinite-chromatic-commutator-code-kills-mf-mark`; the direct root-saturation
theorem then gives full MF collapse of `Delta`.

## Attempts

* **Two-transitive lamp addresses.**  Same-site and different-site
  commutators give the desired diagonal/off-diagonal table at the group level,
  but different representatives of one address differ by an arbitrary point
  stabilizer element.  Generator-wise lamp covariance then costs the
  stabilizer word length; see
  `stabilizer-generator-control-has-unbounded-address-loss`.
* **Three-transitive addresses.**  Fixing one more point only replaces the
  point stabilizer by a two-point stabilizer.  The same unbounded section
  cocycle remains unless that stabilizer is finite or uniformly exactified.
* **Literal Leavitt prefixes.**  Prefix-free words provide arbitrarily many
  exact orthogonal Heisenberg pairs, but their pair relations occur at
  unbounded presentation area.  This is exact Clifford growth, not a bounded
  compiler.
* **Two-address shift-graph fold.**
  `binary-leavitt-shift-graph-has-exact-marked-commutator-table` improves the
  complete prefix table substantially.  On the shift-graph vertex `(i,j)` it
  uses `c_(i,j)=x_12(T_j)` and
  `h_(i,j)=x_23(S_i+S_j)`.  The diagonal product is exactly the prescribed
  corner mark, while `(i,j)->(j,k)` is zero because `T_k` kills both source
  addresses.  The finite shift graphs have chromatic number at least
  `ceil(log_2 M)`, so their disjoint union is an exact infinite-chromatic
  marked table with canonical vertex words and no diagonal conjugators.  The
  remaining question is sharply reduced to uniform filling area for these
  pair and triple identities.  Pair-dependent prefix-code normalization does
  not by itself pay that area, but unlike the complete table the compiler now
  needs coherence only on the shift incidence pattern.
* **Cumulative-row complete-graph fold.**
  `binary-leavitt-cumulative-complete-graph-table` removes
  the pair-indexed vertex charts altogether.  With orthogonal corner pairs
  `A_rB_s=delta_(rs)q`, use
  `C_j=A_0+...+A_j` and `H_j=B_j+B_(j+1)`.  Then `C_jH_j=q`, while
  `C_kH_j=0` for every `j!=k` (later rows see `q+q`; earlier rows see zero).
  The resulting one-indexed canonical words realize every finite complete
  graph, with the prescribed mark on the diagonal and no diagonal
  conjugator.  The cumulative rows and adjacent columns are one pair of dual
  triangular bases, so a single finite-chart basis change normalizes the
  whole table simultaneously.  This strictly sharpens the live wordization
  gate: it is enough to give a uniform-area global triangular basis fold.
  Pair-dependent endpoint sections are no longer part of the proposed
  compiler.  What remains unproved is whether the growing triangular basis
  change can be folded by a fixed number of presentation cells; ordinary
  elementary-row telescoping costs `M` and is not sufficient.
* **The coefficient table has only two stabilized unit orbits.**
  `dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits` proves that
  one prefix-code unit simultaneously takes `(t_alpha,s_beta)` to
  `(t_0,s_0)` or `(t_0,s_1)`, according only to whether `alpha=beta`.  Thus
  long coefficient cancellation is not an algebraic obstruction.  The unit,
  however, depends on the ordered pair.  Replacing the fixed vertex words by
  that pair-dependent chart separately on each edge destroys the compactness
  coloring.  The live gate is to wordize the two simultaneous orbits while
  choosing each `c_alpha,h_alpha` only once and paying bounded area.
* **Finite literal conjugacy prototypes in a residually finite actor.**
  `rf-conjugacy-difference-graphs-finitely-colorable`
  supplies one finite quotient coloring, so this template cannot even produce
  the required infinite-chromatic graph.  Bounded-area consequences must use
  more than finitely many pure conjugacy differences, or the address actor
  must escape that residual-finiteness argument.

The next viable attack must construct a bounded-area orbit section directly,
or replace representative coherence by a finite-coordinate selector whose
error does not telescope with address length.
