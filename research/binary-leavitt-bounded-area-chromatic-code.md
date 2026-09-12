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
  The uniform-area upgrade is now refuted for these words.  Freezing
  `h_(0,1)` leaves all outgoing `c_(1,k)` in infinitely many distinct cosets
  of one fixed involution's centralizer, so
  `leavitt-chromatic-tables-have-area-divergence`
  forces their edge areas to diverge.
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
  whole table simultaneously.  This exact reduction does not admit the
  required area upgrade: freeze `H_0` and all later cumulative rows give
  distinct centralizer cosets with zero exact commutator.
  `leavitt-chromatic-tables-have-area-divergence`
  therefore forces their filling areas to diverge.  No self-similar
  wordization of these same vertex words can make the area uniform.
* **Canonical stabilized Morita tree.**
  `binary-leavitt-canonical-morita-tree-reduction` gives a second, sharper
  complete-graph reduction.  Let the fixed inner Morita branch words
  `D_0,D_1` name `c_u=D_ucD_u^(-1)` and `h_u=D_uhD_u^(-1)` for every binary
  word `u`.  Diagonal discrepancies are literal conjugates of one base cell.
  For two distinct equal-depth words, their longest common branch prefix
  strips by free conjugation; at the first unequal bits `i!=j`, all remaining
  tails occur only as coefficient contexts in
  `r_a(t_i s_j)s_b=0`.  Consequently one uniform first-mismatch estimate
  would realize `K_(2^n)` at every depth without a pair-dependent section.
  The exact context vanishing follows from
  `atlas-steinberg-context-absorption`, and its nested zero word has constant
  area.  This route is now refuted, not live.  The asynchronous strengthening
  fails by `unsynchronized-first-mismatch-area-is-centralizer-impossible`,
  and the exact equal-level estimate fails by
  `level-synchronous-first-mismatch-area-is-centralizer-impossible`: freeze
  one column per level, conjugate its `h`-word to the base involution, and the
  exponentially many row words violate properness of finite-mark centralizer
  area.  Thus the qualitative context-absorption comparison necessarily has
  unbounded area on the canonical tree.
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
* **Put each finite shift graph in a fresh Leavitt cylinder.**  This removes
  the literally persistent column used by
  `leavitt-chromatic-tables-have-area-divergence`, but it does not remove the
  obstruction if all block columns are uniformly conjugate to one prototype.
  Unbounded chromatic number forces unbounded degree; normalizing one
  high-degree column then produces arbitrarily many bounded-area centralizer
  cosets inside that single block.  This is
  `one-column-orbit-codes-have-bounded-chromatic-number`.
  A block construction must therefore vary the normalized column type or
  make many neighbors coincide modulo its cyclic subgroup.
* **Replace the root column by finitely many mixed/opposite-root cells.**
  This does not by itself escape centralizer area.  The theorem
  `finite-prototype-column-codes-force-coset-collisions` allows any finite
  list of nontrivial finite-order column prototypes.  If the normalized
  neighbour rows remain distinct elementary-root coefficients, their cyclic
  coset fibres are uniformly bounded (usually injective), and the theorem
  bounds the chromatic number.  Hence a fixed-cell two-branch construction
  must do more than change the column's root type: it must create unbounded
  normalized-row collisions, or use infinitely many genuinely different
  column types.  The former is a concrete new design target; the latter must
  still keep `(CCC1)--(CCC2)` at uniform presentation area.
* **Private third-address tagged shift table.**
  `binary-leavitt-tagged-shift-table-has-centralizer-collisions` supplies
  genuinely different vertex data.  At `(i,j)` it uses the row `A_i` and
  column `B_i+D_(ij)`, where `D_(ij)` is a private orthogonal prefix column.
  The diagonal is marked, while every outgoing target `(j,k)` has the same
  row `A_j` and commutes with that column.  Thus normalized-row fibres are
  unbounded and no literal column persists across distinct row values; the
  existing cumulative/tree centralizer arguments do not apply.  The new
  bottleneck is multi-predecessor word coherence: one row `A_j` must compare
  at bounded area with all edgewise three-address charts that contain it.
  A pair-dependent simultaneous prefix unit proves each exact identity but
  does not yet give the one-word-per-vertex requirement of `(CCC2)`.
* **Normalize the tagged cell inside the source-row stabilizer.**
  `tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy` rules
  out this coherence shortcut.  A private tag can make one transporter fix
  `A_i` while normalizing `A_j` and `B_i+D_(ij)` as group elements.  To make
  both commutator discrepancies literal conjugates of fixed prototypes,
  however, both row occurrences must agree at bounded area with their one
  canonical vertex words.  Those comparisons are commutators with endpoint
  holonomies centralizing nontrivial order-two roots.  Finite-mark
  centralizer-area properness and the two-role counting identity then force
  bounded successor fibres, contrary to the growing shift packets.  This
  refutes the stabilizer compiler, not the possibility of a non-chart edge
  diagram for the tagged table.
* **Cancel two marked diagonals with a coefficient shear.**  Put
  `u_(ij)=1+B_iA_j`.  It fixes the tagged column and the target row and sends
  the source row to the source-plus-target row.  The group identity
  `[b,h]=a^(-1)delta_1delta_0^(-1)a`, for
  `delta_0=[a,h]z^(-1)` and `delta_1=[ab,h]z^(-1)`, would pay every edge by
  two marked diagonal cells.  The algebra is exact, but
  `tagged-shift-shear-has-unbounded-fixed-mark-area` shows
  that conjugating the first cell into the second is not uniform: the shear
  lifts form infinitely many cosets in the centralizer of the fixed mark,
  so their mark-preservation areas diverge.  Only a direct sheared-diagonal
  diagram avoiding that conjugacy comparison could still use `(TSC5)`.
* **Fill the sheared diagonal directly from one fixed Gram prototype.**
  `tagged-sheared-diagonal-one-chart-hits-mark-area` rules out this attempt
  even without the coefficient shear.  A single transporter can normalize
  the row `A_i+A_j` and tagged column `B_i+D_(ij)` algebraically, but outer
  conjugation changes the terminal prototype mark to `g_(ij)zg_(ij)^(-1)`.
  Making the boundary use the literal common `z` requires a bounded
  `[g_(ij),z]` filling.  Distinct sheared rows put these transporters in
  infinitely many cosets of the fixed mark centralizer, so properness makes
  that return area unbounded.  This leaves only a genuinely multi-chart
  diagram in which internal mark seams cancel collectively, rather than one
  outer-conjugacy cell.
* **Cancel the mark internally across a bounded chart complex.**  Ordinary
  two- and three-chart gluings are still fenced when their conjugated marks
  cancel pairwise.  `bounded-tagged-mark-seam-complex-has-finite-row-range`
  roots the seam graph at the one outer literal `z`; bounded graph size and
  bounded seam area put every chart conjugator in one finite commutator-area
  sublevel of `C_Delta(z)/<z>`.  A bounded word in a finite row palette then
  has only finitely many values, whereas the sheared rows
  `x_12(A_i+A_j)` are infinite.  Thus the next multi-chart attempt must use
  a genuinely ternary-or-higher mark relation, growing chart count, or a
  direct diagram with no distinguished pairwise mark seams.
* **Use one genuinely non-pairwise fixed-arity mark fusion.**
  `fixed-arity-mark-fusion-has-finite-character-model` fences the bare
  higher-arity product relation without refining it into pairwise seams.  On
  `l^2(F_2^r)`, `r` distinct conjugate half-negative signs multiply to one
  further conjugate half-negative sign, and fixed marked Pauli payloads can
  be carried with them.  Thus arity at least three alone is insufficient;
  the fusion cell must read noncommuting address-dependent payload incidence.
* **Let the number of charts grow with the edge addresses.**  This cannot be
  an independent escape under the uniform-area conclusion being sought.
  By `uniform-area-bounds-essential-chart-count`, an area-`B` diagram has at
  most `B` relator-bearing chart instances.  Additional zero-cell charts are
  only free conjugating trees and supply no new fusion equation.  Growing
  boundary paths remain possible, but must be handled as a direct-diagram
  problem rather than as growing positive-area chart count.
* **Use one direct noncommuting `A_3` associator cell.**  For the private
  tagged column `C_(ij)=B_i+D_(ij)`, the nested word
  `N(a,C)=[x_12(a),[x_23(1),x_34(C)]]` equals `x_14(aC)` by either
  bracketing.  It is marked for `a=A_i+A_j` and trivial for `a=A_j`, so it
  reads the address-dependent payload with no conjugated-mark seams at all.
  `tagged-a3-associator-cell-has-finite-positive-root-model` fences it:
  the whole diagram remains in `U_4^+(R)`, and every finite address menu has
  an exact finite regular model with the long-root mark nontrivial.  A live
  direct cell must therefore contain a payload-attached opposite-root or
  Weyl occurrence, not only noncommuting positive-root associativity.
* **Attach the opposite long root to the associator output.**  The partial
  Whitehead `W_q=x_14(q)x_41(q)x_14(q)` is the shortest genuine
  opposite-root word containing the payload-produced mark.  It still reads
  the payload too late.  `marked-a3-output-whitehead-has-finite-gl4-model`
  specializes the tagged diagonal arm to `x_12(1)` and the edge arm to one
  inside `GL_4(F_2)`; both associator bracketings, the edge zero, the
  Whitehead factorization and its root swap are exact while `x_14(1)` stays
  nontrivial.  The next opposite-root cell must contain an individual
  private coefficient arm before the product collapses to `q`.
* **Put the private column into the opposite-root word before multiplication.**
  Use `P=W_14(A_i+A_j,B_i+D_(ij))` for the sheared diagonal and
  `R=W_14(A_j,B_i+D_(ij))` for the edge.  This shares the literal private
  column, and neither `A_j` nor the tag can be specialized to zero in the
  tested table.  `private-arm-opposite-cell-has-finite-m3-model` still gives
  an exact escape: explicit nonzero matrix units in `M_3(F_2)` satisfy all
  tagged products, the two A3 outputs, and both Whitehead words; `P,R`
  generate an `S_3` packet while `x_14(q)` remains nontrivial.  The next
  cell must invoke a full binary completeness relation unavailable in finite
  unital coefficient rings, not only one shared private arm.
* **Couple both binary branches and completeness into that same packet.**
  This finally kills all exact finite-dimensional coefficient-ring
  specializations: `t_0s_0=1` makes `s_0` a unit in finite dimension, while
  `t_0s_1=0` and `t_1s_1=1` then contradict each other.  It still does not
  kill finite group-occurrence models.  By
  `full-completeness-opposite-menu-has-finite-gl5-fusion`, three copies of a
  finite `GL_5(F_2)` payload/opposite packet, permuted by `S_3`, carry every
  individual arm and satisfy `C_0C_1=J` while the common mark remains
  nontrivial.  The unresolved row must force these three chart copies onto
  one coefficient/multiplicity reservoir; coefficient direct-finiteness is
  not itself that same-corner decoder.
* **Compose the full fold through the same two branch arms.**  Add both
  right-compositions by `s_j`, then both left-compositions by `t_i`, so the
  matching loops return `A` and the crossed loops return zero.  This does
  break the three-character specialization, but
  `full-fold-compose-return-has-finite-affine-model` gives a finite
  four-bit replacement.  Two extra label coordinates `R_0,R_1` record the
  intermediate arms, and four literal transvections satisfy the entire
  matching/crossed table while the parent mark stays nonzero.  Hence even
  the composable fold remains an occurrence-label identity unless another
  row forces those labels to act as coefficient multiplication on one
  matrix reservoir.
* **Factor the authenticated intermediate transport as the actual partial
  Whitehead.**  Require `W=UVU`, with `U` transported to the shared `S`
  occurrence and `V` transported to the final `T` occurrence.  This puts
  both coefficient-labelled factors, the intermediate root, and the final
  return in one bounded occurrence table.  It is still fenced by
  `partial-whitehead-fold-return-has-finite-s6-model`: the prior `S_6`
  packet already contains such `U,V` and two exact root-position
  conjugators while its mark remains nontrivial.  The unresolved literal
  row must therefore constrain those conjugators through their prescribed
  native mixed squares, not merely assert the two occurrence conjugacies.

The next viable attack must construct a bounded-area orbit section directly,
replace representative coherence by a finite-coordinate selector whose
error does not telescope with address length, or realize the unbounded
cyclic-coset collisions forced by the finite-prototype theorem.
