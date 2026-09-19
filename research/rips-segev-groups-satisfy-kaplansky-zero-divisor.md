---
rg: 2
id: rips-segev-groups-satisfy-kaplansky-zero-divisor
kind: claim
title: The Rips--Segev torsion-free groups without unique products satisfy Kaplansky's zero-divisor conjecture
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the conjecture for every torsion-free group; this is Steenbock's question for the Rips--Segev groups, the first torsion-free groups without unique products.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that is the open support-three case over torsion-free hosts with cyclic centralizers, a class containing these groups; this asks for every support size, for this family only.
  marked-limits-of-special-groups-have-domain-group-rings: that is a sufficient criterion for the domain property; this is the instance of the conjecture that the criterion is aimed at.
---

**OPEN.** For every field `k` and every Rips--Segev torsion-free group `G`
without the unique product property, `k[G]` has no zero divisors.

**Source of the question.** Steenbock, arXiv:1307.0981, introduction,
verbatim: "Do Rips-Segev groups satisfy Kaplansky's zero-divisor conjecture?".
It is repeated as a problem in Arzhantseva--Steenbock, arXiv:1407.2441: "Do the
Rips-Segev groups without the unique product property satisfy the Kaplansky
zero-divisor conjecture?". Martin--Steenbock, arXiv:1409.3678, "Open problem":
"It is unknown whether these so called generalised Rips-Segev groups satisfy
the Kaplansky zero-divisor conjecture."

**Related nodes on main.**
- The support-three case for torsion-free hosts with cyclic centralizers, which
  include these torsion-free hyperbolic groups, is the OPEN
  `cyclic-centralizer-groups-have-no-support-three-zero-divisors`. Main has
  local constraints there (short cycles, quasimorphism bounds), not a proof.
- `zero-divisor-support-subgroup-host-constraints` applies.

## Attempts

1. **Cubulation (route `rips-segev-zero-divisor-via-cubulation`).** Needs the
   OPEN `rips-segev-groups-are-cocompactly-cubulated`. Martin--Steenbock's
   combination theorem covers only the classical `C'(1/6)` condition over free
   products. Steenbock (arXiv:1307.0981, introduction) notes that
   Rips--Segev relators "can have long common parts", so the classical theorem
   does not apply as stated. For the Kazhdan generalized examples of
   arXiv:1407.2441 this route is closed: those are infinite property (T)
   groups, hence not CAT(0)-cubical.
2. **Special marked limits (route `rips-segev-zero-divisor-via-special-marked-limits`).**
   Needs the OPEN `rips-segev-groups-are-marked-limits-of-special-groups`. It
   avoids cubulating the group itself. By
   `kazhdan-groups-map-trivially-to-torsion-free-special-groups` it cannot
   reach the Kazhdan generalized examples, so it is only a candidate for the
   original Rips--Segev presentations, which are not known to have property
   (T).
3. **Zero divisor on the encoded witness (killed; `rips-segev-witness-pairs-carry-no-zero-divisors`).**
   The natural candidate supports are Steenbock's non-unique-product pair
   `(A, {1,a,b,ab})`.
   - Over `F_2` they carry no zero-divisor pair in any torsion-free group,
     because `beta = (1+a)(1+b)` is a product of non-zero-divisors.
   - Over any field they carry none once one interior `a`-line index is free
     of the Step 1--2 gluings, assuming exact encoding (EE).
   - A counterexample in `k[G(Gamma)]` must use other supports, saturate every
     clean square with extra coincidences, or break (EE).
4. **Every support inside the witness (killed; `rips-segev-witness-supports-carry-no-zero-divisors`).**
   For small-cancellation graphs (`Gr'_*(1/8)`) with at most one pair of
   distinguished positions at distance one, this includes Steenbock's explicit
   families.
   - (EE) holds: a hanging `v b` is never a vertex of `Gamma`, by a van Kampen
     argument.
   - Every pair with `supp alpha` inside `A` and `supp beta` inside
     `{1,a,b,ab}` has `alpha beta != 0`, over any field.
   - A counterexample must put `alpha` or `beta` outside the witness.
5. **Support reduction to the witness (obstruction; `rips-segev-groups-embed-every-torsion-free-group`).**
   The relators read only `a` and `b`.  So the group over `G_1 * G_2` is the
   amalgam `G_1 *_{<a>} K_Gamma *_{<b>} G_2`, where `K_Gamma` is the core group
   over `<a> * <b>`.
   - Every finitely generated torsion-free `H` embeds in `H *_{<a>} K_Gamma`,
     which is a torsion-free generalized Rips--Segev group without unique
     products.  It is hyperbolic when `H` is.
   - For the generalized groups, with arbitrary torsion-free factors, this
     question is equivalent to the full conjecture.  One finitely presented
     generalized group `U *_{<a>} K_Gamma` tests it.
   - A support-reduction lemma that is uniform in the factors is equivalent to
     the conjecture.  It fails at supports in one coset pair `(gH, Hh)`, whose
     coincidences have faceless van Kampen diagrams.
   - What remains is the core groups `K_Gamma` over `F_2`, which is Steenbock's
     original question.  The domain-factor case follows from that together with
     a domain-combination theorem over cyclic amalgams.
6. **Two-layer elements in the core (partial; `rips-segev-core-large-gap-two-layer-elements-are-regular`, obstruction `rips-segev-port-data-cannot-exclude-balanced-divisors`).**
   Take `beta = u + w b` with `u, w` in `k[<a>]`.  A zero product gives a
   finite configuration of `<a>`-cosets with in- and out-ports.  Walking along
   the extreme ports gives a positive relation `b a^{n_1} ... b a^{n_L} = 1`
   whose exponents all lie on one side of the degree offset
   `deg_+ w - deg_+ u` (or `deg_- w - deg_- u`).
   - A small-cancellation count shows that every positive relation has an
     exponent in the difference set `Delta` of the relator exponents.
   - So `beta` is regular in `k[K_Gamma]`, and in every generalized
     Rips--Segev group, when an offset lies outside `[min Delta, max Delta]`.
   - Port data alone cannot go further.  The graph `Gamma` itself gives a
     port configuration with offsets `(0,0)`, which covers the witness
     `{1,a,b,ab}`.  For Steenbock's graphs, its relator cycles give positive
     relations with all exponents `<= -10` and with all exponents `>= 99900`.
     So the walk step fails for offsets in `[-10, 99900]`.
   - What remains is the balanced and intermediate range.  It needs the
     coefficients themselves, not supports or extreme degrees.  The
     extremal-coset route of this lane is dead there.
7. **Coefficients on the witness support (reduction; `rips-segev-witness-divisors-need-saturated-supports`, obstruction `rips-segev-cores-have-no-infinite-cyclic-quotient`).**
   Take `beta = c_0 + c_1 a + c_2 b + c_3 ab` with `D = c_0 c_3 - c_1 c_2`.
   - If `D = 0` then `beta` factors as `(x_0 + x_1 a)(y_0 + y_1 b)` and is
     regular, for every coefficient pattern.
   - If `D != 0`, an annihilator has a *saturated* support: no product of
     `X · supp beta` is unique, and every pair `h, h a` in `X` has a triple
     product at `h a` or at `h a b`.
   - So witness-support regularity follows from a coefficient-free statement:
     `K` has no finite saturated set.
   - Ports together with top and bottom coefficients cannot decide it, because
     `Gamma` realizes arbitrary extreme scalars with no coincidence equations.
     The realizing support `A` is not saturated.
   - Gradings are dead.  Relator cycles give positive relations of both
     exponent signs, so `Hom(K, Q) = 0` and `H_1(K)` is finite, and `K` has no
     locally indicable quotient.  Any nontrivial unique-product quotient would
     still settle `{1,a,b,ab}` completely, but none is known.
   - Next: decide whether a finite saturated set exists, by a van Kampen
     argument at the top pair of a maximal `a`-run.
8. **Witness support settled; short-span two-layer elements (proposed established; `rips-segev-short-syllable-two-layer-elements-are-regular`).**
   - If `alpha (u(x) + w(x) y) = 0` with `u, w` independent of span `d`, then
     every point of `supp(alpha u) ∪ supp(alpha w)` has a `y^{±1}`-neighbour
     and an `x^n`-neighbour with `1 <= |n| <= d`.  An isolated point would
     make `u` and `w` proportional.
   - Alternating the two steps closes a relation `prod x^{n_k} y^{±1} = 1`.
     Small cancellation forbids `prod a^{n_k} b^{e_k} = 1` with every
     `|n_k|` below the least gap `m_Gamma` between distinguished positions of
     a line (`m_Gamma >= 10` for Steenbock's graphs).
   - So for `m_Gamma >= 2` every nonzero element supported on `{1,a,b,ab}` is a
     non-zero-divisor in `k[K]` and `k[G(Gamma)]`, and so is all of
     `k[<b>] + a k[<b>]`.  Also `u(a) + w(a) b` is regular when the reduced span
     is `< m_Gamma`, including the balanced box of attempt 6.  This bypasses
     the saturated-set question of attempt 7 without deciding it.
   - For Steenbock's graphs `K` has no nontrivial left-orderable quotient.
     The two positive relations of opposite sign kill every sign choice.
   - Next: a three-layer neighbour lemma for `u + w b + z b^2`.  Lemma 5 of
     the route already allows arbitrary `b`-exponents.  Two-layer elements
     with span `>= m_Gamma` and balanced offsets also remain.
9. **Any number of b-layers, sparse a-supports (proposed established; `rips-segev-sparse-a-support-elements-are-regular`).**
   - Let `beta = sum c_ij a^i b^j` with `a`-exponents in `S` and any
     `b`-exponents.  If `alpha beta = 0` and the coefficient matrix has rank
     `>= 2`, then every point of `union_j supp(alpha u_j(a))` has a
     `b^e`-neighbour (the layers must cancel) and an `a^n`-neighbour with
     `n in S - S`, `n != 0`.  Rank one factors.
   - The walk reads a relation whose `a`-syllables lie in `S - S`.  The proof
     of Lemma 5 of attempt 8 gives one syllable that is a difference of two
     distinguished positions of a line.  Right annihilators follow by `*`
     with `a` and `b` exchanged.
   - So `beta` is a non-zero-divisor whenever `S - S` misses `Dist(Gamma)`.
     This covers every short-span element with three or more layers.  For
     Steenbock's graphs it covers every `S` whose elements are pairwise
     incongruent mod 10, of any span, including balanced two-layer elements
     beyond `m_Gamma`.
   - Next: `S - S` meeting `Dist(Gamma)`, e.g. `1 + a^{10} + b`.  Use the long
     exterior arc (many consecutive flanked blocks in `(S - S) ∩ Dist`) or
     the coefficients along the walk.
10. **Few-line a-supports in Steenbock's graphs (proposed established; `rips-segev-steenbock-few-line-a-supports-are-regular`).**
   - Steenbock's explicit gluing (arXiv:1307.0981) is reconstructed there.
     The `b`-edges are in bijection with the edges of a girth-`> 41`
     covering `Phi` of the bouquet of four circles.  Every vertex has at most
     one `b`-edge in and one out, and `b`-runs have at most 2 edges.
   - Both inputs of the chain-criterion example of attempt 9 hold.
     `gamma >= girth(Phi) >= 42`, and `v_{1,0} -> v_{1,10}` would be a loop of
     `Phi`.  So `1 + a^{10} + b` and every two-layer element of span
     `<= 89` are regular.
   - Stronger: a backtrack-free path projects to a non-backtracking walk in
     `Phi`.  So the `q(42) = 11` hops of a chain lie on pairwise distinct
     lines of `L_S = {i : (S - S) ∩ Dist_i != ∅}`.
   - Hence `beta in k[a^S <b>]` is regular whenever `|L_S| <= 10`, for any
     number of layers.  In particular this holds for every `a`-span
     `< 10^{51}`.
   - Next: `|L_S| >= 11`, e.g. contiguous `S` of span `>= 10^{51}`.  Chains
     through 11 distinct lines exist, so the coefficients of `alpha beta = 0`
     must be tracked along the walk.
11. **Eleven-point a-supports in Steenbock's graphs (proposed established; `rips-segev-steenbock-eleven-point-a-supports-are-regular`).**
   - Steenbock's rows are super-increasing: `min Dist_r^+ = 10^{5r-4}`
     exceeds the sum of all larger elements of lower rows.
   - So one pair of `S` per line of `L_S` gives a forest on `S`.  A cycle
     would be a signed sum of distinct-row differences equal to zero.  Hence
     `|L_S| <= |S| - 1` for every finite `S`.
   - With attempt 10: every `beta in k[a^S <b>]` (or `k[<b> a^S]`) with
     `|S| <= 11` is regular, whatever the spread of `S`, for any number of
     layers and any field.
   - A zero divisor of this shape therefore needs at least 12 distinct
     `a`-exponents and `a`-span `>= 10^{51}`.
   - The support method stops at some `S` with `|S| <= q(gamma) + 1 <= 25`
     (12 if `gamma = 42`).  A shortest relator cycle gives a chain there, so
     the coefficients must enter beyond it.
12. **Support-method threshold is exactly q(gamma) (proposed established; `rips-segev-support-method-threshold-is-exactly-q-gamma`).**
   - In an `(N_S, N_J)`-chain of length `q(gamma)` the hop lines are
     pairwise distinct.  A repeated hop line closes the segment between the
     two hops into a cycle of free-product length `<= 2(q - 1) < gamma`.
     No girth or looplessness hypothesis on `Phi` is used.
   - So `|L_S| < q(gamma)` gives regularity, and for Steenbock's graphs every
     `beta in k[a^S <b>]` with `|S| <= q(gamma)` is regular.  The previous
     silent support has `|S| = q(gamma) + 1`, so the `12..q(gamma)` gap is
     closed.
   - `gamma` depends on `Phi`: `g <= gamma <= 2g`.  `gamma = 42` is realized
     by the Cayley graph of a finite quotient of `<x | (x_4 x_1)^{21}>`
     (Newman spelling theorem, Wise residual finiteness).  For that `Phi`,
     12-point supports sit exactly at the threshold.
13. **One-copy configurations carry no zero divisors (proposed established; `rips-segev-one-copy-configurations-carry-no-zero-divisors`).**
   - This is the coefficient contradiction on the `Gamma`-local configuration,
     for every support, including the silent 12-point `S`.
   - Suppose `alpha (u(a) + w(a) b) = 0` with `alpha, w != 0`.  Then
     `alpha u` and `alpha w` cannot both lie in one translate of `g(V(Gamma))`.
   - Proof.  Exact encoding (the witness node's Lemma 1, extended to
     `a`-corrections) gives line ports `P_i = f_i u` in `In_i` and
     `Q_i = f_i w` in `Out_i`, matched along `b`-edges.
     `P_i Q_j = P_j Q_i` and row separation force
     `supp P_i = supp Q_i ⊆ {0, C_i}`.  The `x_1`/`x_2` edges leaving `0`
     and `C` then hit ports `I_1`/`I_2`, which is absurd.
   - This answers the port-data obstruction: the balanced configuration
     `Gamma` has no coefficients.  A control with all lines in one row does
     have solutions, so row separation is essential.
   - Next: relations spread over two or more translates of `g(V)` glued
     along pieces, which is van Kampen-type coset configurations.
14. **Two-copy configurations carry no zero divisors (proposed established; `rips-segev-two-copy-configurations-carry-no-zero-divisors`).**
   - Suppose `alpha (u(a) + w(a) b) = 0` with `alpha, w != 0`.  Then
     `alpha u` and `alpha w` cannot both lie in the union of two translates
     of `g(V(Gamma))`, over any field, in `k[K]` and in `k[G]`.
   - Gluing lemma.  Between two links of two copies the van Kampen diagram
     has no faces, since each face would have boundary `< 8 < gamma`.  So two
     copies meet in one `b`-bridge only, or in at most three `<a>`-cosets
     that are pairwise joined by shared `b`-runs (rigidity plus
     `girth(Phi) > 12`).
   - Ports.  On clean cosets the one-copy port constraints hold verbatim.
     Two clean active lines in one copy have dirty, distinct flanking lines
     meeting the same other copy, which the gluing lemma forbids.  So at most
     `2 + 3` cosets are active.
   - Their port graph closes a positive relation `b a^{n_0} ... b a^{n_{L-1}}`
     with `L <= 5`, which is too short to hold in `K`.
   - Exhaustive `F_2`/`F_3` port searches on two-copy models with separated
     rows found no solution for any gluing.  A single-row control does have
     solutions.
   - Three copies reduce to one gap, *mixed flanks*: the two flanking lines of
     a clean line are dirty through different copies.  Excluding them leaves
     `<= 12` active cosets, and `24 < 5 gamma/8 - 1` still closes the proof.
     For `N >= 4` copies the count exceeds 12.  Since the copies cover `K`,
     the `N`-copy theorem for all `N` is the whole `b`-degree-one case.
   - Next: a mixed-flank lemma for three copies, then a Greendlinger-type
     bound on the number of copies a short port cycle can cross, for general `N`.
15. **Three-copy configurations carry no zero divisors (proposed established; `rips-segev-three-copy-configurations-carry-no-zero-divisors`).**
   - *Rank-one lemma.*  Suppose two active cosets have port supports whose
     difference sets meet only in `0`.  Then `P_T Q_T' = P_T' Q_T` holds
     coefficientwise, so `P_T` is a scalar multiple of `Q_T` and `u = c w`.
     Then `(alpha w)(c + b) = 0`, which is impossible.  This holds over any
     field and in any group.
   - So two clean active cosets on different lines are contradictory,
     whatever the number of copies.  Each copy has at most one clean active
     coset, and the mixed-flank lemma of item 14 is not needed.
   - Three copies then have at most `3 + 9` active cosets.  Their port cycle
     is a positive relation of length `<= 24 < 5 gamma/8 - 1`, which is
     impossible.  This settles three copies, in `k[K]` and in `k[G]`.
   - For `N` copies it holds whenever `3N^2 - N <= 5 gamma/8 - 1`.
   - *Shell lemma (toward `N >= 4`).*  Every port cycle has a Greendlinger
     shell in some copy `C_M`.  The shell arc crosses 11 distinct active
     cosets on distinct lines of `C_M`, and at most one of them is pure (rank
     one again).  Each impure one links `C_M` to another covering copy, at
     most 3 per copy.  So at least 4 covering copies differ from `C_M`.
   - For `N = 4` this forces every shell copy outside the covering, with all
     11 arc cosets dirty.  For girth `g` it covers `N` up to about `5g/48`,
     linear in the girth.
   - Next: an extremal-copy lemma (some copy of a minimal covering meets the
     others in `<= 3` links) and a rank-one removal of that copy, which would
     give induction on `N`.  Counting alone cannot handle every `N`.
16. **Six-copy configurations carry no zero divisors (proposed established; `rips-segev-six-copy-configurations-carry-no-zero-divisors`).**
   - Walk the Greendlinger shell arc of item 15 coset by coset.  It has 12
     consecutive `b`-syllables, `e_2` of them `b^2`, so it visits `13 + e_2`
     pairwise distinct active cosets.
   - *Two-or-a-syllable lemma.*  A copy other than the shell copy meets at
     most two arc cosets, or three forming one `b^2`-syllable.  Otherwise a
     shared `b`-run and the arc close a cycle of length `<= 26 < 42` in `Phi`.
   - Shell copy outside the covering: `13 + e_2 <= 2N + e_2`.  Inside: `12 +
     e_2 <= 2(N - 1) + e_2`.  Both fail for `N <= 6`.  This closes the `N = 4`
     residue of item 15 and also `N = 5, 6`, in `k[K]` and `k[G]`.  At girth
     `g` it covers `2N <= ~5g/16`.
   - *Three-port lemma.*  In a counterexample each clean active coset has
     `>= 3` port edges, all to dirty cosets.
   - Exact `N = 7` residue: the shell copy is in the covering, exactly one arc
     coset is pure, and the other six copies see disjoint arc sets.
17. **Extremal-copy lemma on supports alone (killed; `rips-segev-coefficient-free-extremal-copy-lemma-fails`).**
   - The step proposed in item 15 ("some copy meets the others in `<= t`
     links") is false as a support statement, even for port-closed supports,
     for every `t <= 8`.
   - Star family: every copy whose chosen line lies in one long `a`-interval.
     Each copy meets the others in 9 cosets, and far lines stay private, so
     the covering is minimal.
   - The family has many clean active cosets per copy, so the coefficients
     kill it.  Next: the coefficient-compatible version.  If every copy has
     at most one clean active coset (with `>= 3` dirty port neighbours), then
     some copy of a minimal covering has at most two dirty cosets.  With the
     rank-one lemma this gives induction on `N`.
18. **Eight-copy configurations carry no zero divisors (proposed established; `rips-segev-eight-copy-configurations-carry-no-zero-divisors`).**
   - This closes the `N = 7` residue of item 16, and `N = 8`, in `k[K]` and
     `k[G]`.
   - Size the shell window by the shell face's own syllable length `l`, not by
     `gamma`, and count partial end syllables.
   - Bound the arc cosets seen by `N` copies by `2N + min(N, e_2)`.
   - The girth of `Phi` forces a face of length `l` to have at most `l - 42`
     single-`b` syllables, so it is all `b^2` at `l = 42`.
   - Criterion: `n* + max(0, e* - N) >= 2N` for some window with `<= 39`
     `b`-edges.  It holds at `N = 8` for every `l`.
   - Exact `N = 9` residue: shell face of length `42..54` in a diagram with at
     least three faces.
   - The window count cannot pass about `N = 12`.  The extremal-copy step of
     item 17 (coefficient-aware) is still the route to every `N`.  It was not
     proved in this pass.

19. **Nine-copy configurations carry no zero divisors (proposed established; `rips-segev-nine-copy-configurations-carry-no-zero-divisors`).**
   - This closes the exact `N = 9` residue of item 18, in `k[K]` and `k[G]`.
   - Use the whole curvature budget of the port-cycle disc, not one
     Greendlinger face.  The disc has simple boundary with exactly `L`
     `b`-edges.  Gauss–Bonnet under `C'(1/8)` gives `sum (4 - i) >= 6` over
     the shells, where `i` is a shell's number of interior arcs.
   - A shell with `i <= 2` has an arc of `> 3l/4` syllables.  A window in it
     meets the item-18 criterion at `N = 9` for every `l`.  The same holds
     for `i = 3` and `l >= 56`.
   - Otherwise there are at least six three-arc shells of length `42..54`.
     Each carries at least 21 `b`-edges, because girth forces them to be
     mostly `b^2`.  So `L >= 126 > 117 = N + 3N(N-1)/2`, which bounds the
     active cosets.
   - This does not reach `N = 10`.  The surviving shells carry about `2N`
     `b`-edges against `A(N) ~ 1.5 N^2` cosets.
   - The coefficient-aware extremal-copy step (height-function extremal
     coset plus the rank-one lemma) was attempted and not proved.  It
     remains the route to every `N`.

20. **Port-cycle counting has an N-independent ceiling (obstruction; `rips-segev-port-cycle-counting-has-n-independent-ceiling`).**
   - Kills the plan "a linear active-coset bound `A(N) = O(N)` plus the
     curvature count closes every large `N`".
   - The window criterion of item 18 is capped by girth at `E* <= 39`.  Its
     left side is `E* - min(e*, N) <= 39`, but it must reach `2N`.  So it is
     vacuous for `N >= 20`, and on all-`b^2` faces for `N >= 14`.
   - Then a one-face port-cycle diagram whose boundary is the relator of a
     directed cycle of `Phi` passes every check, with `L = L_0(Phi)`
     `b`-edges.  In the `gamma = 42` graph of item 12, `(x_4 x_1)^21` gives
     `L = 42`.
   - So the method closes large `N` only with an active-coset bound below
     `L_0`, independent of `N`.  Linear bounds close only a bounded range of
     `N`, and the `~12N` shell figure holds only while windows bite.
   - Next step: a local coefficient lemma for a single shell face.  The port
     equations with fixed `u/w` must fail along `>= 21` consecutive impure
     arc cosets of one copy, whatever the other copies are.  Item 17 shows
     that supports alone cannot give this.

21. **One-copy port equations are always solvable (obstruction; `rips-segev-single-copy-port-equations-are-always-solvable`).**
   - Kills the step of item 20: "the port equations with fixed `u/w`
     cannot hold along `>= 21` consecutive impure arc cosets of one copy".
     As a local statement it is false, for every nonconstant `u/w`, every
     face and every field.
   - Duality: the port map `f -> ((f u)(In_i), (f w)(Out_i))` of a line
     has image `Dep_i^perp`, where `Dep_i` is the set of reflected pairs
     `(A, B)` on `(In_i, Out_i)` with `Ǎ u + B̌ w = 0`.
   - Row separation, applied to the tensor identity `Ǎ_i B̌_j = Ǎ_j B̌_i`,
     leaves at most one line with `Dep != 0`.  So every edge valuation of a
     copy that respects that one line is realized by coefficients `f_i`.
   - Every directed face cycle of `Phi` gets nonzero values at all its
     ports.  This includes `(x_4 x_1)^21` at `gamma = 42`: 42 active arc
     cosets, all `b^2`.  Consecutive arc cosets share one scalar, so there
     is no ratio recursion.
   - Calibration: the regular element `1 + 2a + (3 + a) b` also solves
     every one-copy system.  The contradiction in
     `rips-segev-one-copy-configurations-carry-no-zero-divisors` comes only
     from the support condition.
   - Next step (holonomy form): impose the support condition at the escaped
     points.  That is, `supp(f_T u)` lies in the arrival ports of `T` and
     `supp(f_T w)` in its departure ports, over every copy `T` meets.  Then
     the space `Rep_T` is small, and each coset fixes an exit/entry ratio.
     Show that the product of these ratios around a directed port cycle
     cannot be `±1`.

22. **Port holonomy is tautological and blind over `F_2` (obstruction; `rips-segev-port-holonomy-is-tautological-and-f2-blind`).**
   - Kills the holonomy form of the previous item: impose the escape support
     condition, get `dim Rep_T <= 1`, and show the ratio product around a
     directed port cycle is not `±1`.
   - (A) The edge equation `X(z b) = - Y(z)` telescopes.  For every solution
     and every directed cycle of length `L`, `prod rho_T = (-1)^L`.
   - (B) The support condition is relative to a covering.  One copy per
     active edge always satisfies it.  Adding copies whose line starts at
     chosen points (position `0` is a port of both kinds) makes `Rep_T`
     arbitrarily large.  So `dim Rep_T <= 1` is false in general.
   - (C) Over `F_2` every ratio is `1`.  The `F_2` case is exactly the
     non-existence of a finite `(u, w)`-harmonic family, a support statement.
   - Also: `Lambda` (active cosets, active `b`-edges) is simple and oriented,
     by the short-relation lemma.  A support-minimal counterexample is
     globally rigid (`V = k alpha`), but that does not make any single coset
     rigid.  On the `(x_4 x_1)^21` face, the intrinsic `R_T` is
     2-dimensional with a free ratio on most cosets, and on all 42 over
     `F_10007` (`port_holonomy.py`).
   - Next step: (i) in characteristic `!= 2`, find a directed cycle of
     locally rigid cosets (`dim R_T = 1`) in a copy-minimal covering and show
     that the pattern-forced product is not `(-1)^L`; (ii) over `F_2`,
     exclude harmonic families by support matching, using only simplicity of
     `Lambda` and the rank-one lemma.

23. **Harmonic cycles split over copies (strict reduction; `rips-segev-two-layer-cycles-split-over-copies`).**
   - The previous item asked for two things: exclude `F_2` harmonic families by support matching with simple
     `Lambda` and the rank-one lemma, and find a rigid directed cycle whose forced product is not `(-1)^L`.
     Neither can close as stated.  In `<a, b | (a^m b)^n>`, `sum_j (a^m b)^j (1 - a^m b) = 0` satisfies every
     such hypothesis.  A proof must use row separation or the non-monomial ratio.
   - New object: if `u(1) + w(1) = 0`, then `sum_z Y(z)[z -> z b] + sum_T f_T (u + w)/(t - 1)` is a finite
     1-cycle on the Cayley graph.  Relators are closed paths in `Gamma`, so it splits as `sum_i c_i` with
     `0 != c_i in Z_1(C_i)`, over finitely many copies that `alpha` itself picks.
   - Each `c_i` runs through a `Phi`-cycle of at least 42 lines.  A cycle line that no other `c_j` touches is
     active and pure.  The rank-one lemma allows such lines on one row only, so each copy has at most one.
   - Reduction: the coefficient-free **linked-cycle lemma** (in every finite family of copies carrying nonzero
     cycles, some copy has two untouched cycle lines) excludes every relation with `u(1) + w(1) = 0`, over any
     field.  Two copies share at most 3 cosets, so the lemma holds for at most 14 copies.  The star family is not
     a counterexample: it leaves at least 33 lines untouched.
   - Next step: prove the linked-cycle lemma for 15 or more copies, via an outermost copy.  Also handle
     `u(1) + w(1) != 0`, where the chain has rays along the cosets with `f_T(1) != 0`.

24. **Two-layer elements have no left annihilator (proposed established; `rips-segev-two-layer-elements-have-no-left-annihilator`).**
   - The previous item reduced the half `u(1) + w(1) = 0` to a linked-cycle lemma, known for at most 14 copies.
     Both halves now close: `alpha (u + w b^{±1}) = 0` with `w != 0` forces `alpha = 0`, in `k[G]` for every
     field `k`.
   - *Hopping lemma, every `N`.*  In any finite family of distinct copies carrying nonzero cycles, some copy has at
     least three lines of its cycle support untouched by the others.
     - Otherwise walk through the cycle supports, leaving the current copy at the first touched coset among the
       3rd, 4th and 5th.  The walk closes into a cyclically non-backtracking loop.
     - Its label is a cyclically reduced relation of `K`.  Greendlinger's arc (`> 5 gamma/8` syllables) puts
       13 consecutive `b`-edges of it into one copy.
     - Those 13 edges contain 3 consecutive edges, spanning 4 cosets, of each of two distinct copies.  Two distinct
       copies share at most 3 cosets.
   - *Removing `u(1) + w(1) = 0`.*  The edges `y <a> -- y b <a>` with `(alpha w)(y) != 0` form a graph in which
     every active coset has degree `>= 2`.
     - A leaf 2-edge-connected block carries a nowhere-zero flow over `k(s)`.  Filled along the cosets, it is a
       nonzero cycle that splits over copies as before.
     - Away from the block's bridge end, every port edge carries the cycle.  So untouched lines there are pure,
       and rows allow at most one per copy.  With the bridge end, that makes at most two, which the hopping lemma
       excludes.
   - This closes the line of `N`-copy attempts (items 13–15 and the linked-cycle reduction) for left
     annihilators.  By `g -> g^{-1}`, elements `u' + b^{±1} w'` have no nonzero right annihilator.
   - Next step: the other side, `(u + w b) alpha = 0`.  Equivalently, left annihilators of `w' + b u'`, with `b`
     to the left of the coefficient.
     - The edge equation becomes `X(b z) = -Y(z)`, linking right cosets `<a> z` to `<a> b z`.
     - The copies are left translates, with lines in left cosets, so the port graph has to be rebuilt.
     - After that comes `b`-degree at least two.
