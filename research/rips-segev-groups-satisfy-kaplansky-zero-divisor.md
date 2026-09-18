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
