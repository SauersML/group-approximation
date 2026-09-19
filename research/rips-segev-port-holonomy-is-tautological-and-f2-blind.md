---
rg: 2
id: rips-segev-port-holonomy-is-tautological-and-f2-blind
kind: claim
title: In Steenbock's Rips--Segev core the product of exit/entry ratios around any directed port cycle of a relation alpha (u + w b) = 0 is (-1)^L identically, the support condition at escaped points is relative to a chosen covering and leaves Rep_T of unbounded dimension, and over F_2 every ratio is 1; so no holonomy contradiction exists, and any proof must use rigidity of a minimal covering or, over F_2, pure support matching
distinct_from:
  rips-segev-single-copy-port-equations-are-always-solvable: that shows the one-copy port equations are always solvable; this kills the next step it proposed, the holonomy form with support conditions at escaped points over all copies.
  rips-segev-port-cycle-counting-has-n-independent-ceiling: that kills counting routes on port cycles; this kills the coefficient (ratio-product) route on port cycles.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: its rank-one lemma and short-relation lemma are used here; this adds that the active coset graph is simple and oriented and that the ratio product along it carries no information.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this is an obstruction to one route toward it.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-port-holonomy-is-tautological-and-f2-blind-proof`.
Obstruction.

**Setting.**  As in `rips-segev-three-copy-configurations-carry-no-zero-divisors` ([3C]): `K = F/<<R>>`,
`F = <a> * <b>`, Steenbock's graph `Gamma` over `Phi`, `Gr'_*(1/8)`, `gamma >= 42`.  A relation
`alpha (u + w b) = 0` in `k[K]` with `alpha != 0`, `u, w in k[t^{±1}]`, `u/w` not constant.  Put `X = alpha u`,
`Y = alpha w`, so `X(z b) = - Y(z)`.  For a left `<a>`-coset `T` put `P_T = f_T u` and `Q_T = f_T w`.
The *active coset graph* `Lambda` has the active cosets as vertices and an edge `T -> T'` for each point `z in T`
with `Y(z) != 0` (then `z b in T'`, where `X(z b) != 0`).

**Theorem.**
- (0) *Coprime reduction.*  If `g = gcd(u, w)`, then `alpha (u + w b) = 0` iff `(alpha g)(u' + w' b) = 0` with
  `u = g u'`, `w = g w'`, and `alpha g != 0`.  So one may assume `gcd(u, w) = 1`.  Then a pair of Laurent
  polynomials `(P, Q)` has the form `(h u, h w)` iff `P w = Q u`.
- (S) *Simplicity.*  `Lambda` has no loops, no parallel edges and no 2-cycles.  The out-degree of `T` is
  `|supp Q_T|` and its in-degree is `|supp P_T|`.  (Each failure is a relation of free-product length `<= 4`,
  which [3C] Lemma 7 forbids.)
- (A) *Holonomy is an identity.*  On a directed cycle `T_0 -> ... -> T_{L-1} -> T_0` of `Lambda`, with exit point
  `q_j` and entry point `p_j` in `T_j`, the transfer ratios `rho_j = Q_{T_j}(q_j) / P_{T_j}(p_j)` satisfy
  `prod_j rho_j = (-1)^L` for every solution.  So "the product is not `±1`" never gives a contradiction.  A ratio
  product constrains a solution only when each `rho_j` is fixed by the support pattern alone.
- (B) *The support condition is relative to a covering.*
  - Every `b`-edge `z -> z b` of the Cayley graph is an edge of some copy `h g(Gamma)`.  So one copy per active
    edge gives a covering for which `supp P_T` lies in the arrival ports of `T` and `supp Q_T` in the departure
    ports, for every `T`: the escape support condition always holds.
  - Adding copies with a line starting at the points of any finite set of `T` puts those points into both port
    sets (position `0` is in `In` and in `Out`).  So `Rep_T` (all `h` with `supp(h u)` in the arrival ports and
    `supp(h w)` in the departure ports) has unbounded dimension.  In particular `dim Rep_T <= 1` is false for
    coverings in general.
- (C) *`F_2` is blind to ratios.*  Over `F_2` every nonzero value is `1`, so every `rho_j = 1`.  A family `(f_T)`
  is a solution iff `z in supp Y <=> z b in supp X`.  So the `F_2` case of the target is exactly the
  non-existence of a finite `(u, w)`-harmonic family of cosets, a pure support statement.
- (M) *Minimal counterexamples are globally, not locally, rigid.*  Suppose `|supp X| + |supp Y|` is minimal.  Then
  the space of solutions supported in `(supp X, supp Y)` is `k alpha`.  This does not make any single `Rep_T`
  one-dimensional.

**Evidence on the `(x_4 x_1)^21` face** (`port_holonomy.py`, over `F_2`, `F_3`, `F_10007`, the witness pair and
three open random pairs; all checks pass).
- No face line has a nonzero face-copy `Rep`.  The holonomy product is `1 = (-1)^42`.  There are 1, 2 and 42
  distinct ratios over `F_2`, `F_3` and `F_10007`.
- The escape covering and its shift by `s = 7 · 10^300` both satisfy every support condition, so relative to them
  `dim Rep_T >= 2`.
- Even intrinsically, with `h` confined to `supp(h u) ⊆ supp P_T` and `supp(h w) ⊆ supp Q_T`, most face cosets
  have dimension 2 with entry and exit decoupled.  Over `F_10007` this holds for all 42 cosets in all four cases.
  Over `F_2` and `F_3` between 0 and 21 cosets are rigid, the rest free.

**What is left.**
- (i) Characteristic `!= 2`: fix a covering with the number of copies minimal for a minimal counterexample.  Show
  that some directed cycle of `Lambda` consists of cosets whose ratio is fixed by the pattern, and that the
  pattern-forced product differs from `(-1)^L`.
- (ii) Over `F_2`: exclude finite harmonic families using only (S) and the rank-one lemma of [3C].  This is a
  support-matching argument, since no coefficient information exists there.
