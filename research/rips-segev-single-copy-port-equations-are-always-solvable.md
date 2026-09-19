---
rg: 2
id: rips-segev-single-copy-port-equations-are-always-solvable
kind: claim
title: In Steenbock's Rips--Segev core the port equations of one copy never contradict a fixed nonconstant ratio u/w, over any field, because the port map of a line has image Dep^perp and at most one line has a nonzero dependency; so every b-edge valuation of a copy that is nonzero on a face cycle, including the (x_4 x_1)^21 face of the gamma = 42 graph, is realized by coefficients, and no single-face or single-copy coefficient lemma exists
distinct_from:
  rips-segev-port-cycle-counting-has-n-independent-ceiling: that kills counting routes and asks for a local coefficient lemma along one shell face; this proves that lemma false, for every nonconstant u/w and every face, and locates what any contradiction must use.
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that kills the extremal-copy step on supports alone; this kills its local coefficient version, with coefficients and the fixed ratio u/w included.
  rips-segev-one-copy-configurations-carry-no-zero-divisors: that forbids all support inside one copy; this shows the one-copy port equations alone are always solvable once support may leave the copy, so the contradiction there comes only from the support condition.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: its rank-one lemma is a consequence of the fixed ratio and holds in every solution built here; this shows it is the only coefficient content of one copy.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this is an obstruction to one route toward it.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-single-copy-port-equations-are-always-solvable-proof`.
Class-killing obstruction.

**Setting.**  As in `rips-segev-three-copy-configurations-carry-no-zero-divisors` ([3C]).  `Gamma` is a Steenbock
graph over `Phi`.  Line `i` has row `r_i` (injective in `i`), ports `In_i = {0, I_1, I_2, C_i}` and
`Out_i = {0, O_1, O_2, C_i}`, and 8 incident `b`-edges, one at each port.  Fix `u, w in k[t^{±1}]`, nonzero, with
`u/w` not constant.  (A constant ratio `u = c w` gives `u + w b = w (c + b)`, which is regular.)

**The local system of a copy `C_M`.**  Unknowns are `f_i in k[t^{±1}]`, one per line.  Put `P_i = f_i u` and
`Q_i = f_i w`.  The equations are
`Q_l(p) = - P_k(p')` for every `b`-edge `v_{l,p} -> v_{k,p'}` of `Gamma`.
These are exactly the equations `X(z b) = - Y(z)` of a relation `alpha (u + w b) = 0` at the points `z` with `z`
and `z b` both in `V_M`, for `alpha = sum_i h_M g(v_{i,0}) f_i(a)`.  All other equations involve a point outside
`V_M`.  They are the *escape equations*.

**Theorem.**
- (a) *Duality.*  Let `Phi_i(f) = ((f u)(p))_{p in In_i} ⊕ ((f w)(q))_{q in Out_i} in k^8`.  Then
  `Im Phi_i = Dep_i^perp`, where `Dep_i` is the space of pairs `(A, B)`, `A` on `In_i` and `B` on `Out_i`, with
  `A(t^{-1}) u(t) + B(t^{-1}) w(t) = 0`.
- (b) *At most one dependent line.*  `Dep_i != 0` for at most one line `i` of `Gamma`.
- (c) *Realizability.*  Let `c` be a valuation of the `b`-edges of `Gamma`.  Suppose it satisfies the condition
  of `Dep_{i_0}` at the dependent line `i_0`, if there is one.  Then some `(f_i)` solves the local system with
  `Q_l(p) = c(e) = - P_k(p')` on every edge `e`.
- (d) *Faces.*  For every directed cycle `c_0` of `Phi`, there is a solution with nonzero values at all the ports
  of the lifted cycle.  So all its cosets are active, and the ratio `P_T/Q_T = u/w` holds on each of them.  The
  support is the lifted cycle's lines, plus at most 6 neighbour lines of `i_0`.  This holds over every
  field, `F_2` included.  In particular it holds for the `(x_4 x_1)^21` face of the `gamma = 42` graph: `l = 42`,
  `L = 42`, all `b`-syllables `b^2`.
- (e) So the step asked for in `rips-segev-port-cycle-counting-has-n-independent-ceiling` is false as a local
  statement.  That step says the port equations with fixed `u/w` cannot hold along `>= 21` consecutive impure
  arc cosets of one copy, whatever the other copies do.
  - There is no ratio recursion along an arc.  Consecutive arc cosets share one scalar, the value on their
    common `b`-edge.  Each coset's fixed ratio constrains its 8 port values only through `Dep`, and only at one
    line of `Gamma`.
  - The rank-one lemma of [3C] holds automatically in these solutions.  At most one coset is pure, and the other
    cosets escape the copy at up to about 1400 support points in the tests.

**Calibration.**  The local system is also solvable for elements already proved regular.  One example is
`u + w b = 1 + 2a + (3 + a) b`, on the witness support `{1, a, b, ab}`.  So no correct proof of regularity can use
only one copy's equations.  The one-copy theorem needs the *support* condition: every point of
`supp P_i ∪ supp Q_i` is a port of the copy.  With that condition, a line can be active only if `u/w = P/Q` with
`P` on `In_i` and `Q` on `Out_i`.  The tensor argument of (b) allows this on at most one line, which is [3C]
Corollary 2.

**What it leaves.**  In a genuine counterexample, every active coset `T` has `supp(f_T u)` in its arrival ports
and `supp(f_T w)` in its departure ports, over the whole covering ([3C] Lemma 3(a)).  So `u/w = P_T/Q_T` is a
*representation on the port set of `T`*, and the realizable port vectors of `T` form the small space
`Phi_T(Rep_T)`, not the space `Dep_T^perp` of (a).
- Any contradiction must use these support conditions at the escaped points, and so must couple the
  coefficients of at least two copies at non-distinguished positions.
- A concrete target is the *holonomy form*.  Where `dim Rep_T = 1`, the ratio of exit value to entry value of
  `T` is a fixed scalar.  Its product around every cycle of the port digraph must then be `±1`.

Artifact: `experiments/rips-segev-one-copy-realizability-2026-09-17/face_realizability.py` (output
`face_realizability.out`, about 2 s).  It builds the `(x_4 x_1)^21` face with Steenbock rows `1..42` over `F_2`,
`F_3` and `F_10007`, for three kinds of pair `(u, w)`:
- the witness pair;
- three open-regime pairs with 14 to 17 exponents, span at least `10^{59}`, and `S - S` meeting `Dist` in up to
  12 rows;
- two adversarial pairs that make a middle or a long face line dependent.

For each it solves for the `f_i` and checks every `b`-edge equation of the modelled copy, the nonvanishing of all
84 face ports, and at most one pure coset.  It also checks that at most one of the rows `1..60` has a nonzero
dependency.  All checks pass.
