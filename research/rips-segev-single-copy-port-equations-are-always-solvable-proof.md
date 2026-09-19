---
rg: 2
id: rips-segev-single-copy-port-equations-are-always-solvable-proof
kind: route
title: The port map of a line has image equal to the annihilator of its dependencies, row separation leaves at most one line with a dependency, and so every edge valuation of one copy compatible with that line is realized by coefficients; a directed face cycle gets nonzero ports at every one of its cosets over every field
target: rips-segev-single-copy-port-equations-are-always-solvable
requires: [rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors]
artifacts: [experiments/rips-segev-one-copy-realizability-2026-09-17/face_realizability.py]
---

**Conventions.**
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof`, [OC] is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`, and [EE] is
  `rips-segev-witness-supports-carry-no-zero-divisors-proof`.
- Notation is that of [3C]: `Gamma` is Steenbock's graph over `Phi`, line `i` has row `r_i` (injective in `i`),
  `D_i = {0, I_1, I_2, O_1, O_2, C_i}`, `In_i = {0, I_1, I_2, C_i}` and `Out_i = {0, O_1, O_2, C_i}`.
- The `b`-edges of `Gamma` are the lifts of the edges of `Phi`.  The edge `x_1` runs `v_{l,0} -> v_{k,I_1}`,
  `x_2` runs `v_{l,C} -> v_{k,I_2}`, `x_3` runs `v_{l,O_1} -> v_{k,C}` and `x_4` runs `v_{l,O_2} -> v_{k,0}`.  So each
  port of `In_i` receives exactly one edge and each port of `Out_i` emits exactly one, and `Phi` has no loops.
- `u, w in k[t^{±1}]` are nonzero and `u/w` is not constant.  For a function `A` on a finite set `S ⊂ Z`, put
  `Ǎ(t) = sum_{p in S} A(p) t^{-p}`.

## 1. The local system is the in-copy part of the relation

Let `C_M = h_M g(Gamma)` be a copy, and let `f_i in k[t^{±1}]` be given for the lines `i`.  Put
`alpha = sum_i h_M g(v_{i,0}) f_i(a)`, `X = alpha u` and `Y = alpha w`.

**Lemma 0.**
- (a) Distinct lines lie in distinct left `<a>`-cosets, and `X(h_M g(v_{i,0}) a^p) = P_i(p)`,
  `Y(h_M g(v_{i,0}) a^p) = Q_i(p)`, where `P_i = f_i u` and `Q_i = f_i w`.
- (b) If `z` and `z b` both lie in `V_M`, then `z -> z b` is a `b`-edge `v_{l,p} -> v_{k,p'}` of `C_M`, and the
  equation `X(z b) = - Y(z)` reads `P_k(p') = - Q_l(p)`.

*Proof.*
- (a) By [OC] §1 (Lemma 1 and its consequence), translated by `h_M`, a left `<a>`-coset meets `V_M` in at most
  one line.  The coset of line `i` is `h_M g(v_{i,0}) <a>`, and the coefficient of `alpha` there is `f_i(a)`.
- (b) The first part is [EE] 1(a)-(b), as used in [3C] Lemma 3(a).  For the second, the edge means
  `g(v_{l,0}) a^p b = g(v_{k,0}) a^{p'}`, and (a) evaluates both sides. ∎

So the *local system* of `C_M` (the edge equations `Q_l(p) = - P_k(p')`) is exactly the set of equations
`X(z b) = - Y(z)` with both `z, z b in V_M`.  The values of `P_i`, `Q_i` off the ports are not constrained by it.
Every other equation has `z` or `z b` outside `V_M`: these are the escape equations.

## 2. Duality

For a line `i` put `Phi_i(f) = ((f u)(p))_{p in In_i} ⊕ ((f w)(q))_{q in Out_i} in k^{In_i} ⊕ k^{Out_i} = k^8`.
The two summands are separate coordinates, even at the shared positions `0` and `C_i`.  Pair `k^8` with itself by
the standard form, and let `Dep_i` be the space of pairs `(A, B)`, `A` on `In_i` and `B` on `Out_i`, with
`Ǎ u + B̌ w = 0`.

**Lemma 1.**  `Im Phi_i = Dep_i^perp`.

*Proof.*  `Phi_i` is linear, and `k[t^{±1}]` is spanned by the monomials `t^s`.  So `(A, B)` annihilates the
image iff `sum_p A(p) (t^s u)(p) + sum_q B(q) (t^s w)(q) = 0` for all `s in Z`.  Since `(t^s u)(p) = u(p - s)`,
the left side is `sum_p A(p) u(p - s) + sum_q B(q) w(q - s)`.  This is the coefficient of `t^{-s}` in
`Ǎ u + B̌ w`.  So the annihilator of `Im Phi_i` is `Dep_i`.  In the finite-dimensional space `k^8`,
`Im Phi_i = (Im Phi_i)^{perp perp} = Dep_i^perp`. ∎

**Lemma 2.**  If `(A, B) in Dep_i` is nonzero, then `Ǎ != 0`, `B̌ != 0`, and `u/w = - B̌/Ǎ`.  In particular
`e_p ∉ Dep_i` for every coordinate vector `e_p` of `k^8`.

*Proof.*  `Ǎ = 0` gives `B̌ w = 0`, so `B̌ = 0` and `(A, B) = 0`, since the monomials `t^{-q}` for `q in Out_i`
are distinct.  Symmetrically `B̌ = 0` forces `Ǎ = 0`, because `u != 0`.  Then `Ǎ u = - B̌ w`.
- `e_p` with `p in In_i` has `B̌ = 0`.
- `e_q` with `q in Out_i` has `Ǎ = 0`. ∎

## 3. At most one dependent line

**Lemma 3.**  `Dep_i != 0` for at most one line `i` of `Gamma`.

*Proof.*  Let `i != j` and suppose `(A_i, B_i) in Dep_i` and `(A_j, B_j) in Dep_j` are nonzero.
- By Lemma 2, `Ǎ_i u = - B̌_i w` and `Ǎ_j u = - B̌_j w`, with all four polynomials nonzero.  Cross-multiplying,
  `Ǎ_i B̌_j u w = Ǎ_j B̌_i u w`.  Since `k[t^{±1}]` is a domain, `Ǎ_i B̌_j = Ǎ_j B̌_i`.
- `Ǎ_i` and `B̌_i` are supported in `-D_i`, and `Ǎ_j`, `B̌_j` in `-D_j`.  Since `r_i != r_j`, [3C] Corollary 2
  (proof) gives `(D_i - D_i) ∩ (D_j - D_j) = {0}`.  So `(x, y) -> x + y` is injective on `(-D_i) × (-D_j)`.
- Comparing coefficients, `Ǎ_i(x) B̌_j(y) = Ǎ_j(y) B̌_i(x)` for all `x in -D_i` and `y in -D_j`.  Here `Ǎ(x)` is the
  coefficient of `t^x`.
- Pick `y_0` with `Ǎ_j(y_0) != 0` and put `c = B̌_j(y_0)/Ǎ_j(y_0)`.  Then `B̌_i = c Ǎ_i`, and
  `u/w = - B̌_i/Ǎ_i = - c` is constant, against the hypothesis. ∎

This is [3C] Lemma 1 transposed: there the two polynomials of one coset are `P_T, Q_T`.  Here they are the
reflected dependency `(Ǎ, B̌)`, and the fixed ratio `u/w` plays the role of the relation.

## 4. Realizability

A *valuation* is a function `c` on the `b`-edges of `Gamma`.  It prescribes on each line `i` the vector
`v_i(c) = ((- c(e_p))_{p in In_i}, (c(e_q))_{q in Out_i})`, where `e_p` is the edge arriving at the port `p` and
`e_q` the edge leaving `q`.

**Proposition 4.**  Let `i_0` be the dependent line, if there is one.  If `v_{i_0}(c) in Dep_{i_0}^perp`, there are
`f_i` with `Phi_i(f_i) = v_i(c)` for every `i`.  Then `Q_l(p) = c(e) = - P_k(p')` on every edge
`e = v_{l,p} -> v_{k,p'}`, so the local system holds.

*Proof.*  The unknowns `f_i` of distinct lines are independent, and the equation of `e` involves `f_l` only
through `Q_l(p) = c(e)` and `f_k` only through `P_k(p') = - c(e)`.  So, given `c`, the system splits into the
conditions `v_i(c) in Im Phi_i`, one per line.  By Lemmas 1 and 3, `Im Phi_i = k^8` for `i != i_0`, and
`Im Phi_{i_0} = Dep_{i_0}^perp`.  Take `f_i = 0` when `v_i(c) = 0`. ∎

## 5. Faces

**Proposition 5.**  Let `c_0` be a directed cycle of `Phi`, through lines `i_1, ..., i_m`, with edges
`e_t : i_t -> i_{t+1}` (indices mod `m`).  There is a solution of the local system with
`Q_{i_t}(q_t) != 0` and `P_{i_{t+1}}(p_{t+1}) != 0` for every `t`, where `q_t`, `p_{t+1}` are the ports of `e_t`.
Its active lines are the `i_t`, plus at most 6 further lines adjacent to `i_0`.  This holds over every field `k`.

*Proof.*  A directed cycle visits distinct vertices, so line `i_t` carries exactly two cycle edges: `e_{t-1}`,
arriving at an in-port, and `e_t`, leaving an out-port.
- *No dependent line on the cycle.*  Put `c = 1` on the cycle edges and `c = 0` elsewhere.  If `i_0` exists and
  is off the cycle, then `v_{i_0}(c) = 0 in Dep_{i_0}^perp`.  Proposition 4 applies.
- *`i_0 = i_t`.*  Let `p` be the in-port of `e_{t-1}` and `q` the out-port of `e_t` at `i_0`.
  - `Dep^perp` is contained in the hyperplane `{x_p = 0}` iff `e_p in Dep^{perp perp} = Dep`.  By Lemma 2 it is
    not.  The same holds for `{x_q = 0}`.
  - A vector space over any field is never the union of two proper subspaces.  (If `x ∈ U_1 \ U_2` and
    `y ∈ U_2 \ U_1`, then `x + y` lies in neither.)  So some `v in Dep_{i_0}^perp` has `v_p != 0` and `v_q != 0`.
  - Define `c` on the 8 edges at `i_0` by `v = v_{i_0}(c)`.  That is, `c(e) = - v_{p'}` on the edge arriving at
    `p'` and `c(e) = v_{q'}` on the edge leaving `q'`.  This is consistent, because `Phi` has no loops, so no edge
    has both ends at `i_0`.
  - Put `c = 1` on the other cycle edges and `c = 0` on all remaining edges.  Proposition 4 applies.
- In both cases every cycle edge has `c != 0`.  The nonzero `v_i(c)` occur only on the cycle lines and on the
  other ends of the at most 6 non-cycle edges at `i_0`. ∎

**The `(x_4 x_1)^21` face.**  On the `gamma = 42` graph of the target's item 12, `c_0 = (x_4 x_1)^21` is a closed
directed walk of length 42.  Girth `>= 42` makes it a directed cycle, since a repeated vertex would close a
shorter directed walk.  Its lines alternate:
- *long lines*, entered by `x_1` at `I_1` and left by `x_4` at `O_2`;
- *middle lines*, entered by `x_4` at `0` and left by `x_1` at `0`.

So Proposition 5 gives 42 active cosets of one copy along the face.  Every face port is nonzero, and the ratio
`P_T/Q_T = f_T u / f_T w = u/w` holds on each.  This refutes the local lemma asked for in
`rips-segev-port-cycle-counting-has-n-independent-ceiling`, which proves the claim's (a)-(e).
- *Arc cosets are not coupled by a ratio.*  Consecutive cosets `i_t`, `i_{t+1}` share only the scalar `c(e_t)`.
  A cycle line off `i_0` imposes nothing on its two values (Lemma 3).
- *Pure cosets.*  Call line `i` *pure* if `supp P_i ⊆ In_i` and `supp Q_i ⊆ Out_i`.  At most one line is pure.
  Indeed `P_i Q_j = f_i f_j u w = P_j Q_i` holds identically, so the tensor step of [3C] Lemma 1, with the row
  separation of [3C] Corollary 2, turns two pure lines into `u = c w`.  Every other active line has support
  points off its ports.  These escape: by Lemma 0(b), a nonzero `Y(z)` at a non-port position of a line has
  `z b ∉ V_M`, and a nonzero `X(z)` there has `z b^{-1} ∉ V_M`.

## 6. Calibration

- *Regular elements.*  `u + w b = 1 + 2a + (3 + a) b` is regular (`rips-segev-witness-pairs-carry-no-zero-divisors`),
  and `u/w = (1 + 2t)/(3 + t)` is not constant.  Propositions 4 and 5 apply to it verbatim.  So the one-copy
  local system is satisfiable even when no zero divisor exists.  Any proof that excludes a configuration must use
  something beyond it.
- *Where [OC] gets its contradiction.*  [OC] assumes `supp X ∪ supp Y ⊆ V_M`.  With that assumption there are no
  escape equations, so `supp P_i ⊆ In_i` and `supp Q_i ⊆ Out_i` ([OC] Lemma 2), and every active line is pure.
  The contradiction is then [3C] Corollary 2 on two pure lines, which is exactly the support condition.  In the
  solutions of §5 all but one active line is impure, so the support condition is where they fail.

## 7. What it leaves

In a genuine relation `alpha (u + w b) = 0` over `N` copies, [3C] Lemma 3(a) holds at every point of the
covering: `Y(z) != 0` forces `z -> z b` to be a copy edge or a bridge, and `X(z) != 0` forces the same for
`z b^{-1} -> z`.  So for every active coset `T` (with any base point):
- `supp(f_T u)` lies in the arrival ports of `T`, and `supp(f_T w)` in its departure ports, over all copies it
  meets;
- `u/w = P_T/Q_T` is a representation with numerator and denominator on those finite port sets.  Let `Rep_T` be
  the space of such `f_T`.

The realizable port vectors of `T` are then `Phi_T(Rep_T)`, typically of dimension `<= 1`, not the 8-dimensional
`Dep_T^perp` of Lemma 1.  So a contradiction has to use the support conditions at the escaped points, that is,
the arrival and departure ports that `T` has in other copies.  It must therefore couple the coefficients of at
least two copies at non-distinguished positions.

*Holonomy form.*  Suppose `dim Rep_T = 1` for every coset along a directed port cycle.  Then each such `T` fixes
the ratio of its exit value to its entry value.  Going around the cycle, the product of these ratios must be `1`
(or `-1` per the sign convention of the edge equations).  This multiplicative condition is the natural
replacement for the ratio recursion the step asked for.

## 8. Checks

`face_realizability.py` (exit 0, `ALL CHECKS PASS`, about 1 s, output `face_realizability.out`) works over
`F_2`, `F_3` and `F_10007` with Steenbock rows `1..42` on the `(x_4 x_1)^21` face.  Middle lines use position `0`
for both face edges, and long lines use `I_1` and `O_2`.  For each pair `(u, w)` it does the following.
- It computes `Dep_i` for rows `1..60`, and asserts that at most one is nonzero (Lemma 3).
- It builds `c` as in Proposition 5, solves `Phi_i(f_i) = v_i(c)` by row reduction (Lemma 1 in the solvable
  direction), and checks every modelled edge equation.
- It checks that all 84 face ports are nonzero and that at most one line is pure.

The pairs are:
- the witness pair `(1 + 2t, 3 + t)`;
- three random open-regime pairs, with 14 to 17 exponents drawn from `{0, 1, 7, 10^{5r-4}, 10^{5r}}`,
  span at least `10^{59}`, and `S - S` meeting the distinguished differences in up to 12 rows;
- two adversarial pairs `u = - B̌`, `w = Ǎ`, built from a middle line (`M_0`) and a long line (`L_3`) so that
  that line is dependent.

In the four independent cases 42 lines are active, none is pure, and about 1100 to 1400 support points escape.
In the two dependent cases exactly one line is dependent, 2 to 6 extra neighbour lines become active, and all
equations hold.
