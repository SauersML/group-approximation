---
rg: 2
id: rips-segev-port-holonomy-is-tautological-and-f2-blind-proof
kind: route
title: The edge equation X(z b) = -Y(z) makes the ratio product around a directed cycle telescope to (-1)^L; every b-edge lies on a copy and position 0 is a port of both kinds, so escape support conditions hold for a canonical covering and can be enlarged at will; over F_2 all ratios are 1; minimality forces global but not local rigidity
target: rips-segev-port-holonomy-is-tautological-and-f2-blind
requires: [rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-single-copy-port-equations-are-always-solvable]
artifacts: [experiments/rips-segev-port-holonomy-2026-09-17/port_holonomy.py]
---

**Conventions.**
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof` and [SC] is
  `rips-segev-single-copy-port-equations-are-always-solvable-proof`.  Notation is that of [3C].
- `alpha = sum_T z_T f_T(a)` over left `<a>`-cosets `T = z_T <a>`, with `P_T = f_T u`, `Q_T = f_T w`,
  `X(z_T a^p) = P_T(p)` and `Y(z_T a^p) = Q_T(p)`.  Values of `X`, `Y` at points do not depend on base points.
- `u != 0` and `w != 0` (the nonvanishing step of [3C] Lemma 1 for `u`; `w = 0` gives `alpha u = 0`, impossible
  in the domain `k[t^{±1}]` coset by coset).  So `supp P_T` and `supp Q_T` are nonempty for active `T`.

## 1. Coprime reduction

**Lemma 0.**  Let `g = gcd(u, w)` in the PID `k[t^{±1}]`, `u = g u'`, `w = g w'`.
- `alpha (u + w b) = (alpha g)(u' + w' b)`, since `g in k[<a>]` and `u + w b = g (u' + w' b)`.
- `alpha g = sum_T z_T (f_T g)(a)` has nonzero pieces `f_T g` in the distinct active cosets, so `alpha g != 0`.
- So a counterexample for `(u, w)` gives one for `(u', w')`, with `u'/w' = u/w`.  Assume `gcd(u, w) = 1`.
- Then `P w = Q u` forces `u | P`, say `P = h u`, and then `Q = h w`.  Conversely `(h u, h w)` satisfies it.  So
  for active `T` the pair `(P_T, Q_T)` is determined by the polynomial identity `P_T w = Q_T u` together with
  `P_T != 0`.  ∎

## 2. Simplicity of the active coset graph

**Lemma S.**  Let `z = z_T a^p` and `z' = z_T a^q` be points of an active coset `T`.
- (out, out)  If `p != q`, `Y(z) != 0 != Y(z')`, then `z b` and `z' b` lie in distinct cosets.
- (in, in)  If `p != q`, `X(z) != 0 != X(z')`, then `z b^{-1}` and `z' b^{-1}` lie in distinct cosets.
- (loop)  If `Y(z) != 0`, then `z b notin T`.
- (2-cycle)  No coset `T'` receives an edge from `T` and sends one to `T`.

*Proof.*  Each failure gives a word `W != 1` of `F` with `W = 1` in `K`, cyclically reduced of free-product length
at most 4, against [3C] Lemma 7 (`|W|_* > 5 gamma / 8 - 1 >= 25.25`).
- (out, out)  `z_T a^p b = z_T a^q b a^m` gives `W = b^{-1} a^{p - q} b a^{-m}`.  If `m = 0` this conjugates to
  `a^{p - q}`, of length 1.  Otherwise it has length 4.
- (in, in)  The same with `b^{-1}` in place of `b`.
- (loop)  `z_T a^p b = z_T a^q` gives `W = a^{p - q} b`, of length at most 2.
- (2-cycle)  `z_T a^p b a^m b = z_T a^q` gives the cyclic word `a^{p - q} b a^m b`, of length at most 4.  ∎

**Corollary.**  `Lambda` is a finite simple oriented graph.
- The out-edges at `T` are the points of `supp Q_T`: at `z` with `Y(z) != 0` we have `X(z b) = - Y(z) != 0`, so
  `z b` lies in an active coset.
- The in-edges at `T` are the points of `supp P_T`: at `z` with `X(z) != 0` the point `z b^{-1}` has
  `Y(z b^{-1}) = - X(z) != 0`.
- So `sum_T |supp Q_T| = sum_T |supp P_T|` is the number of edges.

## 3. Theorem A: holonomy is an identity

Let `T_0 -> T_1 -> ... -> T_{L-1} -> T_0` be a directed cycle of `Lambda`.  Edge `e_j` goes from the exit point
`z_T_j a^{q_j}` to the entry point `z_T_{j+1} a^{p_{j+1}}` (indices mod `L`).  The edge equation reads
`P_{T_{j+1}}(p_{j+1}) = - Q_{T_j}(q_j)`.
Put `rho_j = Q_{T_j}(q_j) / P_{T_j}(p_j)`.  All values are nonzero.  Then
`prod_j rho_j = prod_j Q_{T_j}(q_j) / prod_j (- Q_{T_{j-1}}(q_{j-1})) = (-1)^L`.
This holds for every solution and every cycle.  ∎

*Consequence.*  A ratio-product argument can only work as follows.  Some pattern (supports, or a covering)
determines each `rho_j` as a function of the pattern alone, and then the pattern-determined product is shown to
differ from `(-1)^L`.  Everything therefore rests on rigidity: whether the pattern fixes `rho_j`.  Sections 4 to 6
show that the escape support condition supplies no such rigidity.

## 4. Theorem B: the escape support condition is relative to a covering

A *covering* is a finite set `C` of copies `h g(Gamma)`.  For a coset `T`, let `A_T(C)` (arrival ports) be the
set of `p` such that `z_T a^p = h g(v_{i,x})` for a copy in `C`, a line `i` and a position `x in In_i`.  Define
`D_T(C)` (departure ports) in the same way with `Out_i`.  Put
`Rep_T(C) = {h in k[t^{±1}] : supp(h u) ⊆ A_T(C), supp(h w) ⊆ D_T(C)}`.
The intrinsic space is `R_T = {h : supp(h u) ⊆ supp P_T, supp(h w) ⊆ supp Q_T}`.  It contains `f_T`.

**(B1) The support condition always holds for some covering.**  Let `z -> z b` be an active edge.  Pick a `b`-edge
`v_{l,q} -> v_{k,p}` of `Gamma`, so that `q in Out_l`, `p in In_k` and `g(v_{k,p}) = g(v_{l,q}) b`.  Put
`h = z g(v_{l,q})^{-1}`.  Then `h g(v_{l,q}) = z` and `h g(v_{k,p}) = z b`.
Let `C_0` consist of these copies, one per active edge.  Every point of `supp Q_T` is the tail of an active edge,
so it is a departure port.  Every point of `supp P_T` is the head of one, so it is an arrival port.  Hence
`f_T in Rep_T(C_0)` for every `T`.  No relation in `K` is needed, since each `h` is chosen freely.

**(B2) Monotonicity and unboundedness.**
- `Rep_T(C)` only grows when `C` grows.  If the support condition holds for `C`, then `R_T ⊆ Rep_T(C)`.  So
  `dim Rep_T(C) >= dim R_T` for every admissible covering, and `R_T` is the covering-free lower limit.
- Let `E ⊆ Z` be finite.  The copies `z_T a^x g(v_{1,0})^{-1} g(Gamma)`, for `x in E`, put `z_T a^x` at position
  `0` of line 1.  Position `0` lies in `In_1 ∩ Out_1`, so `E ⊆ A_T ∩ D_T` afterwards.
- Given any finite-dimensional space `H` of Laurent polynomials, take `E = ∪_{h in basis} supp(h u) ∪ supp(h w)`.
  Then `H ⊆ Rep_T`.  For example `f_T` and `t^s f_T` (`s != 0`) are independent and both lie in `Rep_T` for
  a suitable covering.  So the claim "`dim Rep_T <= 1`" fails for coverings in general.  ∎

*Consequence.*  The escape condition can shrink `Rep_T` only once the covering is pinned down by some other
principle, such as a minimal number of copies, and it can never shrink it below `R_T`.  Section 7 records that
`R_T` itself has dimension 2, with entry and exit decoupled, on most cosets of the face realizations.

## 5. Theorem C: over F_2 there is no ratio information

Over `F_2`, `- 1 = 1` and every nonzero value is `1`.  So every `rho_j = 1`, and Theorem A says `1 = 1`.  The
edge equation `X(z b) = Y(z)` becomes `z b in supp X <=> z in supp Y`, that is `supp X = (supp Y) b`.
Hence nonzero `(f_T)` solve the relation iff
`∪_T z_T a^{supp(f_T u)} = (∪_T z_T a^{supp(f_T w)}) b`.
Call such a finite family *`(u, w)`-harmonic*.  The `F_2` case of the target (for this `u + w b`) is exactly the
non-existence of harmonic families.  That is a statement about supports, and any rigidity or holonomy argument
is vacuous for it.  ∎

## 6. Lemma M: minimality gives global rigidity only

Let `alpha` be a counterexample with `|supp X| + |supp Y|` minimal.  Let `V` be the space of families `(f'_T)`
with `supp(f'_T u) ⊆ supp P_T` and `supp(f'_T w) ⊆ supp Q_T` that satisfy every edge equation.
- Every element of `V` solves the relation: at points outside the supports both sides vanish.
- Suppose `beta in V` is not proportional to `alpha`.  Since `beta != 0` and `w != 0`, some `z` has
  `Y_beta(z) != 0`, and then `Y_alpha(z) != 0`.  So `gamma = alpha - (Y_alpha(z) / Y_beta(z)) beta` is a nonzero
  element of `V` with `z notin supp Y_gamma`.  That contradicts minimality.
- Hence `V = k alpha`.  ∎

This is global rigidity.  It fixes every `rho_j` as a function of the pattern, but it does not help with Theorem
A: the actual solution satisfies `prod rho_j = (-1)^L` anyway.  A ratio product gives a *constraint* only when
each `R_T` on the cycle is one-dimensional (*locally rigid*).  Then `rho_T` is read off from `R_T` alone, before
any edge equation is imposed, and the edge equations demand that these numbers multiply to `(-1)^L`.

## 7. Checks on the (x_4 x_1)^21 face

`port_holonomy.py` (exit 0, `ALL CHECKS PASS`, about one minute wall, output `port_holonomy.out`) uses the face of
[SC]: long lines `L_t` (row `2t + 1`; enter at `I_1`, leave at `O_2`) and middle lines `M_t` (row `2t + 2`;
enter and leave at `0`), 42 cosets in all.  It runs over `F_2`, `F_3` and `F_10007`, on the witness pair and
three open random pairs with 8 to 9 exponents from `{0, 1, 7, 10^{5r-4}, 10^{5r}}`.  For each case it does the
following.
- It checks that the face-copy system `P w = Q u` with `P` on `In_i` and `Q` on `Out_i` has only the zero
  solution for every face line.  So the face copy alone fixes no ratio.
- It realizes random nonzero edge values by `f_T`, as in [SC].  It computes `rho_T` from the realized
  polynomials and checks `prod rho_T = 1 = (-1)^42` (Theorem A).  Over `F_2` it checks `rho_T = 1` for all `T`.
  The numbers of distinct ratios are 1, 2 and 42 over `F_2`, `F_3` and `F_10007`.
- It builds the escape covering (Theorem B1, with position 0 of a new line at every escaped point) and its shift
  by `s = 7 · 10^300`.  It checks that `f_T` and `t^s f_T` both satisfy the support conditions (B2).
- It computes a basis of `R_T`, with `h` confined to the shifts `(supp P_T - supp u) ∪ (supp Q_T - supp w)`.
  This is a subspace of `R_T`, so its dimension is a lower bound.  It checks each basis vector and tests whether
  the entry and exit functionals are proportional on it (*rigid*) or not (*free*).

The `(dim, rigid/free)` counts over the 42 cosets are as follows.

| field | witness | open 0 | open 1 | open 2 |
|---|---|---|---|---|
| `F_2` | 21 (1, rigid), 21 (2, free) | 42 (2, free) | 21 (1, rigid), 21 (2, free) | 42 (2, free) |
| `F_3` | 10 (1, rigid), 32 (2, free) | 42 (2, free) | 10 (1, rigid), 32 (2, free) | 14 (1, rigid), 28 (2, free) |
| `F_10007` | 42 (2, free) | 42 (2, free) | 42 (2, free) | 42 (2, free) |

So on these realizations no face cycle is locally rigid, and the face holonomy imposes nothing.  The face
realizations are not complete solutions: the escaped points have no partners.  The table is evidence about
`R_T` on the face, not a theorem about complete solutions.

## 8. What is left

- (i) Characteristic `!= 2`.  Fix a minimal counterexample (Lemma M) and a covering with the minimal number of
  copies.  Find a directed cycle of `Lambda` on which every `R_T` is one-dimensional.  Then show that the
  pattern-forced product `prod rho_T` differs from `(-1)^L`.  The face data show that such cycles need not
  come from a single face.
- (ii) `F_2`.  Exclude finite `(u, w)`-harmonic families using only Lemma S (a simple oriented graph with
  out-degree `|supp f_T w|` and in-degree `|supp f_T u|`) and the rank-one lemma of [3C].  No ratio or holonomy
  argument can contribute there.
