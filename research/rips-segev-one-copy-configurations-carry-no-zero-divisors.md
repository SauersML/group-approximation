---
rg: 2
id: rips-segev-one-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on one translate of the vertex set of Gamma, because the port identities P_i Q_j = P_j Q_i and row separation force every port onto the line endpoints, which the x_1/x_2 gluing forbids
distinct_from:
  rips-segev-port-data-cannot-exclude-balanced-divisors: that shows Gamma itself is a balanced port configuration, so support data cannot exclude two-layer zero divisors; this adds the coefficients and shows the configuration Gamma carries no solution, for any u, w and any field.
  rips-segev-witness-supports-carry-no-zero-divisors: that handles beta = p + x a + y b + z ab with alpha supported on the a-lines; this handles u(a) + w(a) b with arbitrary a-supports, with the hypothesis placed on the products alpha u and alpha w instead of on alpha.
  rips-segev-support-method-threshold-is-exactly-q-gamma: that is the support-only threshold q(gamma); this is a coefficient argument that applies to every support size, including the silent supports beyond that threshold, but only for configurations inside one copy of Gamma.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this excludes the Gamma-local two-layer relations.
artifacts:
  - experiments/rips-segev-one-copy-2026-09-18/one_copy_ports.py
  - experiments/rips-segev-one-copy-2026-09-18/ports_results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`.

**Setting.**
- `Gamma` is Steenbock's explicit generalized Rips--Segev graph (arXiv:1307.0981), with `Gr'_*(1/8)`.
- `K` is its core and `G = G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`.
- `g : V(Gamma) -> K` sends a vertex `v` to the image of the label of a path from the base vertex `v_{1,0}` to
  `v`.  Line `i` has row `r = phi(i)`, with `phi` injective, and positions `0 <= p <= C_i`.  Its distinguished
  positions are `(I_1, I_2, O_1, O_2, C) = 10^{5r-4}, ..., 10^{5r}`.
- *Targets* of `b`-edges on line `i` form `In_i = {0, I_1, I_2, C}`.  *Sources* form `Out_i = {0, O_1, O_2, C}`.

**Theorem.**  Let `k` be a field, and let `u, w in k[<a>]`, `alpha in k[K]` with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there is no `h in K` with `supp(alpha u) ∪ supp(alpha w) ⊆ h g(V(Gamma))`.  The
same holds in `k[G]`, with `h in G`.

**Mechanism.**
1. *Cosets meet one line each.*  If `g(v) a^x = g(v')`, then `v, v'` lie on one line at distance `x`.  This is
   the proof of Lemma 1(b) of `rips-segev-witness-supports-carry-no-zero-divisors`, with the one-letter correction
   `b^{-1}` replaced by the one-syllable correction `a^{-x}`.
2. *Port system.*  Split `alpha` along left `<a>`-cosets: `alpha = sum_T h_T f_T(a)`.  Each coset carrying
   `alpha u` or `alpha w` is the coset of a unique line `i`.  Put `P_i = f_i u` and `Q_i = f_i w` in `k[t^{±1}]`.
   - Lemma 1(a)-(c) of the witness node turn `alpha u = - alpha w b` into three conditions:
     `supp P_i ⊆ In_i`, `supp Q_i ⊆ Out_i`, and `Q_l(m) = - P_i(p)` along each `b`-edge
     `v_{l,m} -> v_{i,p}`.
3. *Two active lines.*  A same-line `b`-edge would close a cycle `b a^x` of free-product length `2 < gamma`.  So
   some line `j != i` is active too.
4. *Commutation.*  `P_i w = f_i u w = Q_i u`, hence `P_i Q_j = P_j Q_i`.
5. *Row separation.*  Distinct lines have distinct rows, and `min Dist_j^+ = 10^{5r_j - 4} > 10^{5r_i} = C_i`
   for `r_i < r_j`.  So sums of row-`i` and row-`j` positions decompose uniquely.  There is no cancellation, and
   `supp P_i + supp Q_j = supp P_j + supp Q_i`.
   - Projecting to each row gives `supp P_i = supp Q_i ⊆ In_i ∩ Out_i = {0, C_i}`.
6. *Contradiction.*  `Q_i != 0` at `0` (resp. `C`) sends the `x_1`-edge (resp. `x_2`-edge) to position `I_1`
   (resp. `I_2`) of an active line `k`.  There `P_k != 0`, contradicting `supp P_k ⊆ {0, C_k}`.

**Scope.**
- The same proof works for any generalized Rips--Segev graph with `Gr'_*(1/8)` that satisfies three conditions:
  - `In_i ∩ Out_i ⊆ {0, C_i}`;
  - the `b`-edges leaving `0` and `C` land at interior target positions;
  - the lines carry pairwise separated position sets, so that sums decompose uniquely.
- Row separation is essential.  If all lines share one position set, the port system of `Gamma` does have
  solutions: `f_i = 1`, `u = P` arbitrary on `In`, and `w = Q` with
  `Q(0) = -P(I_1)`, `Q(C) = -P(I_2)`, `Q(O_1) = -P(C)`, `Q(O_2) = -P(0)`.
- This is the coefficient contradiction that `rips-segev-port-data-cannot-exclude-balanced-divisors` says the
  balanced case needs.  It covers every support `S`, including the silent 12-point `S` at which the support method
  stops.

**What remains.**
- A genuine relation must spread over several translates of `g(V(Gamma))`, which are glued along relator arcs
  like a van Kampen diagram.
- Next step: run the same commutation-and-separation argument across two translates `h g(V)` and `h' g(V)` meeting
  along a piece.  The port identities there couple lines of different copies.

**Calibration.**  `experiments/rips-segev-one-copy-2026-09-18/one_copy_ports.py`, output in `ports_results.txt`:
- *Part 1.*  Exhaustive over all 3375 support classes of rows 1..6 of Steenbock's table.  It checks unique
  decomposition and "equal sumsets imply supports in `{0, C}`" (step 5).
- *Part 2.*  The full linear system over `F_10007` for a scaled 4-line model, with 1363 unknowns (coefficients of
  the `f_i`).
  - With separated rows the nullity is 0 for all 7 pairs `(u, w)`.  These include the port-table pair and four
    random pairs on 12-point supports.
  - The degenerate one-row control has nullity 1 for the port-table pair, which is the solution `f_i = 1`.
