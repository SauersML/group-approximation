---
rg: 2
id: rips-segev-one-copy-configurations-carry-no-zero-divisors-proof
kind: route
title: Exact encoding turns a one-copy relation into line ports P_i = f_i u, Q_i = f_i w matched along b-edges; P_i Q_j = P_j Q_i with uniquely decomposing row sums forces supp P_i = supp Q_i inside {0, C_i}, and the x_1/x_2 edges from 0 and C then hit forbidden ports
target: rips-segev-one-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-witness-supports-carry-no-zero-divisors]
---

**Conventions.**
- [EE] is `rips-segev-witness-supports-carry-no-zero-divisors-proof`.  Its Lemma 1 gives:
  - (a) `g` is injective on `V(Gamma)`;
  - (b) `g(v) b != g(u)` for hanging `v`, meaning `v` has no outgoing `b`-edge, and any vertex `u`.
- `g(v_{i,p}) = g(v_{i,0}) a^p`, and a `b`-edge `v' -> v` gives `g(v) = g(v') b`.
- In Steenbock's gluing (row `r = phi(i)`), `b`-edges leave the positions `0, C, O_1, O_2` by `x_1, x_2, x_3, x_4`
  and arrive at `I_1, I_2, C, 0` respectively.
  - Each distinguished position is the source of exactly one `b`-edge if it lies in `Out_i = {0, O_1, O_2, C}`.
  - It is the target of exactly one `b`-edge if it lies in `In_i = {0, I_1, I_2, C}`.
- `gamma >= 42` is the least free-product length of a cycle label.

## 1. Cosets meet one line

**Lemma 1.**  If `v, v'` are vertices, `x != 0` and `g(v) a^x = g(v')`, then `v = v_{i,p}` and
`v' = v_{i,p+x}` for one line `i`.

*Proof.*  Run the proof of [EE] Lemma 1(b) with the boundary edge `e` labelled `a^{-x}` instead of `b^{-1}`.
- The diagrams there are over the free product, and the proof uses only two facts about `e`: it is a single
  boundary edge, and its label is one nontrivial factor element, of free-product length 1.
- So the cases "more than two faces", "one face" and "two faces" go through verbatim.  In each, the face avoiding
  `e` has a long exterior arc inside `q̄` that is a piece, which is absurd.  The one-face case with `e ∈ ∂M`
  still gives `gamma < 1/(1 - lambda) < 2`.
- Only the case `|D| = 0` changes.
  - Then `omega(q) = a^x` in `F = G_1 * G_2`, and `q` is backtrack-free, so `omega(q)` is freely reduced in
    `a^{±1}, b^{±1}`.
  - Its syllables are nonzero powers, which are nontrivial since `a, b` have infinite order.  By the normal form
    in `F`, `omega(q)` is the single syllable `a^x`: `|x|` consecutive `a`-edges in one direction.
  - The `a`-edges of `Gamma` are exactly the edges of the lines, and at each vertex there is at most one `a`-edge in
    and one out.  So `q` runs along one line from `v` to `v'` at distance `x`. ∎

**Consequence.**  A left coset `T = h<a>` meeting `g(V)` meets it in exactly `g(line i) = g(v_{i,0}) a^{[0, C_i]}`
for a unique `i`.  Distinct such cosets give distinct lines, and vice versa.

## 2. The port system

Let `alpha (u + w b) = 0` with `alpha != 0`, `w != 0`, and suppose
`supp(alpha u) ∪ supp(alpha w) ⊆ h g(V)`.
- Replace `alpha` by `h^{-1} alpha`, so `h = 1`.
- Put `X = alpha u` and `Y = alpha w`.  Then `X = - Y b`, that is `X(z) = - Y(z b^{-1})` for all `z`.
- Write `alpha = sum_T alpha_T` over left `<a>`-cosets `T`.  Since `u, w in k[<a>]`, `alpha_T u` and
  `alpha_T w` are supported in `T`.
- `k[<a>] = k[t^{±1}]` is a domain.  So `alpha_T != 0` implies `alpha_T w != 0`, and `T` meets `supp Y ⊆ g(V)`.
  In particular `alpha ∈ k[K]`, even if it was given in `k[G]`.
- By §1, such `T` is the coset of a unique line `i`.  Write `alpha_T = g(v_{i,0}) f_i(a)`, and put `f_i = 0` for
  the other lines.  Define `P_i = f_i u` and `Q_i = f_i w`, so that `X(g(v_{i,p})) = P_i(p)` and
  `Y(g(v_{i,p})) = Q_i(p)`.

**Lemma 2.**  (i) `supp Q_i ⊆ Out_i`.  (ii) `supp P_i ⊆ In_i`.  (iii) `Q_l(m) = - P_i(p)` for every `b`-edge
`v_{l,m} -> v_{i,p}`.

*Proof.*
- (i) Let `Y(g(v')) != 0`.  Then `X(g(v') b) = - Y(g(v')) != 0`, so `g(v') b = g(v)` for some vertex `v`.
  - By [EE] 1(b), `v'` is not hanging.  So it has a `b`-edge `v' -> v''`, and `g(v'') = g(v') b = g(v)`.
  - Then `v'' = v` by [EE] 1(a).  So `v'` is a source, and its position lies in `Out`.
- (ii) Let `X(g(v)) != 0`.  Then `Y(g(v) b^{-1}) != 0`, so `g(v) b^{-1} = g(v')` with `v' ∈ V`.  By the proof
  of (i), `v' -> v` is a `b`-edge, so `v` is a target.
- (iii) This is `X = - Y b` evaluated at `g(v_{i,p}) = g(v_{l,m}) b`. ∎

Call line `i` *active* if `f_i != 0`.

**Lemma 3.**  `u != 0`, and there are two distinct active lines.  For every active `i`, `P_i != 0` and
`Q_i != 0`.

*Proof.*
- Take an active `i`.  Then `Q_i = f_i w != 0`.  Pick `m ∈ supp Q_i ⊆ Out_i` and its `b`-edge
  `v_{i,m} -> v_{k,p}`.
- By (iii), `P_k(p) != 0`, so `u != 0` and `k` is active.
- If `k = i`, the edge and the segment of line `i` from `p` back to `m` form a cycle.  Its label is `b` (if
  `p = m`) or `b a^{m-p}`, of free-product length `<= 2 < gamma`.  So `k != i`.
- Finally `P_j = f_j u != 0` for every active `j`. ∎

## 3. Commutation and row separation

**Lemma 4.**  `P_i Q_j = P_j Q_i` in `k[t^{±1}]` for all `i, j`.

*Proof.*  `P_i Q_j = f_i f_j u w = P_j Q_i`. ∎

**Lemma 5.**  Let `i != j` with `r_i < r_j`, and let `D_i = {0, I_1, I_2, O_1, O_2, C}` for line `i`.  Then
`(x, y) -> x + y` is injective on `D_i × D_j`.

*Proof.*
- If `x + y = x' + y'` with `y != y'`, then `|y - y'| >= min Dist_j^+ = 10^{5 r_j - 4}`.
- On the other hand `|x - x'| <= C_i = 10^{5 r_i} <= 10^{5 r_j - 5}`.  That is a contradiction.
- So `y = y'` and `x = x'`. ∎

**Lemma 6.**  For every active `i`, `supp P_i = supp Q_i ⊆ {0, C_i}`.

*Proof.*
- By Lemma 3 there is an active `j != i`.  `phi` is injective, so `r_i != r_j`; say `r_i < r_j` (the other case is
  symmetric).
- All four supports are nonempty and lie in `D_i` or `D_j`.  By Lemma 5 every monomial of `P_i Q_j` arises from
  a single pair, with coefficient `P_i(x) Q_j(y) != 0`.
- So `supp(P_i Q_j) = supp P_i + supp Q_j`, and likewise `supp(P_j Q_i) = supp Q_i + supp P_j`.
- By Lemma 4 these sets are equal.  Apply the row-`i` coordinate, which is well defined on `D_i + D_j` by
  Lemma 5.  This gives `supp P_i = supp Q_i`.
- With Lemma 2 this lies in `In_i ∩ Out_i = {0, C_i}`, since `I_1, I_2, O_1, O_2` are distinct and different
  from `0` and `C_i`. ∎

## 4. Conclusion

Take an active `i`.  By Lemmas 3 and 6, `Q_i` is nonzero at `0` or at `C_i`.
- If `Q_i(0) != 0`: the `b`-edge from `v_{i,0}` is `E(x_1)`, ending at `v_{k, I_1}`.  By (iii) `P_k(I_1) != 0`,
  so `k` is active and `I_1 ∈ supp P_k ⊆ {0, C_k}`.  This is absurd.
- If `Q_i(C_i) != 0`: the edge is `E(x_2)`, ending at `v_{k, I_2}`, and the same contradiction follows.

So no such `h` exists. ∎

**Generality.**  The proof uses only the following:
- `Gr'_*(1/8)`, through [EE] Lemma 1 and §1;
- `gamma > 2`;
- `In_i ∩ Out_i ⊆ {0, C_i}`;
- the edges leaving `0` and `C` land at targets outside `{0, C}`;
- pairwise unique decomposition of the position sets of distinct lines.

**Control.**  Drop the last hypothesis and let all lines have positions `0 < 1 < 2 < 3 < 4 < 5`.  Then `f_i = 1`,
`u = P` and `w = Q` with `Q(0) = -P(1)`, `Q(5) = -P(2)`, `Q(3) = -P(5)`, `Q(4) = -P(0)` solve Lemma 2(i)-(iii).
The script finds this solution (nullity 1) and nothing in the separated model (nullity 0).

## 5. Computation

`experiments/rips-segev-one-copy-2026-09-18/one_copy_ports.py`, output in `ports_results.txt` (seed 1, 8 s):
- *Part 1* checks Lemmas 5 and 6 exhaustively for rows 1..6 of Steenbock's table (3375 support classes).
- *Part 2* solves Lemma 2(i)-(iii) over `F_10007` for a 4-line model with random fixed-point-free `x_1, ..., x_4`
  (1363 unknowns).
  - With separated rows (scale `6^{r-1}`), the nullity is 0 for 7 pairs `(u, w)`: the port-table pair, `(1, 1)`,
    `(1 + t, 1 - t)`, and four random pairs on 12-point supports.
  - With degenerate rows, the port-table pair has nullity 1.
