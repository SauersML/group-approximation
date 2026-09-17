---
rg: 2
id: sl3z-racg-witnesses-are-antiflag-configurations-proof
kind: route
title: Twisting to reflections, integrality, and abelian transvection radicals
target: sl3z-racg-witnesses-are-antiflag-configurations
requires:
  - two-dimensional-coxeter-coherence-criterion
---

Throughout, `U_p = {I + p mu^T : mu(p) = 0}` is the group of transvections
with centre `p`. It is abelian, because
`(I + p mu^T)(I + p nu^T) = I + p (mu + nu)^T + p (mu·p) nu^T = I + p (mu + nu)^T`.
Dually, `U^L = {I + x L^T : L(x) = 0}` is abelian.

`W` has trivial centre. A central element of a right-angled Coxeter group is
a product of generators adjacent to every other vertex, and there are none.

1. **Twist.** Each `rho(s_v)` is an involution in `GL_3(Z)`. It is not `±I`:
   `rho` is injective and `s_v` is not central. So one of the eigenspaces
   `E_{-1}`, `E_{+1}` is a line and the other is a plane. Put `eps(s_v) = 1`
   if `E_{-1}` is the line, and `eps(s_v) = -1` otherwise. Every relator of
   `W` has even length in each generator, so `eps` extends to a character.
   `rho' = eps rho` is a homomorphism, and every `rho'(s_v)` is a reflection.

   Suppose `rho'(g) = I`. Then `rho(g) = ±I`, so `g` lies in `rho^{-1}({±I})`.
   That subgroup is normal of order at most two, hence central, hence trivial.
   So `rho'` is injective.

2. **Integrality.** A reflection `s in GL_3(Z)` has a rational `(-1)`-line,
   spanned by a primitive `p`, and a rational fixed plane `ker L` with `L`
   primitive. So `s = I - p beta^T` with `beta = c L` and `beta(p) = 2`, which
   gives `c = 2/d` with `d = L·p != 0`. Choose the sign of `L` so that `d > 0`.
   The matrix `p L^T` has coprime entries, since `p` and `L` are primitive.
   `(2/d) p L^T` is integral, so `d` divides `2`.

   `[p]` and `[L]` determine `s`. So (A1) is equivalent to injectivity on
   generators.

3. **Commutation (A2).** Suppose `s_u s_v = s_v s_u` with `u != v`. Then `s_u`
   preserves `E_{-1}(s_v) = [p_v]`, so either `s_u p_v = p_v`, that is
   `L_u·p_v = 0`, or `[p_v] = [p_u]`.

   In the second case `s_u` preserves `ker L_v`, which does not contain `p_u`.
   So `s_u` acts on `ker L_v` without eigenvalue `-1`, and fixes it
   pointwise. Hence `ker L_v = ker L_u` and `s_u = s_v`, contradicting (A1).

   So `L_u·p_v = 0`, and symmetrically `L_v·p_u = 0`. Conversely, mutual
   incidence gives a common eigenbasis `p_u, p_v, r` with `r` spanning
   `ker L_u cap ker L_v`, so the reflections commute. In `W`, `s_u` and `s_v`
   commute exactly when `u ~ v`, which proves (A2).

4. **Non-edges (A3).** Suppose `u` and `v` are not adjacent, so `s_u s_v` has
   infinite order in `W`, and hence also under `rho'`.
   - If `[p_u] != [p_v]` and `[L_u] != [L_v]`, then `s_u s_v` fixes the line
     `ker L_u cap ker L_v` and acts on `R^3 / (that line)` with trace
     `a_uv a_vu - 2` and determinant `1`. Finite order with integral trace
     would need `a_uv a_vu - 2` in `{-2, -1, 0, 1}` and diagonalizability.
     The value `-2` occurs, with `a_uv a_vu = 0`, as `-I` on the quotient when
     both entries vanish; that case is the commuting case of step 3 and is
     excluded. When only one entry vanishes, the element is `-`(a nontrivial
     unipotent), of infinite order. The values `a_uv a_vu` in `{1, 2, 3}`
     give finite order (`3`, `4`, `6`) and are excluded.
   - If `[p_u] = [p_v]` or `[L_u] = [L_v]`, the product is a nontrivial
     transvection (see step 5), of infinite order.

   The converse holds: any anti-flags satisfying (A2) give a homomorphism,
   because the defining relators hold. Coherence consequence: for
   triangle-free `Gamma`, `W_Gamma` is a two-dimensional Coxeter group. By
   the cited criterion it is incoherent when some induced `Lambda` has
   `chi(W_Lambda) > 0`. An incoherent group containing a finite-index
   subgroup inside `SL_3(Z)` makes that subgroup incoherent, and so makes
   `SL_3(Z)` incoherent.

5. **Shared centre gives a transvection.** Suppose `p_u = p_w = p`, choosing
   signs so that the centre vectors agree, with `beta_u(p) = beta_w(p) = 2`.
   Then
   `s_u s_w = (I - p beta_u^T)(I - p beta_w^T) = I - p beta_u^T - p beta_w^T + 2 p beta_w^T = I + p lambda^T`
   with `lambda = beta_w - beta_u`. So `lambda(p) = 0` and `lambda != 0`,
   because `s_u != s_w`. Hence `T = s_u s_w` lies in `U_p \ {I}`, and `u`,
   `w` are not adjacent. The dual statement for a shared axis follows by
   applying the contragredient `g -> g^{-T}`, which exchanges centres and
   axes.

6. **Rule (R1).** Suppose `u`, `w`, `c` share the centre `p`. They are
   pairwise non-adjacent by step 5, so they generate
   `Z/2 * Z/2 * Z/2 <= W`, a special subgroup. `s_c p = -p`, so
   `s_c T s_c = I - p (s_c^T lambda)^T` lies in `U_p`, and it commutes with `T`.

   In `W` the commutator `[s_u s_w, s_c s_u s_w s_c]` is the word
   `u w c u w c w u c w u c`. It has no two equal adjacent letters, so it is
   a reduced nontrivial word in the free product. That is a kernel element,
   a contradiction. Axes follow by duality.

7. **Rule (R2).** Suppose `p_u = p_w = p`, and let `x != u, w` have
   `L_x·p = 0`. Then `s_x p = p` and `s_x T s_x = I + p (s_x^T lambda)^T` lies
   in `U_p`, so `rho'([T, s_x T s_x]) = I`. If `x` is adjacent to both `u` and
   `w`, the commutator is trivial in `W`. Otherwise the special subgroup
   `<u, w, x>` is one of three groups, and the word
   `u w x u w x w u x w u x` is nontrivial in each:
   - `Z/2 * Z/2 * Z/2`: the word is reduced;
   - `x ~ u` only: the group is `(Z/2 × Z/2) * Z/2` with factors `<u, x>` and
     `<w>`. The syllables are `u | w | xu | w | x | w | ux | w | ux`, all
     nontrivial and alternating;
   - `x ~ w` only: the factors are `<w, x>` and `<u>`, with syllables
     `u | wx | u | wxw = x | u | xw | u | x`, all nontrivial and alternating.

   Each case gives a kernel element, a contradiction. (R3) is the dual
   statement.

8. **Rule (R4).** Take the induced 4-cycle `v – u_1 – w – u_2 – v`. By (A2),
   `p_{u_1}` and `p_{u_2}` lie on `L_v` and on `L_w`, while `p_v` and `p_w`
   lie on `L_{u_1}` and on `L_{u_2}`.
   - Suppose `[L_v] != [L_w]`. The two lines meet in one point, so
     `[p_{u_1}] = [p_{u_2}]`. By (A1) this forces `[L_{u_1}] != [L_{u_2}]`, so
     those two lines also meet in one point, giving `[p_v] = [p_w]`.
   - Otherwise `[L_v] = [L_w]`. Then (A1) gives `[p_v] != [p_w]`, so the two
     points span a unique line, giving `[L_{u_1}] = [L_{u_2}]`.

   The two alternatives exclude each other: in the first, the axes `L_v`,
   `L_w` differ.

   In the centre case, put `T_1 = s_{u_1} s_{u_2} = I + p lambda^T`. Here
   `lambda` vanishes on `p` by step 5, and on `q = p_v` because `q` lies on
   both `L_{u_1}` and `L_{u_2}`. Also `q != p`, since `p` lies on `L_v` and
   `q` does not. So `lambda` is proportional to the line `pq`. Symmetrically,
   `T_2 = s_v s_w = I + q mu^T` with `mu` proportional to `pq`. Both lie in
   `U^{pq}`, with linearly independent translation vectors `p` and `q`.

   Finally, no shared centre and no shared axis implies no induced 4-cycle,
   so `W` is hyperbolic by Moussong's theorem.

9. **Rule (R5).** Call an induced square *of centre type* or *of axis type*
   according to the alternative in step 8. Let `x` be a vertex, and let `Q`
   and `Q'` be two centre-type squares through `x`, with opposite vertices
   `y` and `y'`.
   - If `y != y'`, then `p_x = p_y = p_{y'}`, three vertices share a centre,
     and (R1) is violated.
   - If `y = y'`, the squares `Q` and `Q'` are formed from common neighbours
     of `x` and `y`. There are at most two such neighbours, because `Gamma` is
     `K_{2,3}`-free, so `Q = Q'`.

   The same argument applies to axis type. So `x` lies in at most one square
   of each type.

   **The graphs.** Steps 1–9 use only linear algebra over `R`, so the rules
   hold for faithful reflection representations in `GL_3(R)`. Step 1 needs
   that every involution other than `±I` is plus or minus a reflection, and
   this holds over `R`.
   - In `C_m □ C_n` with `m, n >= 4`, a vertex lies in four squares.
   - In `Q_4` a vertex lies in six squares.
   - In the Clebsch graph (5-regular, 16 vertices, any two non-adjacent
     vertices with exactly two common neighbours), a vertex lies in ten
     squares.

   All three graphs are triangle-free and `K_{2,3}`-free. Their Euler
   characteristics `1 - V/2 + E/4` are:
   - `1 - mn/2 + 2mn/4 = 1` for the grid;
   - `1 - 8 + 8 = 1` for `Q_4`;
   - `1 - 8 + 10 = 3` for the Clebsch graph.

10. **Rule (R6).** Suppose `p_u = p_w = p` with `u != w`. Every neighbour `x`
    of `u` has `L_x·p = L_x·p_u = 0`, and `x != w` because vertices with a
    shared centre are not adjacent (step 5). By (R2), `x` is adjacent to `w`.
    So `u` and `w` have at least `deg u >= 2` common neighbours, which gives a
    4-cycle and contradicts girth at least 5. The axis statement
    is the dual, using (R3). Incidence along edges is (A2).
