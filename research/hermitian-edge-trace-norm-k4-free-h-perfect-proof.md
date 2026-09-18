---
rg: 2
id: hermitian-edge-trace-norm-k4-free-h-perfect-proof
kind: route
title: The exact odd-cycle minimum 2cot(pi/2n) from gauge, shift-averaging and a concavity breakpoint, plus chord splitting, puts the threshold vector in STAB for K4-free h-perfect graphs
target: hermitian-edge-trace-norm-k4-free-h-perfect
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-2026-09-18/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane w6-078, 2026-09-18. The numerical checks are in
`experiments/hermitian-edge-trace-norm-2026-09-18/` (`cycle_check.py`, `facet_min.py`).

## Setting

`G` is a finite graph on `V = [N]`. A matrix `C` is **admissible for `G`** if it is Hermitian with
`C_ii = 0`, `C_ij = 0` for non-edges, and `|C_ij| >= 1` for edges. For `w >= 0` put `W = sum w_i`,
`alpha_w(G) = max_I w(I)` over independent sets `I`, and `D = diag(sqrt w)`. The inequality is

```text
(**)     || D C D ||_1  >=  sqrt3 ( W - alpha_w(G) ) .
```

For `S ⊆ V`, `C_S` and `Q_S` denote principal submatrices. If `C` is admissible for `G` then `C_S`
is admissible for the induced subgraph `G[S]`.

## Step 0. The dual form and the threshold vector

**Lemma 0.** (a) If `Q` is Hermitian with `Q + C >= 0` and `Q - C >= 0`, then `Q >= 0` and
`sum_i w_i Q_ii >= ||DCD||_1` for every `w >= 0`. (b) If `w > 0`, equality is attained by
`Q = D^(-1) |DCD| D^(-1)`.

*Proof.* (a) `Q = ((Q+C) + (Q-C))/2 >= 0`. Congruence by `D` gives `DQD +- DCD >= 0`. For Hermitian
`M` and `X >= +-M`, `tr X >= ||M||_1`: write `M = M_+ - M_-` with `P_+` the projection onto the
positive part. Then `tr X >= tr(P_+ X) + tr((1-P_+) X) >= tr M_+ + tr M_-`. So
`sum w_i Q_ii = tr DQD >= ||DCD||_1`. (b) `|DCD| +- DCD >= 0`; conjugate back by `D^(-1)`. ∎

**Lemma 0'.** Fix `G`. Suppose that for every admissible `C` and every `Q` with `Q +- C >= 0`, the
vector `y = (1 - Q_ii/sqrt3)_i` satisfies `y_+ in STAB(G)`. Then (**) holds for `G` and all `w >= 0`.
(The converse also holds, by Lemma 0(a): `sum w_i y_i <= alpha_w` for all `w >= 0` forces `y_+ in STAB`.)

*Proof.* Both sides of (**) are continuous in `w`, so take `w > 0`. Take `Q` from Lemma 0(b). Then
`||DCD||_1 = sum w_i Q_ii = sqrt3 (W - sum w_i y_i) >= sqrt3 (W - sum w_i (y_i)_+) >= sqrt3 (W - alpha_w)`,
because `y_+ in STAB(G)` and `w >= 0` give `w . y_+ <= alpha_w`. ∎

Since `Q >= 0`, always `y_i <= 1`. Write `q_i = Q_ii` and `T(y) = {i : y_i > 0} = {i : q_i < sqrt3}`.

## Step 1. Edges

**Lemma 1.** If `ij` is an edge and `y_i, y_j > 0`, then `y_i + y_j <= 2 - 2/sqrt3 < 1`.

*Proof.* The `2x2` principal minors of `Q +- C` give `q_i q_j >= |Q_ij +- C_ij|^2`, and
`max_+- |Q_ij +- C_ij| >= |C_ij| >= 1`. So `q_i + q_j >= 2 sqrt(q_i q_j) >= 2`. ∎

## Step 2. The exact odd-cycle minimum

**Theorem 2.** Let `n >= 3` be odd and let `C` be admissible for the cycle `C_n` (support exactly
on the `n` cycle edges). Then

```text
||C||_1  >=  2 cot(pi/(2n)) ,
```

and equality is attained when all moduli equal `1` and the flux is `Phi ≡ n pi/2 (mod pi)`
(Step 2.4). Moreover `2 cot(pi/(2n)) >= sqrt3 (n+1)/2`,
with equality only at `n = 3`.

Label the vertices `0, ..., n-1` cyclically and write `C_(j,j+1) = c_j e^(i theta_j)` with
`c_j >= 1` (indices mod `n`).

**2.1 Gauge.** For a diagonal unitary `U = diag(e^(i phi_j))`, `U C U^*` has entries
`c_j e^(i(theta_j + phi_j - phi_(j+1)))` and the same trace norm. Only the flux
`Phi = sum_j theta_j (mod 2 pi)` is invariant. Solving `phi_(j+1) = phi_j + theta_j - Phi/n` (consistent
around the cycle because the increments sum to `0`) makes every edge phase equal to `Phi/n`.
So `C` is unitarily equivalent to `C(c, Phi)`, the matrix with `(j, j+1)` entry `c_j e^(i Phi/n)`.

**2.2 Shift averaging.** Fix `Phi`. The map `c -> ||C(c, Phi)||_1` is convex on `R^n`, because
`C(c, Phi)` is linear in `c` and the trace norm is a norm. Let `P` be the cyclic permutation
matrix `e_j -> e_(j+1)`. Then `P C(c, Phi) P^T = C(sigma c, Phi)`, where `sigma` shifts the
coordinates cyclically: the edge `(j, j+1)` goes to `(j+1, j+2)` with the same phase `Phi/n`. So the
function is `sigma`-invariant. By convexity, with `cbar = (1/n) sum c_j >= 1`,

```text
||C(c,Phi)||_1  >=  || C(cbar 1, Phi) ||_1  =  cbar || C(1, Phi) ||_1  >=  || C(1, Phi) ||_1 .
```

**2.3 Spectrum.** `C(1, Phi) = e^(i Phi/n) S + e^(-i Phi/n) S^*` with `S` the cyclic shift. `S`
has eigenvalues `e^(2 pi i k/n)`, `k = 0..n-1`, with common eigenvectors (Fourier). So the eigenvalues of
`C(1,Phi)` are `2 cos((Phi + 2 pi k)/n)`, and

```text
||C(1,Phi)||_1 = 2 sum_(k=0)^(n-1) |cos(x + 2 pi k/n)| ,      x = Phi/n .
```

**2.4 Odd n: the breakpoint minimum.** `|cos|` has period `pi`. Since `n` is odd, `2` is invertible
mod `n`, so the residues `2k mod n` run over `0..n-1`. Hence `{2 pi k/n mod pi} = {pi j/n : j = 0..n-1}`
and `||C(1,Phi)||_1 = 2 g(x)` with

```text
g(x) = sum_(j=0)^(n-1) |cos(x + j pi/n)| .
```

`g` has period `pi/n`. Its breakpoints are the zeros of the summands, i.e. `x ≡ pi/2 (mod pi/n)`. Between
two consecutive breakpoints the signs `eps_j` are constant and
`g(x) = Re( e^(ix) sum_j eps_j e^(i j pi/n) ) = R cos(x + psi)` for constants `R >= 0` and `psi`.
Here `g > 0` everywhere, since the summands cannot all vanish. A function `R cos(x + psi)` that is
positive on an interval is concave there. So `g` is concave on each closed interval between breakpoints,
and its minimum is attained at a breakpoint, where by periodicity `g = g(pi/2)`:

```text
g(pi/2) = sum_(j=0)^(n-1) sin(j pi/n) = Im (1 - e^(i pi)) / (1 - e^(i pi/n)) = cot(pi/(2n)) .
```

(For `theta = pi/n`: `2/(1 - e^(i theta)) = (sin(theta/2) + i cos(theta/2))/sin(theta/2)`.)
Combining 2.1 to 2.4, `||C||_1 >= 2 min_x g(x) = 2 cot(pi/(2n))`. Equality holds at `c = 1`,
`Phi/n ≡ pi/2 (mod pi/n)`, i.e. `Phi ≡ n pi/2 (mod pi)`.
For `n = 3` this is the triangle case (`2 cot(pi/6) = 2 sqrt3`, flux `pi/2`, eigenvalues `+-sqrt3, 0`),
matching the previously known equality case.

**2.5 Comparison with sqrt3 (n+1)/2.** `n = 3`: `2 sqrt3 = sqrt3 * 2` (equality). `n = 5`:
`2 cot(pi/10) = 6.1554 > 5.1962`. For `n >= 7`: `tan` is convex on `[0, pi/2)` with `tan 0 = 0` and
`tan(pi/4) = 1`, so `tan t <= 4t/pi` on `[0, pi/4]`. With `t = pi/(2n)` this gives
`2 cot(pi/(2n)) >= n`, and `n >= sqrt3 (n+1)/2` iff `n >= sqrt3/(2 - sqrt3) = 6.46`. ∎

Asymptotically `2 cot(pi/(2n)) ~ 4n/pi`, so the ratio to the needed `sqrt3 (n+1)/2` tends to
`8/(sqrt3 pi) = 1.470`.

**Corollary 2'.** For odd `n >= 3`, admissible `C` on `C_n` and `Q +- C >= 0`:
`sum_(i in C_n) q_i >= 2 cot(pi/(2n)) >= sqrt3 (n+1)/2`, hence `sum_i y_i <= n - (n+1)/2 = (n-1)/2`.
(Apply Lemma 0(a) with `w = 1`.)

## Step 3. Induced odd cycles with partial support

**Lemma 3.** Let `H` be an induced odd cycle of `G` with vertex set `S`, `|S| = n >= 3` odd. Then
`sum_(i in S) (y_i)_+ <= (n-1)/2`.

*Proof.* Let `U = S ∩ T(y)`. If `U = S`: `C_S` is admissible for `G[S] = C_n` (the cycle is induced,
so `C_S` is supported exactly on the cycle edges), and `Q_S +- C_S >= 0`. Corollary 2' gives the
claim. If `U` is empty the claim is trivial. If `∅ ≠ U ⊊ S`: `G[U]` is a disjoint union of `p >= 1` paths with `k_1, ..., k_p` vertices, and
consecutive paths are separated by at least one vertex of `S \ U`, so `sum k_l <= n - p`. Cover a path
on `k` vertices by `floor(k/2)` disjoint edges plus at most one vertex. Lemma 1 (each edge contributes
`< 1`) and `y_i <= 1` give `sum_(i in U) y_i <= sum_l ceil(k_l/2) <= (sum k_l + p)/2 <= n/2`. The left
side is at most an integer bound `sum_l ceil(k_l/2)` that is `<= n/2`, and `n` is odd, so it is
`<= (n-1)/2`. ∎

## Step 4. Chord splitting

**Lemma 4.** Let `z in [0,1]^V` satisfy `z_i + z_j <= 1` on every edge and
`z(V(H)) <= (|H|-1)/2` for every **induced** odd cycle `H` of length `>= 5`, and let
`z(K) <= 1` for every triangle `K`. Then `z(V(H)) <= (|H|-1)/2` for every odd cycle `H` of `G`.

*Proof.* Induction on `|H|`. If `|H| = 3`, `H` is a triangle. If `H` is induced, it is a hypothesis.
Otherwise `H` has a chord `uv`, which splits `H` into two cycles through `u, v`. Their lengths add
up to `|H| + 2`, which is odd, so exactly one of them, `H_1`, is odd, and `|H_1| < |H|`. The vertices
of `H` not on `H_1` form a path of `|H| - |H_1|` vertices (an even number), which has a perfect
matching `M`. Then `z(V(H)) = z(V(H_1)) + sum_(e in M) z(e) <= (|H_1| - 1)/2 + (|H| - |H_1|)/2 = (|H|-1)/2`. ∎

## Step 5. The theorem

Recall: `G` is **h-perfect** if `STAB(G)` is cut out by `x >= 0`, the clique inequalities
`x(K) <= 1` and the odd-cycle inequalities `x(V(H)) <= (|H|-1)/2` for all odd cycles `H`. It is
**t-perfect** if the edge inequalities suffice in place of the clique inequalities. Perfect graphs and
t-perfect graphs are h-perfect. Bipartite graphs, odd cycles, series-parallel graphs (Boulala–Uhry
1979), odd-`K_4`-free graphs (Gerards–Shepherd 1998), and many more, are t-perfect. `K_4` is not
t-perfect, and every t-perfect graph is `K_4`-free.

**Theorem 5.** (a) (**) holds, for all `w >= 0` and all admissible `C`, for every h-perfect graph
`G` with `omega(G) <= 3`. In particular it holds for every t-perfect graph, and for every `K_4`-free
perfect graph.

(b) More generally, let `G` be h-perfect and suppose the **uniform clique inequality**
`||C||_1 >= sqrt3 (m-1)` holds for every admissible `C` on `K_m`, for all `m <= omega(G)`.
Then (**) holds for `G`. Conversely, (**) for `K_m` with `w = 1` is exactly the uniform clique inequality.
So (**) for all h-perfect graphs (or all perfect graphs) is equivalent to the uniform clique inequality for all `m`.

*Proof.* (b) By Lemma 0' it suffices to show `z = y_+ in STAB(G)`. We check the defining inequalities.
`z >= 0` and `z <= 1` are clear. *Cliques:* for a clique `K`, let `U = K ∩ T(y)`. If `|U| <= 1`,
`z(K) <= 1`. Otherwise `C_U` is admissible for `K_|U|` and `Q_U +- C_U >= 0`. So Lemma 0(a) and the
uniform clique inequality give `sum_(i in U) q_i >= sqrt3 (|U| - 1)`, i.e. `z(K) = sum_U y_i <= 1`.
*Odd cycles:* edges and triangles are cliques, handled above. Induced odd cycles of length `>= 5`
are handled by Lemma 3. Lemma 4 then gives all odd-cycle inequalities. Since `G` is h-perfect,
`z in STAB(G)`.

(a) The uniform clique inequality holds for `m = 2` (`||C||_1 = 2|C_12| >= 2 >= sqrt3`) and for
`m = 3` (the triangle case: `tr C = 0` gives `||C||_1 >= sqrt2 ||C||_F >= sqrt2 sqrt6 = 2 sqrt3`).
So (b) applies whenever `omega(G) <= 3`. ∎

## Step 6. The facet reduction for general graphs

**Proposition 6.** (**) holds for `G` (all `w`) iff it holds at `(G[S], a)` for every `S ⊆ V` and
every nontrivial facet normal `a` of `STAB(G[S])` with full support `S`. Here "nontrivial" means other
than `x_i >= 0`, so that `a > 0` on `S`, and "at `(H, a)`" means for the single weight `w = a`.

*Proof.* (⇒) Given `C'` admissible for `G[S]`, extend it by `1` on the other edges of `G`, and put
`w = a` on `S` and `0` elsewhere. Then `DCD` is `D_a C' D_a` padded by zeros and `alpha_w(G) = alpha_a(G[S])`.

(⇐) By Lemma 0' it suffices to show `y|_T in STAB(G[T])`, where `T = T(y)`. `y|_T > 0`, so we need
`a . y|_T <= alpha_a(G[T])` for every nontrivial facet normal `a` of `STAB(G[T])`. Let `S = supp(a)`.
By Padberg's restriction lemma (a facet of `STAB(H)` with support `S` restricts to a facet of
`STAB(H[S])`; proof: otherwise `a|_S . x <= alpha` is a nonnegative combination of other valid
inequalities of `STAB(H[S])`, which stay valid for `STAB(H)`, and a facet inequality of a full-dimensional
polytope cannot be such a combination), `a|_S` is a full-support facet normal of `STAB(G[S])`. `C_S` is
admissible for `G[S]` and `Q_S +- C_S >= 0`. So Lemma 0(a) and (**) at `(G[S], a|_S)` give
`sum_S a_i q_i >= sqrt3 (a(S) - alpha_a(G[S]))`, which is `a . y <= alpha_a(G[S]) = alpha_a(G[T])`. ∎

**Consequences.**
- `STAB(K_m)` has a single nontrivial facet, `x(V) <= 1`, and induced subgraphs of cliques are cliques.
  So (**) for `K_m` with all weights is equivalent to the uniform clique inequality for `K_s`, `s <= m`.
- For each facet `(H, a)` of full support, (**) at `(H, a)` is a single-weight statement. The facets
  are cliques (`H = K_m`, `a = 1`), odd holes (`H = C_n`, `a = 1`, done by Theorem 2), and the rest
  (odd antiholes, webs, wheels with lifted hub weight, ...). So general (**) is equivalent to the
  uniform clique inequality **plus** (**) at every full-support facet of STAB that is neither a clique
  nor an odd hole. This is the decomposition in `hermitian-edge-trace-norm-via-stab-facets`.

## Numerical checks

`experiments/hermitian-edge-trace-norm-2026-09-18/cycle_check.py`: for `n = 3, ..., 13` the flux scan,
random admissible matrices (20000 each) and L-BFGS-B minimization over moduli and phases all give
`min ||C||_1 = 2 cot(pi/(2n))` to 6 digits, and never less. `facet_min.py`: at the non-clique,
non-hole facets `C̄_7, C̄_9` (antiholes), wheels `W_5, W_7` (hub weights `2, 3`), webs
`C_8^2, C_11^3, C_7^2, C_10^3`, local minima of `||D_a C D_a||_1 / (sqrt3 (a(V) - alpha_a))` are all `>= 1.108`.
