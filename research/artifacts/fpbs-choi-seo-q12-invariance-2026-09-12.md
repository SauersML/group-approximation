# Choi–Seo Question 1.2: comparing thresholds across generating sets

Lane `bs-choi-seo-q12-invariance`, 2026-09-12.

Choi–Seo arXiv:2508.08932v2, Question 1.2 (claim
`fpbs-nonuniqueness-phase-is-a-group-invariant`): is the existence of a
nonuniqueness phase a group invariant? This note proves two things.

1. **A two-sided comparison between the thresholds of two Cayley graphs of one
   group** (`fpbs-generating-set-threshold-comparison`). It transfers a gap
   only when the gap has a margin, and the margin loses a power of the
   parameter.
2. **An exact reduction of Question 1.2 to single elementary moves** on
   generating sets (`fpbs-generating-sets-connected-by-product-moves` and the
   route `fpbs-group-invariance-via-product-moves`).

Question 1.2 is not settled.

## 0. Notation and imports

- `Gamma` is finitely generated. A generating set is a finite symmetric
  generating set not containing `e`. `G = Cay(Gamma,S)` is the simple Cayley
  graph with edges `{x, xs}`.
- `tau^G_p(x,y) = P_p(x <-> y)` and `theta^G(p) = P_p(o <-> infinity)`.
- `p_c(G) = inf{p : theta^G(p) > 0}` and
  `p_u(G) = inf{p : G_p has a unique infinite cluster a.s.}`.
- For an infinite subgroup `I`, `chi^{I,G}_p = E_p|K_o ∩ I|`, and `p_c(I;G)` is
  the threshold for an `I`-infinite cluster, as in
  `fpbs-relative-gap-along-any-subgroup-separates`.

Two established imports are used.

- `fpbs-hp-uniqueness-and-long-range-order` (Hutchcroft–Pan Thm 1.4, `H = Gamma`).
  For every `p`, `G_p` has a unique infinite cluster a.s. iff
  `inf_{x,y} tau^G_p(x,y) > 0`.
- `fpbs-cluster-count-trichotomy` (Newman–Schulman; Häggström–Peres,
  Schonmann). Every `p > p_u(G)` has a unique infinite cluster a.s.

## 1. The coupling lemma

**Data.** Let `S, S'` be generating sets, `G = Cay(Gamma,S)` and
`G' = Cay(Gamma,S')`.
- **Words.** From each pair `{s', s'^{-1}} ⊆ S'` choose one representative `s'`
  and a word `w_{s'} = a_1 ... a_l` over `S` with product `s'`, `l = l(s') >= 1`.
  Put `L = max l(s')`.
- **Paths.** A `G'`-edge of type `s'` is `f = {x, xs'}`.
  - If `s'^2 != e`, this representation is unique, and `f` carries the one
    path `pi_x = (x, xa_1, xa_1a_2, ..., xs')` in `G`.
  - If `s'^2 = e`, then `f = {xs', xs's'}` as well, and `f` carries the two
    paths `pi_x` and `pi_{xs'}`.
- **Uses.** A use is a triple `j = (f, pi, i)`: a `G'`-edge `f`, one of its paths
  `pi`, and a step index `1 <= i <= l(s')`. The step traverses exactly one
  `G`-edge `e(j)`. Let `J(e) = {j : e(j) = e}` and `M = max_e |J(e)|`.
  - `M` is finite, because `|J(e)|` depends only on the type of `e`.
  - `M <= 4 L |S'|`. A `G`-edge `{y, ys}` is step `i` of a path from `x` only
    when `x a_1 ... a_{i-1}` is `y` or `ys`, which gives at most two `x` per
    (type, path, `i`).
- **The map.** Define

```text
phi(p) = (1 - (1-p)^{1/M})^L,
```

  a continuous increasing bijection of `[0,1]`.

**Lemma 1.** For all `p in [0,1]`, all `x, y in Gamma` and every infinite
subgroup `I`:

```text
tau^{G'}_{phi(p)}(x,y) <= tau^G_p(x,y),    theta^{G'}(phi(p)) <= theta^G(p),
chi^{I,G'}_{phi(p)} <= chi^{I,G}_p .
```

*Proof.*
- **Randomness.** Take independent uniforms `U_j` (one per use) and `V_e` (one
  per `G`-edge). Put `b = phi(p)` and `c = b^{1/L} = 1 - (1-p)^{1/M}`.
- **The configuration `xi` on `G'`.**
  - A path of length `l` gets threshold `c_j = beta^{1/l}` on each of its uses,
    where `beta = b` for one path and `beta = 1 - sqrt(1-b)` for two paths.
    Declare `f` open in `xi` iff for some path `pi` of `f`, `U_j <= c_j` for
    all uses `j = (f,pi,i)`.
  - Then `P(xi(f) = 1) = b`. Distinct `G'`-edges use disjoint uniforms, so
    `xi` is Bernoulli(`b`) percolation on `G'`.
  - Every `c_j <= b^{1/l} <= b^{1/L} = c`, since `beta <= b <= 1` and
    `l <= L`.
- **The configuration `omega` on `G`.**
  - Declare `e` open in `omega` iff `U_j <= c_j` for some `j in J(e)`, or
    `V_e <= z_e`. Here `z_e` solves `1 - (1-z_e) prod_{j in J(e)} (1-c_j) = p`.
  - A solution exists because `prod (1-c_j) >= (1-c)^M = 1-p`.
  - Distinct `G`-edges use disjoint uniforms (each use traverses one edge), so
    `omega` is Bernoulli(`p`) percolation on `G`.
- **Comparison.** If `xi(f) = 1` through the path `pi`, every `G`-edge
  traversed by `pi` is `omega`-open, so the endpoints of `f` are
  `omega`-connected. Hence every `xi`-cluster, as a vertex set, lies inside one
  `omega`-cluster. That gives `{x <->_xi y} ⊆ {x <->_omega y}` and
  `{o <->_xi infinity} ⊆ {o <->_omega infinity}`, and
  `|K^xi_o ∩ I| <= |K^omega_o ∩ I|` pointwise. ∎

No invariance of the coupling is needed: `xi` and `omega` are honest Bernoulli
percolations, and the inequalities hold pointwise.

## 2. The comparison theorem

**Theorem 2** (`fpbs-generating-set-threshold-comparison`). With `phi` as
above:

- (a) `p_u(G') >= phi(p_u(G))`;
- (b) `p_c(G) <= phi^{-1}(p_c(G'))`, equivalently `p_c(G') >= phi(p_c(G))`;
- (c) `p_c(I;G) <= phi^{-1}(p_c(I;G'))` for every infinite `I`;
- (d) if `S ⊆ S'`, then `p_c(G') <= p_c(G)` and `p_u(G') <= p_u(G)`.

*Proof.*
- **(a).**
  - Let `p < p_u(G)`. Since `p_u(G)` is an infimum, `G_p` has no unique
    infinite cluster a.s. By HP Thm 1.4, `inf tau^G_p = 0`.
  - By Lemma 1, `inf tau^{G'}_{phi(p)} = 0`, so by HP Thm 1.4 again
    `G'_{phi(p)}` has no unique infinite cluster.
  - Every `q > p_u(G')` is unique (trichotomy node), so `phi(p) <= p_u(G')`.
  - Let `p ↑ p_u(G)` and use continuity of `phi`.
- **(b).** If `phi(p) > p_c(G')`, then `theta^{G'}(phi(p)) > 0`, since
  `theta` is increasing. By Lemma 1, `theta^G(p) > 0`, so `p >= p_c(G)`.
  Taking the infimum over such `p` gives `p_c(G) <= phi^{-1}(p_c(G'))`.
- **(c).** Same as (b): an `I`-infinite `xi`-cluster lies in an `omega`-cluster
  containing the same vertices of `I`.
- **(d).**
  - `G` is a spanning subgraph of `G'`. Couple by restriction:
    `tau^G_q <= tau^{G'}_q` and `theta^G(q) <= theta^{G'}(q)`, so
    `p_c(G') <= p_c(G)`.
  - If `q > p_u(G)`, then `G_q` is unique, so `inf tau^G_q > 0` (HP), so
    `inf tau^{G'}_q > 0`, so `G'_q` is unique (HP). Hence `q >= p_u(G')`, and
    `p_u(G') <= p_u(G)`. ∎

**Corollary (gap transfer with a margin).** Let `S ⊆ S'`, with `phi` built from
words of `S'` over `S`.
- (i) If `p_c(G) < phi(p_u(G))`, then `p_c(G') < p_u(G')`, because
  `p_c(G') <= p_c(G) < phi(p_u(G)) <= p_u(G')`.
- (ii) If `phi^{-1}(p_c(G')) < p_u(G')`, then `p_c(G) < p_u(G)`, because
  `p_c(G) <= phi^{-1}(p_c(G')) < p_u(G') <= p_u(G)`.

For general `S, S'`, apply (a) with words of `S'` over `S` and (b) with words of
`S` over `S'`.

**Sanity checks.**
- `Cay(F_2,{a,b}) ⊂ Cay(F_2,{a,b,ab})`: `L = M = 2`. From `p_u = 1` on the tree,
  (a) gives `p_u(G') = 1`, consistent with infinitely many ends.
- `Z^2 ⊂` the triangular lattice: `phi(1/2) ≈ 0.086 <= 0.347 ≈ p_c(tri)` and
  `phi^{-1}(0.347) ≈ 0.83 >= 1/2`.

**Size of the loss.** For small `p`, `phi(p) ≈ (p/M)^L`. A single move adding
`t = uv` has `L = 2`, and `M = 2` in the generic case (`u != v`, and none of
`u, v, t` an involution). If `u = v`, then `M = 3`. So only gaps with roughly
`p_c(G) < p_u(G)^2/4` are transferred.

## 3. Reduction to elementary moves

Moves on generating sets:
- **Add:** `S -> S ∪ {t, t^{-1}}` with `t = uv`, `u, v in S`, `t ∉ S ∪ {e}`.
- **Remove:** `S -> S \ {t, t^{-1}}` with `t in S`,
  `t = uv`, `u, v in S \ {t, t^{-1}}`.

Both moves keep the set symmetric, generating (for Remove, `t` stays in the
generated group), and free of `e`.

**Lemma 3** (`fpbs-generating-sets-connected-by-product-moves`). Any two
generating sets `S, S'` of `Gamma` are joined by a finite sequence of moves.

*Proof.* Write `|x|_S` for word length.
- **Phase 1 (add `S'`).**
  - For each `s' in S' \ S`, pick an `S`-geodesic word `a_1 ... a_l`. Here
    `l >= 2`: `l = 1` would put `s'` in `S`, and `l = 0` would give `s' = e`.
  - Add the prefixes `P_2, ..., P_l = s'` in order, skipping any already
    present. Each prefix `P_j = P_{j-1} a_j` has both factors present, and
    `P_j != e` because `|P_j|_S = j`.
- **Phase 2 (remove auxiliary prefixes).**
  - The auxiliary prefixes are those not in `S ∪ S'`. Remove them in
    decreasing `|.|_S`.
  - Justification when removing `P_j`: `P_{j-1}` is shorter, so it is still
    present, and `a_j in S` is present.
  - Neither factor is `P_j^{±1}`. `a_j = P_j^{±1}` would put `P_j` in `S`, and
    `P_{j-1} = P_j^{±1}` contradicts `|P_{j-1}|_S = j-1 != j = |P_j^{±1}|_S`.
  - Only strictly shorter elements are needed, so removing `P_j^{-1}` together
    with `P_j` breaks no later step.
- **Phase 3 (remove `S \ S'`).**
  - For each `s in S \ S'`, add the prefixes of an `S'`-geodesic word for `s`,
    as in Phase 1.
  - Then remove all elements of `S \ S'` and all new auxiliaries in decreasing
    `|.|_{S'}`. Each has length at least 2, since length 1 would put it in `S'`.
  - Each is `Q_{j-1} b_j` with `b_j in S'` and `Q_{j-1}` strictly shorter, so
    both are still present. Neither equals the removed element or its inverse,
    by the same length argument.
- The result is `S'`. ∎

**Theorem 4** (route `fpbs-group-invariance-via-product-moves`). Question 1.2
holds iff `fpbs-gap-survives-product-generator-moves` holds: for every `Gamma`
and every `S` with `p_c < p_u`, every single Add or Remove move yields a
generating set with `p_c < p_u`.
- `⇐` by Lemma 3, chaining moves.
- `⇒` is the special case. (It is not wired as a route, to avoid a dependency
  cycle.)

## 4. Where invariance dies

For a single Add move (`G ⊆ G⁺`, `L = 2`), Theorem 2 confines the new
thresholds to windows:

```text
phi(p_c(G)) <= p_c(G⁺) <= p_c(G),     phi(p_u(G)) <= p_u(G⁺) <= p_u(G).
```

So a counterexample to Question 1.2 must contain a move that shrinks `p_u`
down to `p_c`:
- an Add move with `p_u(G⁺) <= p_c(G⁺)` although `p_c(G) < p_u(G)`; or
- a Remove move that raises `p_c` to `p_u`.

Theorem 2 rules this out only when the windows are disjoint, and they overlap
unless `p_c(G) < phi(p_u(G))`.

**Why the power is lost.** Lemma 1 buys independence of the `G'`-edges by
giving each one private randomness along a fixed path, which costs a path
probability. The lossless comparison event for a new edge `{x, xt}` is
`x <-> xt` in `omega`, and those events are dependent across edges. Turning a
dependent comparison process into a threshold statement would need uniqueness
monotonicity for that dependent process. The imports on main give monotonicity
only for Bernoulli percolation.

**The relative-gap criterion does not help.** Lemma 1(c) transfers finiteness
of relative susceptibility `chi^I` from `G` to `G'` only at the parameter
`phi(p)`. The criterion of `fpbs-relative-gap-along-any-subgroup-separates`
therefore transfers under exactly the same margin `p_c(G') < phi(p)`.

**Not claimed.** No novelty is claimed. Layered couplings of this kind are
folklore in proofs that `p_c < 1` is invariant. Nothing here is refereed or in
Lean.
