# The replica meet limit is governed by the exponential decay threshold

swarm-0917, lane w18c-bs-follow, 2026-09-19. Follow-through on the two wave-14
results `fpbs-replica-meet-cap-inf-fails-free-products` and
`fpbs-meet-threshold-capped-by-amenable-relative-threshold` (Lemma A).

## 0. Notation and imports

`G = Cay(Gamma,S)` is a connected, locally finite Cayley graph with degree `D`.
`tau_p(x,y) = P_p(x <-> y)`, `o` is the identity.

- `Z_k(p) = sum_x tau_p(o,x)^k = E|M_k(o)|`, where `M_k(o)` is the meet of the
  clusters of `o` in `k` independent Bernoulli(`p`) configurations; `p_k =
  sup{p : Z_k(p) < infinity}`; `p_cap^(k) = sup{p : |M_k(o)| < infinity a.s.}`;
  `p_cap^(infty) = sup_k p_cap^(k)`. All from
  `fpbs-replica-meet-threshold-sandwich` (items 1, 3, 4:
  `p_c <= p_k <= p_cap^(k) <= p_cap^(k+1) <= p_u`).
- **Exponential decay threshold** (Hutchcroft, EJP 2020, arXiv:1904.05804,
  Section 2, following Schonmann), verbatim: "We say that G has exponential
  connectivity decay at p if the quantity ξp := − lim sup_{n→∞} (1/n) log
  sup{τp(u,v) : d(u,v) ≥ n} is positive." and "pexp = pexp(G) = sup{p ∈ [0,1] :
  G has exponential connectivity decay at p}." Imported in
  `fpbs-exp-decay-threshold-facts`.
- `gr(G) = lim_n (1/n) log |S_n|` (sphere growth; `<= log D`).
- Lemma A (`fpbs-meet-threshold-capped-by-amenable-relative-threshold`, item 1):
  `p_cap^(k) <= p_c(H;G)` for every infinite amenable `H <= Gamma` and every `k`.

Monotonicity: `tau_p` is nondecreasing in `p`, so exponential decay at `p`
gives it at every `p' < p`, and `(0, p_exp)` consists of decay points.

## 1. Theorem 1 (the exponential sandwich)

For every connected, locally finite, transitive graph `G` of finite degree:

```text
p_exp(G) <= sup_k p_k(G) <= p_cap^(infty)(G) <= p_u(G).
```

More precisely, `Z_k(p) < infinity` whenever `k * xi_p > gr(G)`.

**Proof.** Fix `p` with `xi_p > 0` and `k` with `k xi_p > gr`. Choose `eps > 0`
with `k (xi_p - eps) > gr + eps`. By definition of `xi_p` there is `N` with
`tau_p(o,x) <= exp(-(xi_p - eps) n)` for `d(o,x) = n >= N` (the sup over
`d >= n` is at least the value at distance exactly `n`). By definition of `gr`
there is `C` with `|S_n| <= C exp((gr + eps) n)`. So

```text
Z_k(p) <= |B_N| + sum_{n >= N} C exp((gr+eps) n) exp(-k (xi_p - eps) n) < infinity.
```

Hence `p <= p_k`. Every `p < p_exp` has `xi_p > 0`, so `p < p_exp` gives
`p <= p_k` for `k > gr/xi_p`. Thus `p_exp <= sup_k p_k`. The remaining two
inequalities are sandwich items 1 and 4. QED

**Calibration (sharp on trees).** On `T_d`, `tau_p(o,x) = p^{|x|}`, so
`xi_p = -log p`, `gr = log(d-1)`. The criterion `k xi_p > gr` reads
`p < (d-1)^{-1/k}`, which is exactly `p_k(T_d)` (sandwich item 5). So the
growth-versus-rate criterion loses nothing on trees.

## 2. Corollaries

**Corollary 2 (amenable subgroups).** For every infinite amenable `H <= Gamma`,

```text
p_exp(G) <= p_cap^(infty)(G) <= p_c(H;G) <= p_u(G).
```

The middle inequality is Lemma A. The last: for `p > p_u` let `U` be the unique
infinite cluster; `W = U ∩ H` has an `H`-invariant law (`U` is defined
equivariantly) and `P(o in W) = theta(p) > 0`, so by the invariant-finite-set
lemma (Lemma 1.1 of `fpbs-replica-meet-threshold-sandwich-proof`, Lemma 0 of
the amenable-caps artifact) `|W| = infinity` on `{o in W}`; so `p >= p_c(H;G)`.

**Corollary 3 (Hutchcroft's Conjecture 2.1 feeds the whole chain).** If
`p_c(G) < p_exp(G)`, then [Q_fin] holds (some `p > p_c`, `k` with
`Z_k(p) < infinity`), hence [cap_fin] (`fpbs-replica-meet-threshold-gap-universal`),
hence RG along every infinite amenable subgroup
(`fpbs-relative-gap-along-every-amenable-subgroup-universal`), hence BS.

**Corollary 4 (where p_exp = p_u, the limit question is settled).** If
`p_exp(G) = p_u(G)`, then

```text
p_cap^(infty)(G) = sup_k p_k(G) = p_u(G)  and  p_c(H;G) = p_u(G)
for every infinite amenable H <= Gamma.
```

This applies to:

1. **Transitive, one-ended, nonamenable planar graphs** (Schonmann's theorem
   `p_exp = p_u`, imported in `fpbs-exp-decay-threshold-facts` item 4). This
   includes the standard Cayley graph of every closed surface group of genus
   at least 2 (the 1-skeleton of the `{4g,4g}` tiling). So **every infinite
   cyclic subgroup of a surface group has `p_c(H;G) = p_u`** on that Cayley
   graph, and the wave-14 spark ("cyclic subgroup of a surface group might
   give `p_c(H;G) < p_u` and refute `sup_k p_cap = p_u`") is answered in the
   negative.
2. **`T x A` for a regular tree `T` (degree at least 3) and an infinite
   amenable Cayley graph `A`, and the lamplighter `LL(T)`**:
   `p_(2->2) = p_u` (Hutchcroft–Pan, `fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu`)
   and `p_(2->2) <= p_exp <= p_u` (`fpbs-exp-decay-threshold-facts` items 1, 3).
3. **Trees** (`p_exp = 1 = p_u`), recovering sandwich item 5.

So [cap_inf] (`p_cap^(infty) = p_u`) holds on all three classes, all of which
except trees are one-ended (`T x A` is one-ended since `A` is infinite).

## 3. Theorem 5 (free products: the limit is exactly p_exp = p_c(A))

Setting of `fpbs-replica-meet-cap-inf-fails-free-products`: `A` infinite,
finitely generated, amenable, `L = Cay(A,S_A)`, `p_c(L) < 1`,
`G = Cay(A * Z/2, S_A ∪ {t})`. Then

```text
p_exp(G) = sup_k p_k(G) = p_cap^(infty)(G) = p_c(L) < 1 = p_u(G).
```

In particular `p_cap^(k)(G)` increases to `p_c(L)`, for every such `A` (this
generalises `fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2` from
`Z^3` to every amenable factor), and on `Z^2 * Z/2`, `p_cap^(infty) = 1/2`
(Kesten's `p_c(Z^2) = 1/2`).

**Proof.** Upper bound: `p_cap^(k)(G) <= p_c(L)` for every `k` is item 3 of
`fpbs-replica-meet-cap-inf-fails-free-products`. With Theorem 1 it remains to
show `p_exp(G) >= p_c(L)`.

*Exact factorisation.* Write `x in Gamma` in normal form
`x = a_0 t a_1 t ... t a_m` with `a_i in A`, `a_1, ..., a_{m-1} != e`. Since
`S_A` and `{t}` generate the free factors, `|x|_S = m + sum_i |a_i|_{S_A}`.
Every `t`-edge is a bridge (cut edge) of `G` (Section 2.0 of the w14
artifact). The `o`–`x` geodesic in the Bass–Serre coset tree passes through
the planes `P_i = a_0 t ... a_{i-1} t A` and the `m` bridges between
consecutive ones. A path from `o` to `x` must cross each of these `m` bridges;
between the entry and the exit vertex of `P_i` (which differ by right
multiplication by `a_i`) any excursion out of `P_i` leaves and returns through
one bridge, so it can be cut out, and the two points are joined inside the
subgraph `P_i ≅ L`. The events "bridge `j` open" and "entry of `P_i` joined to
exit of `P_i` inside `P_i`" use disjoint edge sets. Hence

```text
tau_p^G(o,x) = p^m * prod_{i=0}^m tau_p^L(e, a_i).
```

*Sharpness on `L`.* Apply `fpbs-hp-relative-sharpness` to the Cayley graph `L`
with `H = A` the whole group: `p_c(A;L) = p_c(L)`, and for `p < p_c(L)` there
is `c > 0` with `P_p(|K^L_e| >= n) <= exp(-c n)` for all `n >= 1`. A cluster
containing `e` and `a` has at least `|a| + 1` vertices, so
`tau^L_p(e,a) <= exp(-c(|a|+1)) <= exp(-c|a|)` for all `a` (trivially for
`a = e`).

*Conclusion.* For `0 < p < p_c(L)`, put `eta = min(c, -log p) > 0`. Then
`tau^G_p(o,x) <= p^m exp(-c sum|a_i|) <= exp(-eta |x|_S)`, so `xi_p >= eta > 0`
and `p <= p_exp(G)`. Hence `p_exp(G) >= p_c(L)`. QED

(`p_exp(G) <= p_c(L)` also follows directly: for `p > p_c(L)`,
`tau^G_p(o,a) >= theta_L(p)^2` for all `a in A`, by FKG inside `L`. This
matches Kozáková's Proposition 6, `p_exp(G_1 * ... * G_n) = min_i p_exp(G_i)`,
quoted in `free-product-critical-l2-2026-09-12.md`; it is not used.)

## 4. What this changes

**The invariant.** On every graph where `p_cap^(infty)` is now computed —
trees, `A * Z/2` for every amenable `A`, one-ended planar graphs, `T x A`,
`LL(T)` — it equals `p_exp`, not `p_u`. The wave-14 counterexample to [cap_inf]
is exactly Hutchcroft's example of `p_exp < p_u` ("it is known that this
inequality is strict in some examples, such as the free product Z2 ∗ (Z/2Z)",
EJP 2020, Section 2). So:

- **[cap_inf] fails exactly where `p_exp < p_u` can be exhibited.** Its
  failure is a statement about the exponential decay threshold, not about
  amenable subgroups per se; Lemma A's amenable caps are sharp there only
  because amenable factors pin `p_exp`.
- **The cyclic-subgroup test is dead.** A counterexample to
  "`p_c(H;G) = p_u` for every infinite amenable `H`" needs `p_exp(G) < p_u(G)`
  (Corollary 2). It cannot live on a surface group with planar generators, on
  a tree product with an amenable graph, or on any other graph with
  `p_exp = p_u`. The examples of `p_exp < p_u` recorded in this graph (free
  products `A * Z/2`, Hutchcroft's `Z^2 * Z/2`) are infinitely ended; this is a
  statement about what is recorded here, not a literature survey.
  The live belief question becomes: **is there a one-ended Cayley graph with
  `p_exp < p_u`?** (Schonmann's problem; see Hutchcroft, EJP 2020, Section 2.)
- **[cap_fin] is sandwiched by Hutchcroft's Conjecture 2.1.** `p_c < p_exp`
  implies [Q_fin], [cap_fin] and RG (Corollary 3). Conversely, if
  `p_cap^(infty) = p_exp` held on `G` (open node
  `fpbs-replica-meet-limit-equals-exp-decay-threshold`), then [cap_fin] on `G`
  would be *equivalent* to `p_c < p_exp`. So an a.s. proof of [cap_fin] that
  does not also prove `p_c < p_exp` needs a graph with `p_exp < p_cap^(infty)`;
  none exists among the computed classes.

**Status.** `fpbs-replica-meet-threshold-gap-universal` stays OPEN: nothing
here proves `p_c < p_exp` on a new class. The known classes with
`p_c < p_exp` (hence [cap_fin] and RG) are those with `p_c < p_(2->2)`
(Hutchcroft's Theorem 2.2: hyperbolic, nonunimodular, and the others in the
graph), one-ended planar graphs (Schonmann plus BS 2001 `p_c < p_u`), and free
products (this Theorem 5 plus `p_c(G) < p_c(L)`, Kozáková Corollary 7).
