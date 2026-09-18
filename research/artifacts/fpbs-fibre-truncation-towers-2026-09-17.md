# Fibre-truncation towers: the finite-models transplant of relative subcriticality

2026-09-17, agent `b-p-bs5` (wave `swarm-0917`, role transplanter, family
finite-models). Target hole: `fpbs-amenable-wq-normal-relative-subcriticality`.
Nothing here is refereed or formally verified.

## 0. Why this transplant, and what it is

The finite-models family approximates a group by finite or "more finite"
objects and counts. For percolation on a nonamenable Cayley graph `G`, two
versions are available.

* **Finite quotients** `Gamma -> F_n`. These are already killed:
  `fpbs-expander-approximant-giant-data-is-glued` shows that giant-component and
  bounded-separation connectivity data of finite expander approximants see only
  the glued law, and the dead approach on `fpbs-pivotal-budget-universal`
  records that finite approximants cannot keep a margin above `p_c(G)`. For
  relative susceptibility the same thing happens: once the images of `H` are
  large and a giant exists, `E|K_o ∩ image(H)| >= theta^2 |image(H)| -> infinity`.
* **Fibre truncations.** Keep the quotient `Q = Gamma/H` intact and make only
  the amenable fibre finite. Let `H` be normal and let `H_k <= H` be subgroups
  that are normal in `Gamma`, of finite index in `H`, nested
  (`H_(k+1) <= H_k`), with `∩_k H_k = {1}`. Put `Gamma_k = Gamma/H_k` and
  `G_k = Cay(Gamma_k, S_k)` with `S_k` the image of `S`. The fibre `H/H_k` of
  `G_k` is finite, so its relative susceptibility is at most `[H:H_k]`, and
  `G_k` is quasi-isometric to `Gamma/H`. When `Q` is hyperbolic, every `G_k`
  is hyperbolic, and gap theorems with `k`-dependent constants apply to it.

Examples of such towers: `H = <z>` central or normal infinite cyclic,
`H_k = <z^(2^k)>` (braid groups, `F_2 x Z`, Seifert-fibred groups);
`H = Z^d` normal, `H_k = 2^k Z^d` (characteristic, hence normal in `Gamma`),
e.g. `Z^d x| SL_d(Z)`; more generally any finitely generated residually finite
normal `H`, with `H_k` the intersection of all subgroups of `H` of index at
most `k`. These are characteristic in `H` (hence normal in `Gamma`), of finite
index because a finitely generated group has finitely many subgroups of each
index, nested, and with trivial intersection by residual finiteness.

Question: does the tower `(G_k)` carry any information about the hole that
`G` itself does not? Answer (Sections 2–4): the relative susceptibility is
monotone along the tower and converges to that of `G`, the uniqueness threshold
is lower semicontinuous along the tower, and the only transferable datum is the
hole itself.

Notation. `tau^X_p(x,y)` is the two-point function on a graph `X`,
`K^X_x` the cluster of `x`, `theta_X(p) = P_p(|K^X_o| = infinity)`, and

```text
chi^H_G(p)   = E_p |K^G_o ∩ H|,
chi^(k)(p)   = E_p |K^(G_k)_o ∩ pi_k(H)|,     pi_k : Gamma -> Gamma_k.
```

Fix `k_0` with `H_(k_0) ∩ B_Gamma(2) = {1}` (it exists: `B_Gamma(2)` is finite,
each `b != 1` lies outside some `H_k`, and the chain is nested). For
`k' >= k >= k_0` the maps `G -> G_k` and `G_(k') -> G_k` induced by the
quotient maps are covering maps of simple graphs: `S ∩ H_k = ∅` gives no
loops, and `s^(-1) s' notin H_k` for `s != s'` in `S` gives that the `|S|`
neighbours `x s` of `x` have distinct images. All statements below are for
`k >= k_0`.

## 1. The lifting coupling

**Lemma 1.1 (lifted exploration).** Let `phi : X -> Y` be a graph homomorphism
between locally finite connected graphs that is locally surjective: for every
vertex `x` of `X` and every edge `f` of `Y` at `phi(x)`, some edge of `X` at `x`
maps to `f`. Let `o in X`. Then there is a coupling of Bernoulli(`p`) bond
percolation `omega` on `X` and `omega'` on `Y` and an injective map
`L : K^Y_(phi(o)) -> K^X_o` with `phi ∘ L = id`. In particular, for every set
`A` of vertices of `Y`,

```text
|K^Y_(phi(o)) ∩ A|  <=  |K^X_o ∩ phi^(-1)(A)|     almost surely in the coupling,
```

and `|K^Y_(phi(o))| = infinity` implies `|K^X_o| = infinity`.

*Proof.* Let `omega` be Bernoulli(`p`) on `E(X)` and `xi` an independent
Bernoulli(`p`) field on `E(Y)`. Run breadth-first exploration of the cluster of
`y_0 = phi(o)` in `Y`, maintaining the explored set `V_t`, a queue, and a lift
`L : V_t -> V(X)` with `phi(L(y)) = y`, starting from `L(y_0) = o`. Fix an
enumeration of edges at each vertex. When a vertex `y` is processed, go through
its edges `f = {y, y'}` in order; if `y'` is currently unexplored, choose (by a
fixed rule depending only on `L(y)` and `f`) an edge `f~` of `X` at `L(y)` with
`phi(f~) = f`, set `omega'(f) := omega(f~)`, and if it is open add `y'` to the
queue with `L(y') :=` the other endpoint of `f~`. Edges never examined get
`omega'(f) := xi(f)`.

Each edge `f` of `Y` is examined at most once, and distinct examined edges `f`
have distinct lifts `f~` (their images differ). So every examined value
`omega(f~)` is a coordinate of `omega` that has not been read before, and the
choice of which edge to examine next depends only on values already read. By
the standard adaptive-reading argument, `omega'` is an iid Bernoulli(`p`)
field on `E(Y)`.

The final explored set is `K^Y_(y_0)` for `omega'`: every `omega'`-open edge
from an explored `y` to a vertex `y'` was either examined when `y` was
processed, so `y'` was added, or `y'` was already explored. By induction each
`L(y)` is joined to `o` by `omega`-open edges (the lifts `f~`), so
`L(K^Y_(y_0)) ⊆ K^X_o`. `L` is injective because `phi ∘ L = id`. QED.

For `phi = pi_k : G -> G_k` and `A = pi_k(H)` we have
`phi^(-1)(A) = H H_k = H`. For `phi : G_(k') -> G_k` and `A = pi_k(H)`,
`phi^(-1)(A) = pi_(k')(H)`.

## 2. Relative susceptibility is monotone and converges along the tower

**Theorem 2.1.** For every `p in [0,1]`, every `n >= 1` and `k_0 <= k <= k'`:

1. `P_p(|K^(G_k)_o ∩ pi_k(H)| >= n) <= P_p(|K^(G_(k'))_o ∩ pi_(k')(H)| >= n)
   <= P_p(|K^G_o ∩ H| >= n)`, hence
   `chi^(k)(p) <= chi^(k')(p) <= chi^H_G(p)`;
2. `P_p(|K^(G_k)_o ∩ pi_k(H)| >= n) -> P_p(|K^G_o ∩ H| >= n)` and
   `chi^(k)(p) -> chi^H_G(p)` as `k -> infinity` (the limit may be `+infinity`);
3. `theta_(G_k)(p) <= theta_(G_(k'))(p) <= theta_G(p)`, so
   `p_c(G_k)` is nonincreasing in `k` and `p_c(G_k) >= p_c(G)`.

*Proof.* (1) and (3) are Lemma 1.1 applied to the coverings
`G_(k') -> G_k` and `G -> G_(k')`.

(2) Fix `R`. Let `k` be so large that `H_k ∩ B_Gamma(2R + 2) = {1}`. Then
`pi_k` is injective on `B = B_G(o,R+1)`, and two distinct edges of `B_G(o,R)`
have distinct images (if `pi_k(e) = pi_k(e')` then `e' = h e` for some
`h in H_k`, and `h` moves a vertex of `B_G(o,R)` into `B_G(o,R)`, so
`h in B_Gamma(2R)`, so `h = 1`). Hence the image of `B_G(o,R)` is an isomorphic
copy of it inside `G_k`, and the Bernoulli field of `G_k` restricted to the image
edges is iid. Couple `omega` on `B_G(o,R)` with it through `pi_k`. An open path
inside `B_G(o,R)` from `o` to `h` maps to an open path from `pi_k(o)` to
`pi_k(h)`, and `pi_k` is injective on `H ∩ B_G(o,R)`. Therefore

```text
P_p( |{h in H ∩ B_G(o,R) : o <-> h inside B_G(o,R)}| >= n )
      <=  P_p(|K^(G_k)_o ∩ pi_k(H)| >= n)
```

for all large `k`. As `R -> infinity` the events on the left increase to
`{|K^G_o ∩ H| >= n}`, so `liminf_k P_p(|K^(G_k)_o ∩ pi_k(H)| >= n) >=
P_p(|K^G_o ∩ H| >= n)`. With the upper bound from (1), the probabilities
converge, and the expectations `chi^(k)(p) = sum_n P(... >= n)` converge to
`chi^H_G(p)` by monotone convergence (they are nondecreasing in `k` by (1)).
QED.

Nothing in Section 2 uses amenability, wq-normality or nonamenability.

**Corollary 2.2 (no slack).** For a tower as above and `p in [0,1]`:
`chi^H_G(p) < infinity` iff `sup_k chi^(k)(p) < infinity`, and then
`chi^H_G(p) = sup_k chi^(k)(p)`. So `fpbs-amenable-wq-normal-relative-subcriticality`
for `(Gamma,S)` is *equivalent* to: there is `p > p_c(G)` at which the finite
fibre occupations `E_p|K^(G_k)_o ∩ pi_k(H)|` are bounded uniformly in `k`.
Any bound with a `k`-dependent constant (for instance the trivial `[H:H_k]`)
transfers nothing.

## 3. The uniqueness threshold is lower semicontinuous along the tower

Now assume in addition that `H` is infinite and amenable (it is normal, hence
wq-normal). Imports, all already in the graph:

* `fpbs-amenable-wq-normal-pu-is-relative-pc`: `p_u(G) = p_c(H;G)`.
* `fpbs-hp-relative-sharpness` (Hutchcroft–Pan Theorem 1.8): for
  `p < p_c(H;G)`, `|K_o ∩ H|` has an exponential tail; in particular
  `chi^H_G(p) < infinity`.
* `fpbs-cluster-count-trichotomy` (Häggström–Peres, Schonmann): on a
  quasi-transitive graph the infinite cluster is unique a.s. for every
  `p > p_u`.
* Harris–FKG inequality for increasing events (textbook).

**Theorem 3.1.** Let `H` be an infinite amenable normal subgroup and `(H_k)`
a tower as in Section 0. Then

```text
p_u(G)  <=  liminf_(k -> infinity) p_u(G_k).
```

Quantitatively: if `p > p_c(G_(k_1))` for some `k_1 >= k_0` and
`chi^H_G(p) < infinity`, then `p <= p_u(G_k)` for every `k >= k_1` with

```text
[H : H_k] * theta_(G_(k_1))(p)^2  >  chi^H_G(p).
```

*Proof.* Quantitative part. Let `k >= k_1` satisfy the displayed inequality
and suppose `p > p_u(G_k)`. By the trichotomy import `G_k` has a unique
infinite cluster a.s. at `p`. For every vertex `x` of `G_k`, the events
`{o <-> infinity}` and `{x <-> infinity}` are increasing, so Harris–FKG and
uniqueness give

```text
tau^(G_k)_p(o,x) >= P_p(o <-> infinity, x <-> infinity) >= theta_(G_k)(p)^2
                 >= theta_(G_(k_1))(p)^2,
```

the last step by Theorem 2.1(3). Summing over the `[H:H_k]` points of
`pi_k(H)` gives `chi^(k)(p) >= [H:H_k] theta_(G_(k_1))(p)^2 > chi^H_G(p)`,
contradicting Theorem 2.1(1). So `p <= p_u(G_k)`.

Semicontinuity. Let `p < p_u(G) = p_c(H;G)`. By relative sharpness
`chi^H_G(p) < infinity`. If `p <= p_c(G_k)` for every `k`, then
`p_u(G_k) >= p_c(G_k) >= p` for all `k`. Otherwise pick `k_1` with
`p > p_c(G_(k_1))`; then `theta_(G_(k_1))(p) > 0`, and since `[H:H_k] -> infinity`
(the `H_k` have trivial intersection and `H` is infinite) the quantitative part
gives `p_u(G_k) >= p` for all large `k`. As `p < p_u(G)` was arbitrary,
`liminf_k p_u(G_k) >= p_u(G)`. QED.

**Corollary 3.2 (necessary uniform gap; counterexample detector).** If
`p_c(G) < p_u(G)` then `liminf_k p_u(G_k) >= p_u(G) > p_c(G)`: the uniqueness
thresholds of the truncations stay a fixed distance above `p_c(G)`, while
`p_c(G_k) >= p_c(G)`. Contrapositive: a tower with `p_u(G_k) -> p_c(G)` along a
subsequence is a counterexample to the Benjamini–Schramm conjecture for `G`.

## 4. Obstruction: per-truncation gap theorems do not transfer

**Killed class.** Derivations of `p_c(G) < p_u(G)` (equivalently of the hole
for `(Gamma,S)`) from theorems proved on the truncations `G_k` with constants
depending on `k`. Members include:

* Choi–Seo on every Cayley graph of an acylindrically hyperbolic group, applied
  to `Gamma/<z^k>` when `Q = Gamma/<z>` is non-elementary hyperbolic (a finite
  central extension of `Q` is quasi-isometric to `Q`, hence hyperbolic);
* Hutchcroft's `p_c < p_(2->2)` on hyperbolic graphs, whose constants depend on
  the geometry of `G_k`, in particular on its hyperbolicity constant, which is
  not uniform in `k` (for `F_2 x Z/m` with standard generators the fibre cycle
  of length `m` is isometrically embedded, since only `z`-edges change the
  `Z/m` coordinate, so the constant is at least of order `m`);
* `p_u = 1` on infinitely-ended truncations (for `Q` virtually free);
* per-truncation fibre bounds `chi^(k)(p) <= [H:H_k]`.

**Where every member dies.** At the passage `k -> infinity`, for two
independent reasons. Reason 2 is proved; reason 1 is proved up to the recorded
calibration.

1. *The output of a per-truncation gap theorem is a lower bound on
   `p_u(G_k)`.* Turning it into a lower bound on `p_u(G)` is an upper
   semicontinuity of `p_u` along the tower. Theorem 3.1 proves only the
   opposite inequality. Calibration (recorded, not claimed;
   uses the imports "infinitely many ends implies `p_u = 1`" and Babson–Benjamini
   "one-ended finitely presented implies `p_u < 1`", neither in the graph):
   for `Gamma = F_2 x Z` with standard generators, `G_k = Cay(F_2 x Z/2^k)` has
   infinitely many ends, so `p_u(G_k) = 1` for every `k`, while
   `p_u(G) < 1`. So `p_u` genuinely jumps down in the limit, and the
   uniform-gap condition of Corollary 3.2 holds automatically for every
   virtually-free `Q`. Hence "uniform truncation gap implies the hole" would by
   itself settle Choi–Seo Question 1.3 (`F_2 x Z` on every generating set); it
   is not a weaker target.
2. *The only transferable datum is uniform fibre occupation.* By Corollary 2.2,
   a bound on the truncations transfers to the hole iff it is a bound on
   `chi^(k)(p)` uniform in `k` at one `p > p_c(G)`, and that bound equals
   `chi^H_G(p)`. So the truncation adds no slack: it is the hole itself.

**The invariant.** Fibre occupation `E_p|K_o ∩ pi_k(H)|` at a fixed parameter,
uniformly over the tower. Finite quotients kill it (giant component), fibre
truncations preserve it exactly (Theorem 2.1), and uniqueness-threshold data
only bound it from below (Theorem 3.1).

## 5. What survives, and a spark

* Theorem 3.1 is a new structural fact usable by any lane: along a fibre tower,
  `p_u` is lower semicontinuous, and nonuniqueness of the truncations at `p`
  is forced for large `k` whenever the hole holds at `p`.
* Corollary 3.2 is a falsifiable necessary condition for one-ended hyperbolic
  `Q` (surface groups times `Z`, Seifert-fibred groups), where `p_u(G_k) < 1`
  is not automatic.
* **Spark (not pursued).** For `G = T_d x Z` the truncation `T_d x C_m` is a tree
  of cycles joined by perfect matchings. Its fibre occupation
  `chi^(m)(p)` satisfies a finite-type tree recursion whose types are the
  connection patterns (set partitions) of one cycle, exactly computable for
  small `m`. Monotone convergence in `m` (Theorem 2.1) turns these into
  certified lower bounds for `chi^Z_G(p)`; a linear growth in `m` at a
  parameter already known to exceed `p_c(T_d x Z)` would be evidence for
  collapse on small `d`, where Grimmett–Newman does not apply.
