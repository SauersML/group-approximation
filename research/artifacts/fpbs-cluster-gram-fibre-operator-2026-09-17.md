# Cluster Gram representation of the fibre operator (2026-09-17)

Author: swarm-0917-w18-w18-bs-pull, working as transplanter via operator
algebras on `fpbs-percolation-kesten-normal-gap`.

Nodes:

- `fpbs-normal-fibre-mass-cluster-gram-representation`: ESTABLISHED, proof in the
  `-proof` route.
- `fpbs-critical-profile-kesten-ratio-integrable`: OPEN.
- `fpbs-kesten-gap-via-profile-kesten-ratio`: the route to the Kesten gap.

Scripts are in `experiments/fpbs-gram-profile-2026-09-17/`.

## 1. The dictionary

Fix `Gamma`, `S`, a normal subgroup `N` and `Q = Gamma/N`. Let `L(Q)` be the
group von Neumann algebra, with trace `tr(x) = <x delta_e, delta_e>`. The fibre
operator `A_p = lambda_Q(sigma_p)` is a positive operator affiliated with `L(Q)`.

| percolation | von Neumann algebra |
|---|---|
| `chi^N_p = sigma_p(e)` | `tr(A_p)` |
| `m`-chain relative susceptibility `chi^(N,m)_p` | `tr(A_p^m)` |
| `||sigma_p||_Q` (diagonal formula of the sandwich node) | `lim tr(A_p^m)^(1/m) = ||A_p||_infinity` |
| `p < p_c(N;G)` | `A_p ∈ L^1(L(Q))` |
| `p < p^Q_(2->2)(N;G)` | `A_p ∈ L(Q)` (bounded) |
| critical fibre l2 | `A_(p_c) ∈ L(Q)` |
| trichotomy type (ii): `p_c = p^Q < p_c(N;G)` | `A_p ∈ L^1 \ L^infinity` just above `p_c` |
| conjecture E: `p_c(N;G) = p^Q` | `A_p ∈ L^1` implies `A_(p') ∈ L^infinity` for `p' < p` |

The transplanted question is therefore an `L^1 -> L^infinity` upgrade for one
specific family of positive affiliated operators. The new input is that this
family has a concrete positive structure.

**Gram form.** When clusters are finite,

```text
A_p = E_p[ |K_o|^{-1} lambda_Q(a)^* lambda_Q(a) ],     a(u) = |K_o ∩ u~ N|,
```

in the weak sense (Section "Operator form" of the proof route). Each summand
`lambda_Q(a)^* lambda_Q(a)` is a positive element of the group ring. So `A_p` is
an average of positive group-ring elements, each weighted by the inverse cluster
size. From this:

- The trace identity is `tr(A_p) = E[ ||a||_2^2 / |K_o| ]`.
- The operator norm satisfies `||A_p|| <= E[ ||lambda_Q(a)||^2 / |K_o| ]`.
- `A_p >= 0`, meaning `sigma_p` is positive definite, for every normal `N`.
- The Cauchy--Schwarz bound `|tr(A_p lambda(u))| <= tr(A_p)` is the fibre
  maximality `sigma_p(u) <= chi^N_p`. At finite clusters this is immediate from
  the Gram form. The proof route also proves it by a separate mass transport for
  all `p`, including when clusters are infinite.

## 2. Where the dictionary breaks: `L^1` does not give `L^infinity` from invariant-percolation structure

**Proposition W (type-(ii) witness with finite clusters).**

*Setup.* Let `Gamma = F_2 x Z`, `S ∋ (a,0)`, `N = 0 x Z` and `Q = F_2`.

- Fix a law `w` on `{1,2,...}` with mean `mu = sum L w_L < infinity` and
  `sum L^2 w_L = infinity`, for example `w_L ∝ L^(-5/2)`.
- For each left coset `C = g<a> x {n}`, choose independently a stationary
  renewal partition of `C ≅ Z` into consecutive blocks with gap law `w`. The
  identification is `g a^k -> k`, and it is well defined up to translation.
  Left multiplication maps cosets to cosets and preserves the order along `a`,
  so the resulting random partition of `Gamma` into finite connected pieces is
  `Gamma`-invariant.

*Conclusion.* Let `K_o` be the piece of `o`. Its length `L` has the size-biased
law `L w_L / mu`, and `o` is uniform in it. Then:

```text
sigma(a^j) = E[(L - |j|)_+ / L],     sigma = 0 off <a>,
chi^N = sigma(e) = 1,
||lambda_Q(sigma)|| = sum_j sigma(a^j) = E|K_o| = sum L^2 w_L / mu = infinity.
```

The norm identity holds because `sigma >= 0` is supported on the amenable
subgroup `<a>`, where the norm of a nonnegative function is its `l^1` norm.

So the fibre operator is in `L^1(L(Q))` but not in `L(Q)`. This happens:

- for an invariant random partition into finite connected clusters;
- with a positive definite, first-moment-maximal `sigma`;
- with the exact Gram form of Section 1.

The deterministic partition into the cosets `g<a> x {n}` gives the same with
infinite clusters: `sigma = 1_<a>`.

**Class kill.** Consider arguments that use only the following properties:

- invariance;
- finite clusters, possibly at criticality;
- positive definiteness and fibre maximality of `sigma`;
- the Gram form of `A_p`;
- any other identity derived by mass transport from the partition structure
  alone.

No such argument can prove `A_p ∈ L^1 => A_(p') ∈ L^infinity`.

- **Named invariant:** the size-biased squared Kesten ratio `E[|K_o| r(a)^2]`.
  Here `r(a) = ||lambda_Q(a)||/||a||_1`.
- **Where it dies:** the witness has clusters confined to cosets of an amenable
  subgroup, so `r(a) = 1`. Then `E[|K_o| r(a)^2] = E|K_o| = infinity`, even
  though `tr A = 1`.

Any proof of conjecture E, and any proof of critical fibre l2, must therefore
use a Bernoulli-specific input that prevents critical clusters from
concentrating their shadow on amenable pieces of `Q`. Examples of such inputs
are Russo's formula, BK, and insertion tolerance. That prevention is exactly the
content of `fpbs-critical-profile-kesten-ratio-integrable`.

**Consistency with Bernoulli percolation.** Insertion tolerance does not remove
the obstruction by itself. A critical Bernoulli cluster contains a straight
segment along `a` of length about `log |K|`. That segment contributes only
`O(log |K|)` to `||lambda_Q(a)||`, which is harmless. The danger is a cluster
whose whole shadow is amenable-like, with `r(a)` bounded below while `|K|` is
large. For nonamenable `Q` this has exponentially small cost per unit size in
mean-field heuristics. Nothing yet proves that.

## 3. Calibration: the structure used cannot be weakened to positive definiteness

On `F_2 x Z/2`, with `N = F_2 x 0` (nonamenable) and `Q = Z/2`, put
`tau(n,0) = delta_e(n)` and `tau(n,1) = 0.27 · 1_S(n)`, where `S` is the
symmetric free generating set, so `|S| = 4`.

- **Positive definiteness of `tau`.** The characters of `Z/2` reduce it to
  positive definiteness of `delta_e ± 0.27 · 1_S` on `F_2`. That holds because
  `0.27 · ||lambda(1_S)|| = 0.27 · 2 sqrt 3 ≈ 0.935 < 1`, by Kesten.
- **The fibre sums fail.** They are `sigma(0) = 1` and `sigma(1) = 1.08`, so
  `sigma` is neither maximal at `e` nor positive definite on `Z/2`.

`calibration_f2xz2.py` checks the arithmetic. It also finds the minimum
eigenvalue of the Gram matrix of `tau` on a ball of radius 4 to be `0.166`,
which is positive.

For amenable `N`, Følner averaging forbids this, as in the 2026-09-16 artifact.
For nonamenable `N`, the fibre maximality and positive definiteness proved in
`fpbs-normal-fibre-mass-cluster-gram-representation` therefore need cluster
(partition) structure, which mass transport supplies. They are not consequences
of positive definiteness of the two-point function.

## 4. Evidence for the Kesten-ratio claim: the tree proxy

**Test case.** `Gamma = Z/2*Z/2*Z/2`, `N` trivial, `Q = Gamma`, so the Cayley
graph is `T_3`, `p_c = 1/2`, and `a = 1_K`. By the Gram bound, the claim on this
case would imply `p_c < p_(2->2)`, which is true on trees. So this is a
consistency test and not new mathematics. The quantity
`E[||lambda(1_K)||^2/|K|]` could still diverge if the criterion were too lossy,
and it could fail only in that way. Since `P(|K| >= n) ≍ n^(-1/2)`, divergence
needs `||lambda(1_K)||^2/|K|` to grow like `|K|^(1/2)` on typical clusters.

**Method.** Both scripts give rigorous lower bounds on `||lambda(1_K)||`.

- `tree_cluster_kesten_ratio.py` takes the top singular value of the
  compression to a ball `B_R` around the centred cluster.
- `tree_cluster_power_lower_bound.py` takes the best Rayleigh quotient
  `||A xi||/||xi||` along pruned power iteration for `A^T A`. The value `A xi` is
  computed exactly, so the quotient is a valid lower bound whatever the pruning.

**Results.** The table gives the mean of `(lower bound)^2/|K|`, with the
maximum in brackets.

| size bin | mean `n` | power iteration (M=1500, 12 steps) | compression, R=11 |
|---|---|---|---|
| 8-16 | 10 | 6.78 (7.75) | 7.18 (8.11) |
| 16-32 | 21-22 | 8.86 (9.37) | 8.98 (10.72) |
| 32-64 | 42-46 | 10.39 (11.31) | 9.76 (12.02) |
| 64-128 | 89 | not completed within the run budget | 7.63 (10.90), not converged in R |

**Calibration sets**, compression with R = 11:

- balls of `n = 10, 22, 46, 94`: `7.1, 11.4, 16.0, 20.4`;
- alternating `ab`-segments inside the amenable subgroup `<a,b> ≅ D_infinity`,
  whose true value is `n`: `7.4, 12.1, 13.9` at `n = 8, 16, 32`.

The compression visibly underestimates long thin sets. So the power-iteration
column is the more reliable one.

**Reading.** Per doubling of `n`, the cluster statistic grows by factors of
about `1.31` and then `1.17`. The forbidden rate `|K|^(1/2)` would give `1.41`
per doubling. Clusters sit below metric balls of the same size, whose statistic
is about `(log n)^2` by the radial Haagerup estimate. That is consistent with
polylogarithmic growth, which is integrable against `n^(-3/2)`. These are lower
bounds at modest sizes. They can kill the claim but cannot confirm it.

**Mean-field heuristic.** Model the profile of a critical cluster of size `n`
by critical branching random walk projected to `Q`. Pairs at genealogical
distance `k` meet in one fibre with probability `O(rho^k k^(-3/2))`, where
`rho < 1` is the spectral radius of the projected step. So
`||a||_2^2 = O(n)`. Test vectors cannot gain more than the ball-like factor
`(log n)^2`, because the shadow is tree-like at scale `k` and nonamenable. On
that heuristic the claim holds. Turning the heuristic into a proof needs:

- a comparison of critical clusters with branching random walk, which is a
  triangle-type input;
- an upper bound on the volume tail.

That is the same wall as in `fpbs-critical-sphere-fibre-operator-below-one`.
The new point is that the quantity to control is quenched, one cluster at a
time.

## 5. Open points

1. **Positive definiteness in the gap window.** Is `sigma_p` positive definite
   for `p_c < p < p_c(N;G)`, where clusters are infinite but have finite
   profile? Item 1 still holds there. The Gram root `1/|K|` does not exist,
   and no invariant substitute has been found.
2. **The killing test on `F_2 x Z` along `Z`**, with shadows in `F_2`. See
   `fpbs-critical-profile-kesten-ratio-integrable`.
3. **A converse.** Does critical fibre l2 imply boundedness of
   `E[|K| r(a)^2]`? That is, is the Gram criterion lossless for Bernoulli
   percolation? The witness of Section 2 does not decide this, since it is not
   Bernoulli.
