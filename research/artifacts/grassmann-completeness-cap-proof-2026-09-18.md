# Feed the exact Grassmann spectral gap into the ratio gate, then close the converse with a counting argument for a low-value unique game on the same graph

*Attempt artifact (2026-09-18), formerly route `grassmann-completeness-cap-proof`
into `grassmann-hosted-unique-games-cap-completeness`, requires
[grassmann-graphs-have-constant-normalized-spectral-gap,
spectral-gap-ratio-reductions-cannot-prove-ugc]. Demoted from the graph at
landing because all three swarm-0917 referee lenses returned `refuted` on the
parent result `unique-games-hard-on-non-sse-grassmann-constraint-graphs`. All
three lenses checked steps (1)-(4) below --- the gap, the domination lemma, the
(K1) gate arithmetic, the AKKSTV bridge and the Chernoff/union-bound converse
--- and found them sound; the step they refuted is step (5), which proves
Theorem D of the target claim. See the `## Attempts` section of that claim for
the verbatim reason. Restore this as a route once step (5) and Theorem D are
restated and a full referee pass survives.*

Notation is that of the target claim.

## (1) The gap of a Grassmann-hosted constraint graph

Let `U` be Grassmann-hosted with density `rho`, on `Gr_q(n,l)` with weighted
graph `W`, common weighted degree `d`, and `W >= (rho d/d_1) A_1` entrywise.
Theorem 5 of `grassmann-graphs-have-constant-normalized-spectral-gap`, applied
with `c = rho d/d_1`, gives

```text
lambda_2(W)  >=  (rho d/d_1) d_1 lambda_2(Gr_q(n,l)) / d  =  rho lambda_2(Gr_q(n,l)),
```

and Theorem 3 of the same claim gives `lambda_2(Gr_q(n,l)) > (q-1)/q >= 1/2`.
So

```text
lambda_2(W)  >  rho (q-1)/q  >=  rho/2,                                     (1)
```

uniformly in `n`, `l`, `q` and in the alphabet of `U`. `W` is loop-free and
weighted-regular by hypothesis, which are the two shape hypotheses that (K1)
quotes. (K1) reads weights as multiplicities, so `W` must have rational weights;
clearing denominators turns a weighted-regular rational `W` into a regular
loop-free multigraph with the same normalized Laplacian, hence the same
`lambda_2` and the same game value. Instances produced by a polynomial-time
reduction are finite objects with rational weights, so this costs nothing.

## (2) Theorem A

Fix `s < 1` and `rho > 0`, and let `eta < rho(q-1)/(q X(s))`. Let `U` be
Grassmann-hosted of density `>= rho` with `opt(U) >= 1 - eta`. By (1),

```text
lambda_2(U)  >  rho (q-1)/q  >  X(s) eta  >=  X(s) (1 - opt(U)),
```

and `lambda_2(U) > 0`. These are exactly the YES hypotheses of bullet (K1) of
`spectral-gap-ratio-reductions-cannot-prove-ugc`, whose decider is: run the
AKKSTV rounding on `U` and accept iff the returned labeling has value `> s`.
(K1) proves that this accepts every instance satisfying the YES hypotheses and
rejects every instance with `opt <= s`, in polynomial time. So the same decider
solves `Gap-UG[1 - eta, s]` on this promise class, which is the algorithm; and
composing it with a reduction `f` as in the statement decides `L` in polynomial
time, which is the gate. Since `(q-1)/q >= 1/2` for every `q >= 2`, the weaker
threshold `eta < rho/(2X(s))` always suffices. Replay (C10) checks the
arithmetic `lambda_2 >= X(s) eta` for a range of `C_A`, `s`, `q`, `n`, `l`.

*Where every member of the class dies.* At the YES output, before any soundness
analysis, and the invariant is the second eigenvalue of the output constraint
graph --- equivalently, by Theorem 4 of the graph claim, the zoom-in expansion
`q^(l-1)/[l]`, which is the same number.

## (3) Theorem B

Contrapositive of Theorem A. If `Gap-UG[c, s]` were NP-hard on Grassmann-hosted
instances of density `>= rho` with `c > 1 - rho(q-1)/(q X(s))`, then the
reduction witnessing NP-hardness has `eta = 1 - c < rho(q-1)/(q X(s))` and
Theorem A puts 3SAT in P. The second inequality of Theorem B is
`(q-1)/q >= 1/2`.

## (4) Theorem C

*Forward.* Apply Theorem A with `rho = 1`, `s = delta` and any
`eta < 1/(2X(delta))`; H3 supplies a reduction from 3SAT at that `eta`, so
3SAT in P and `P = NP`.

*Backward.* Assume `P = NP`. Fix `eta, delta > 0`. Two constant-size instances
suffice, because `eta` and `delta` are constants:

* a YES instance: take any `Gr_q(n,l)` and give every edge the identity
  permutation of a two-letter alphabet. All weighted degrees are equal, there
  are no loops, the edge law is uniform on the Grassmann relation so `rho = 1`,
  and the value is `1 >= 1 - eta`.
* a NO instance: we claim that for `k = ceil(2/delta)` and any `Gr_q(n,l)` with
  degree `d_1 > 6 k ln k`, some assignment of permutations of `[k]` to the edges
  gives a unique game of value `< 2/k <= delta`. Draw the permutations
  independently and uniformly. For a fixed labeling `L : V_l -> [k]` the events
  "edge `e` is satisfied" are independent across edges with probability `1/k`
  each, so the number of satisfied edges has mean `mu = |E|/k` and, by the
  multiplicative Chernoff bound, `Pr[val(L) >= 2/k] <= exp(-mu/3)`. There are
  `k^N` labelings, `N = |V_l|`, and `|E| = N d_1/2`, so a union bound gives
  failure probability at most

  ```text
  exp(N ln k - N d_1/(6k))  <  1     whenever   6 k ln k < d_1.
  ```

  Since `d_1 = q[l][n-l] -> infinity` with `n`, such `(q, n, l)` exist for every
  `delta`. Fix one such game once and for all.

The reduction is: decide satisfiability of the input formula in polynomial time
(possible because `P = NP`), and output the hard-wired YES or NO instance. Both
are Grassmann-hosted with density `1`, and the value promises hold. So H3 holds.

## (5) Theorem D

The first bullet is Theorem 4 of `grassmann-graphs-have-constant-normalized-spectral-gap`
read against the `Gap-SSE` promise: a YES instance of `Gap-SSE(eta, delta)`
carries a set of measure `delta` with `Phi <= eta`, while every set of measure
`mu` in `Gr_q(n,l)` has `Phi >= (1-mu)(q-1)/q`; at `mu = delta` these are
incompatible when `eta < (1-delta)(q-1)/q`. The second and third bullets are the
equality statement of that same theorem: `Phi(Z_x) = (1 - mu(Z_x)) lambda_2` and
`Phi(Z^H) = (1 - mu(Z^H)) lambda_2` exactly, so `1_(Z_x) - mu` and
`1_(Z^H) - mu` lie in the second eigenspace and the zoom sets carry no
information about the graph beyond `lambda_2` itself.

## (6) The escapes named in the target

* *Density.* Hypothesis 3 of the definition cannot be dropped. Fix `x != 0`,
  put `S = Z_x = {L : x in L}`, and for `e > 0` weight the Grassmann edges by

  ```text
  a  inside S,        b  inside V_l \ S,        e  across the cut.
  ```

  Let `H = Stab_(GL_n(F_q))(x)`. `H` acts transitively on `S` (it surjects onto
  `GL(F_q^n/<x>)`, which is transitive on the `(l-1)`-spaces of the quotient)
  and transitively on `V_l \ S` (given `L` with `x notin L`, the set
  `{x} u basis(L)` is independent, so any two such `L` are carried to one
  another by an element fixing `x`). So the inside-degree and the cut-degree are
  constant on `S` and constant on `V_l \ S`, and `a, b > 0` can be chosen, for
  each `e`, to make all weighted degrees equal. The resulting `W` is loop-free,
  weighted-regular and supported on Grassmann edges, and
  `Phi_W(S) = e . cut(S)/vol_W(S) -> 0` as `e -> 0` with the total weight
  normalized, so by (K4) of `spectral-gap-ratio-reductions-cannot-prove-ugc`
  `lambda_2(W) <= Phi_W(S)/(1 - mu_W(S)) -> 0`. Its density is
  `rho = e d_1/d -> 0`, exactly as the theorem demands. So `rho` is a genuine
  parameter of the kill and not a convenience: the DKKMS test survives only
  because its edge law is *uniform* on the Grassmann relation.
* *Regularity.* By Theorem 6 of the graph claim the bipartite containment host
  has gap `> 1 - q^(-1/2)`, so if (K1) is extended past its regular hypothesis
  (S1) --- either by a proof that the AKKSTV rounding tolerates biregular
  bipartite constraint graphs, or by a value-preserving regularization at
  completeness `1 - eta` versus soundness `delta` --- then Theorems A--C apply
  verbatim to orientation lifts of bipartite 2-to-1 games on the Grassmann
  poset, and in particular to
  `parity-leaking-branch-selectors-reach-near-perfect-completeness`. That
  extension is *not* claimed here.
