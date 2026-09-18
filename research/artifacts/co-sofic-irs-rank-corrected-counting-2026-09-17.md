# Co-sofic IRS carry no strict design: rank-corrected statement and complete proof (2026-09-17)

Worker `swarm-0917-w6-w6-gs-last2`, lane paradigm/decomposition, last mile toward
`gottschalk-surjunctivity-conjecture`.

**Why this exists.** `co-sofic-irs-carry-no-strict-design` was demoted on 2026-09-17. Both referee lenses
refuted its *stated* inequality because one symbol `r` named both the rank of the free group and
`R_tau + R_sigma`. Read literally, `d_k` counts balls in the `2(R_tau+R_sigma)`-regular tree, and the
constant is too small. Both lenses found proof steps 1-5 sound once `d_k` is the ball size in the
`2*rank`-regular tree. That node's body may not be edited in this lane. So this artifact states the
corrected theorem as a new node, `co-sofic-free-group-irs-carry-no-strict-design`, and rewrites the full
proof with separate variables. Every step was re-derived here, not copied.

**Graph effect.** Route `irs-surjunctivity-via-rank-corrected-co-sofic-split` targets
`free-group-irs-carry-no-strict-design`. Its prerequisites are the corrected node (ESTABLISHED here) and
`non-co-sofic-free-group-irs-carry-no-strict-design`. That leaves exactly one open hole on the IRS route
to the goal (`gottschalk-via-irs-surjunctivity`, whose other prerequisite
`atomic-irs-strict-designs-are-nonsurjunctive-quotients` is ESTABLISHED).

No novelty is claimed. This is Gromov-Weiss counting, made robust to a density of forward failures.

## 1. Notation (one symbol per quantity)

- `m >= 1`: the rank. `Gamma = F_m`, free on `a_1..a_m`.
- `A`: a finite alphabet, `|A| >= 1`.
- `D = (tau, sigma)`: a design of shape-dependent automata with radii `R_tau` and `R_sigma`, as in
  Section 2 of `research/artifacts/irs-surjunctivity-heretic-2026-09-17.md`. Put
  `rho = R_tau + R_sigma`.
- `b_k = b_k(m)`: the number of vertices in the radius-`k` ball of the `2m`-regular tree, so `b_0 = 1`
  and `b_k = 1 + 2m((2m-1)^k - 1)/(2m-2)` for `m >= 2`, and `b_k = 2k+1` for `m = 1`.
- `X`: a finite set with a right `Gamma`-action, `N = |X|`. Its Schreier graph has an undirected edge
  `v -- v.a_i` for each `v` and `i`, with loops and multi-edges allowed. `dist` is the graph metric, and
  `B_k(v)` is the vertex set at distance `<= k` from `v`.

**Ball bound.** Every vertex of `B_k(v)` has the form `v.w` for a reduced word `w` of length `<= k`, so
`|B_k(v)| <= b_k`. For `S ⊆ X`, the set of vertices within distance `k` of `S` has at most `|S| b_k`
elements, because the metric is symmetric.

**Local dependence.** `(tau x)(u)` depends only on `x|B_(R_tau)(u)`, and `(sigma y)(u)` only on
`y|B_(R_sigma)(u)`. Hence `(sigma tau x)(v)` and `(tau sigma y)(v)` depend only on the restrictions to
`B_rho(v)`. This uses `B_(R_sigma)(u) ⊆ B_rho(v)` for `u in B_(R_tau)(v)`, and symmetrically.

**Definitions (artifact Section 2, with `rho` for `r`).**
- `v` is **forward-good** if `sigma(tau x)(v) = x(v)` for every `x in A^X`. By local dependence this is
  a condition on colourings of `B_rho(v)`, hence on the labelled shape of `B_rho(v)`.
- `v` is **reverse-bad** if some `p in A^(B_rho(v))` has `(tau sigma p)(v) != p(v)`, evaluated through
  any extension of `p` to `X`.
- `eps_X` is the fraction of vertices that are not forward-good, and `delta_X` the fraction that are
  reverse-bad.

## 2. Finite inequality

**Theorem 2.1.** For every finite `Gamma`-set `X`,

```text
delta_X <= C_D eps_X,   C_D = b_(R_tau) + b_(2 rho) |A|^(b_rho) ln|A| .
```

*Proof.* Let `Good ⊆ X` be the forward-good set, so `|X \ Good| = eps_X N`, and let `Bad` be the
reverse-bad set, `|Bad| = delta_X N`. If `|A| = 1` every map is the identity, `Bad` is empty and there is
nothing to prove. Assume `|A| >= 2`.

1. **Lower bound on the image.** Given `z in A^Good`, extend it to some `x in A^X`. Then
   `(sigma tau x)|Good = x|Good = z`. So `y -> (sigma y)|Good` maps `tau(A^X)` onto `A^Good`, and
   `|tau(A^X)| >= |A|^((1 - eps_X) N)`.
2. **Excluded patterns.** Let `v in Bad` with witness `p_v in A^(B_rho(v))`, and assume
   `B_(R_tau)(v) ⊆ Good`. Let `y = tau x`. For `u in B_(R_tau)(v)` forward-goodness gives
   `(sigma y)(u) = x(u)`. So `sigma y` and `x` agree on `B_(R_tau)(v)`, and
   `(tau sigma y)(v) = (tau x)(v) = y(v)`. If `y|B_rho(v) = p_v`, local dependence would give
   `(tau sigma y)(v) = (tau sigma p_v)(v) != p_v(v) = y(v)`, a contradiction. Hence
   `y|B_rho(v) != p_v` for every `y in tau(A^X)`.
3. **Counting the exceptions.** A vertex `v in Bad` with `B_(R_tau)(v)` not inside `Good` lies within
   distance `R_tau` of `X \ Good`. By the ball bound there are at most `eps_X N b_(R_tau)` of them. Let
   `Dset` be the remaining reverse-bad vertices, so `|Dset| >= (delta_X - eps_X b_(R_tau)) N`.
4. **Separation.** Choose `D' ⊆ Dset` greedily: pick a vertex, then delete every vertex within distance
   `2 rho` of it. Each pick deletes at most `b_(2 rho)` vertices, so `|D'| >= |Dset| / b_(2 rho)`. Distinct
   points of `D'` are at distance `> 2 rho`, so the balls `B_rho(v)`, `v in D'`, are pairwise disjoint.
5. **Upper bound on the image.** By step 2, `tau(A^X)` lies in the set of `y` avoiding `p_v` on
   `B_rho(v)` for all `v in D'`. The balls are disjoint, so

   ```text
   |tau(A^X)| <= |A|^N prod_(v in D') (1 - |A|^(-|B_rho(v)|)) <= |A|^N (1 - |A|^(-b_rho))^|D'| .
   ```

   The second inequality uses `|B_rho(v)| <= b_rho`.
6. **Combine.** Take logarithms of steps 1 and 5 and use `ln(1-u) <= -u` with `u = |A|^(-b_rho)`:

   ```text
   (1 - eps_X) N ln|A| <= N ln|A| - |D'| |A|^(-b_rho) .
   ```

   So `|D'| <= eps_X N |A|^(b_rho) ln|A|`. With steps 3 and 4,

   ```text
   (delta_X - eps_X b_(R_tau)) N <= |Dset| <= b_(2 rho) |D'| <= eps_X N b_(2 rho) |A|^(b_rho) ln|A| ,
   ```

   which is the claim. QED

Transitivity of `X` is never used. Each step is a statement about one finite graph, and the only
graph-theoretic input is the ball bound, which is where the rank `m` enters.

## 3. Passage to co-sofic IRS

For an IRS `mu` of `Gamma`, `eps_D(mu)` is the probability that the root `H` of `H\Gamma`, `H ~ mu`, is
not forward-good, and `delta_D(mu)` is the probability that it is reverse-bad.

1. **Clopen events.** The labelled rooted ball `B_rho(H)` in `H\Gamma` is determined by which words of
   length `<= 2 rho + 1` lie in `H`. So "root forward-good" and "root reverse-bad" are finite Boolean
   combinations of the clopen sets `{H : w in H}` in `Sub(Gamma)`. Hence `eps_D` and `delta_D` are
   weak-* continuous and affine in `mu`.
2. **Finite sets.** Let `mu_X` be the law of `Stab(o)` for `o` uniform in `X`. The map
   `o.g <-> Stab(o) g` is an isomorphism of rooted labelled graphs from the orbit of `o`, rooted at `o`,
   to `Stab(o)\Gamma`, rooted at `Stab(o)`. Both properties depend only on `B_rho` of the root, and
   `B_rho(o)` lies in the orbit. So `eps_D(mu_X) = eps_X` and `delta_D(mu_X) = delta_X`.
3. **Closure.** By Theorem 2.1 and item 2, the closed convex set `{mu : delta_D(mu) <= C_D eps_D(mu)}`
   contains every `mu_X`. It therefore contains the weak-* closure of `{mu_X}`, which by definition is
   the set of co-sofic IRS. Convexity is not even needed.
4. **No strict design.** A strict design has `eps_D(mu) = 0 < delta_D(mu)`, which violates the
   inequality.

**Theorem 3.1.** Let `m >= 1`, `A` a finite alphabet, and `D` a design on Schreier graphs of `F_m` with
radii `R_tau`, `R_sigma`. Every co-sofic IRS `mu` of `F_m` satisfies

```text
delta_D(mu) <= ( b_(R_tau) + b_(2 rho) |A|^(b_rho) ln|A| ) eps_D(mu),   rho = R_tau + R_sigma,
```

where `b_k` is the size of the radius-`k` ball in the `2m`-regular tree. In particular, no co-sofic IRS
of a free group carries a strict design.

## 4. Calibrations

- **Referee lens 1 counterexample** (`F_20`, `|A| = 2`, `R_tau = 0`, `R_sigma = 1`): `eps = 1/39` and
  `delta = 1`. The corrected constant is `b_0 + b_2 2^(b_1) ln 2` with `b_1 = 41` and `b_2 = 1601`,
  which is far above 39. The inequality holds.
- **Referee lens 2 counterexample**, same parameters. Re-checked by hand:
  - The loop vertex `u` is forward-bad and reverse-bad.
  - Its `2m - 2 = 38` loop-free neighbours are forward-good, because `y(u) = 0` on the image. They are
    reverse-bad with witness `p(u) = 1`, `p(w) = 0`.
  - No other vertex is reverse-bad.
  - So `delta/eps = 2m - 1 = 39`. The corrected constant exceeds it.
- **The rank dependence is necessary, not an artefact of the proof.** The lens 2 family works on every
  `F_m` with `m >= 2`, using one `a_1`-fixed point with `2m - 2` distinct loop-free neighbours. There
  `R_tau = 0`, `R_sigma = 1`, `|A| = 2` are fixed while `delta/eps = 2m - 1`. So no constant depending
  only on `(R_tau, R_sigma, |A|)` can be valid, and the demoted statement fails exactly because its
  `d_k` ignores `m`.
- **Vertex-transitive calibration.** On `X = Gamma/N` finite, `eps_X` is 0 or 1. With `eps = 0` the
  theorem gives `delta = 0`: an injective automaton on a finite group with a left inverse is bijective,
  which is correct.
- **Where the proof needs co-soficity.** Steps 1 and 5 compare two cardinalities of finite sets. The
  non-unimodular end-fixing tree calibration (`end-fixing-tree-symmetries-carry-strict-automata`) has a
  strict automaton and no finite approximations, which is consistent with this.
- No computation was run. Every step is an elementary finite count.

## 5. What remains on the route

`gottschalk-via-irs-surjunctivity` needs `free-group-irs-carry-no-strict-design` and the ESTABLISHED
`atomic-irs-strict-designs-are-nonsurjunctive-quotients`. The new split route needs this theorem and
`non-co-sofic-free-group-irs-carry-no-strict-design`. After this lane, that is the only open hole on the
IRS route. It is Gottschalk-strength for non-sofic groups, since its atomic part contains
`delta_N` for non-sofic `F_m/N`. The live branch is nonatomic IRS supported on infinitely generated
subgroups; see that node's Attempts.
