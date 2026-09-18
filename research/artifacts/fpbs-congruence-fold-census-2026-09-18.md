# Fold density of profinite witnesses is a finite percolation number; congruence census

swarm-0917-w11-w11-fp-last1, September 18, 2026. Lane: paradigm/decomposition
toward `fpbs-fixed-price-universal`, via `fpbs-mal-bernoulli-single-stage-floor`.
Experiments: `experiments/fpbs-congruence-fold-census-2026-09-17/`.

## 0. Setting and notation

- `L = F(a, b)`, `phi(a) = a`, `phi(b) = b a b^{-2}`, `t_j = phi^j(b)`, so
  `t_{j+1} = t_j a t_j^{-2}` and `L_j = phi^j(L) = <a, t_j>`, free on `(a, t_j)`.
- For an L-set `Y` (a p.m.p. action, or a finite set with counting measure),
  the *triples* are `T_y = (y, a y, b y)`, one per `y`, members counted with
  multiplicity. `cl(S)` is the closure of `S` under "if at least two positions
  of a triple are in the set, add the whole triple".
- `sigma_b(X) = inf { mu(A) : cl(A) conull }` for a p.m.p. action `X`.
  For a finite L-set `Q`, `r(Q) = min { |S| : cl(S) = Q }` and the *density*
  is `r(Q)/|Q|`.
- Fold theorem (`[[fpbs-mal-fold-closure-exactness]]`, ESTABLISHED): for a free
  action, `E_K v b|_A = E_L` iff `cl(A)` is conull, with `K = <a, b a b^{-2}>`.
  Hence `relC(E_X; E_{X|K}) <= sigma_b(X)`.
- For an action `X` of `L`, write `X∘phi^j` for the L-action in which `a` acts
  as `a` and `b` acts as `t_j`. It is free when `X` is free, since `phi^j` is an
  isomorphism `L -> L_j` and a restriction of a free action is free.

**Depth bound (D).** Let `Q_j(X)` be the least cost of a graphing inside `E_X`
that promotes `E_{X|L_{j+1}}` to `E_{X|L_j}` (the deep-promotion quantity of
`research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md`). Then

```text
Q_j(X) <= sigma_b(X∘phi^j)      for every free X and every j >= 0.
```

*Proof.* `L_{j+1} = <a, t_j a t_j^{-2}>` is the fold subgroup of the free pair
`(a, t_j)` of `L_j`. Apply the fold theorem to the free `L`-action `X∘phi^j`:
for any `A` with conull closure on the triples `(y, a y, t_j y)`, the graphing
`t_j|_A`, of cost `mu(A)`, promotes `E_{X|L_{j+1}}` to `E_{X|L_j}`. Take the
infimum over `A`. QED

## 1. Proposition P: profinite fold density is a finite percolation limit

Let `X = lim_n Q_n` be a profinite action: `Q_n` are finite transitive L-sets
with equivariant surjections `Q_{n+1} -> Q_n`, `X` is the inverse limit with the
limit of uniform measures, and `pi_n : X -> Q_n` are the projections. (No
normality and no freeness is needed for P itself.)

**Proposition P.** `sigma_b(X) = lim_n r(Q_n)/|Q_n| = inf_n r(Q_n)/|Q_n|`.

**Lemma P0 (projected derivations).** Let `pi : Y -> Q` be an equivariant map of
L-sets and `S ⊆ Q`. For every `k`, the `k`-step closure satisfies
`cl_k(pi^{-1} S) = pi^{-1} cl_k(S)`; hence `cl(pi^{-1} S) = pi^{-1} cl(S)`.

*Proof.* A point `y` outside a set `U` enters at the next step iff for one of
the three positions `p` it can occupy (`y = T_z[p]` with `z = y, a^{-1} y,
b^{-1} y`), the other two positions of `T_z` are in `U`. This is a fixed
monotone formula in the membership of `y, a^{±1} y, b^{±1} y, b a^{-1} y,
a b^{-1} y`. In `Q`, with multiplicities, the same formula is exactly the
multiset rule: if `q` fills two positions of one triple, the only other
position cannot bring the count of in-set positions to 2, and the formula also
fails because it requires a position filled by `q`. Since `pi` commutes with
the generators, the formula for `y` equals the formula for `pi(y)`. Induct on
`k`. QED

*Proof of P.*
- *Monotone.* Applying P0 to `Q_{n+1} -> Q_n` gives
  `r(Q_{n+1})/|Q_{n+1}| <= r(Q_n)/|Q_n|`, so the limit exists and equals the
  infimum.
- *(<=).* If `cl(S) = Q_n`, then P0 gives `cl(pi_n^{-1} S) = X`, and
  `mu(pi_n^{-1} S) = |S|/|Q_n|`.
- *(>=).* Let `cl(A)` be conull and `eps > 0`. Since `cl(A)` is the increasing
  union of the `cl_k(A)`, fix `k` with `mu(cl_k(A)) > 1 - eps`. Membership in
  `cl_k(A)` is a monotone Boolean formula in `1_A(g x)` for `g` in a finite set
  `W_k ⊂ L` of size `M`. Cylinders are dense, so for some `n` there is `S ⊆ Q_n`
  with `mu(A Δ pi_n^{-1} S) < eps / M`. Off the set
  `U(x) = ⋃_{g in W_k} g^{-1}(A Δ pi_n^{-1} S)`, of measure `< eps`, the formula
  takes the same value for `A` and `pi_n^{-1} S`. So
  `mu(cl_k(pi_n^{-1} S)) > 1 - 2 eps`, and by P0 `|cl(S)| >= (1 - 2 eps)|Q_n|`.
  Adding the points of `Q_n \ cl(S)` as seeds gives
  `r(Q_n)/|Q_n| <= |S|/|Q_n| + 2 eps < mu(A) + 3 eps`. QED

**What P replaces.** Proposition F of the w10 node
`fpbs-mal-promotion-cost-monotone-under-weak-containment` (commit `350d52a0f`,
not in this worktree) is a finite-level problem for the full promotion cost,
and it must keep the Cayley tree. For the single label `b`, P needs no tree:
the fold density of a free profinite witness is the limit of an explicit
finite hypergraph invariant. In particular:

```text
Q_j(X) <= inf_n r(Q_n∘phi^j)/|Q_n|,
```

where `Q_n∘phi^j` is `Q_n` with `b` acting as `t_j`. This follows from (D) and P.

**Sofic direction (one-sided only, not used below).** For finite L-sets `Y_u`
and their Loeb ultraproduct action `X_u`, the (>=) argument above, with
internal sets in place of cylinders, gives
`sigma_b(X_u) >= lim_u r(Y_u)/|Y_u|`. The reverse inequality does not
transfer: a percolating seed set of `Y_u` may need unboundedly many steps, and
only bounded-depth derivations pass through the ultralimit. So for sofic
witnesses a finite census gives lower bounds on `sigma_b`, while for profinite
witnesses P gives the exact value.

## 2. Amenable-quotient kills at every depth

**Corollary P1 (factor bound).** If a p.m.p. action `X` has finite factors
`Q^{(N)}` (equivariant maps onto finite L-sets with uniform measure) and
`r(Q^{(N)})/|Q^{(N)}| -> 0`, then `sigma_b(X) = 0`. This is the (<=) half of P,
which uses only Lemma P0. If this holds for `Q^{(N)}∘phi^j` for every `j`, then
by (D) `Q_j(X) = 0` for every `j` when `X` is free.

**Lemma C (characters).** Let `chi : L -> Z` with `chi(a) = alpha`,
`chi(b) = beta`, `(alpha, beta) != (0, 0)`, and let `Z/N` carry
`a y = y + alpha`, `b y = y + beta`. Then the interval
`I = {0, ..., |alpha| + |beta| - 1}` percolates, for every `N`.

*Proof.* The triple of `y` is `(y, y + alpha, y + beta)`. Write
`m = |alpha| + |beta| >= 1`. If `m >= N` all of `Z/N` is seeded. Otherwise
suppose an interval `J` of `M` consecutive residues, `m <= M < N`, is in the
set; we show one neighbouring residue is added. Swapping `alpha, beta` permutes
each triple, and negating both mirrors `Z/N`, so there are three cases, with
`J = [0, M)`:
- `0 <= alpha < beta`: take `y = M - beta >= 0`. Then `y` and
  `y + alpha < M` lie in `J`, which adds `M = y + beta`. When `alpha = 0` the
  position `y` counts twice.
- `alpha < 0 < beta`: take `y = M - beta`. Then
  `0 <= M - m <= y + alpha < y < M`, so both lie in `J`, which adds `M`.
- `alpha = beta > 0`: the triple of `y = -1` is `(-1, alpha - 1, alpha - 1)`,
  and `alpha - 1` lies in `J` and fills two positions, which adds `-1`.
The interval grows by one residue per step until it is all of `Z/N`. QED

Under `phi`, `chi(t_{j+1}) = alpha - chi(t_j)`, so `chi∘phi^j` takes the values
`(alpha, beta)` and `(alpha, alpha - beta)` alternately, and is never zero.
Hence:

**Kill K1.** Every free action with a factor onto `Z/N` along a nonzero
character, for infinitely many `N` (for example a product with a
`chi`-odometer), has `sigma_b(X∘phi^j) = 0` and `Q_j = 0` for all `j`. This
generalizes the seed interval of Lemma 2.1 in
`research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`, which uses
`chi(a) = 1`, to all nonzero characters, and adds the all-depth statement.

**Lemma Dh (dihedral).** Let `D_N = <r, s | r^N, s^2, (s r)^2>` act on itself by
left multiplication, with `a -> r`, `b -> s` (or `a -> s`, `b -> r`). Then the
two seeds `{e, s}` percolate, for every `N >= 2`.

*Proof.* Write `r^k s^e` as `(k, e)`, so `r (k, e) = (k + 1, e)` and
`s (k, e) = (-k, 1 - e)`. The triple of `g` is `(g, r g, s g)`. Swapping the
roles of `a` and `b` permutes each triple, so both cases have the same
closure. Steps:
- From `T_{(0,0)} = ((0,0), (1,0), (0,1))` and
  `T_{(0,1)} = ((0,1), (1,1), (0,0))`, add `(1,0)` and `(1,1)`.
- *Induction.* Suppose `(k, e)` is in the set for all `|k| <= m` and both
  `e`, with `m >= 0`, and also `(1, 0), (1, 1)` when `m = 0`. Then:
  - `T_{(m,0)} = ((m,0), (m+1,0), (-m,1))` adds `(m+1, 0)`;
  - `T_{(m,1)} = ((m,1), (m+1,1), (-m,0))` adds `(m+1, 1)`;
  - `T_{(-m-1,0)} = ((-m-1,0), (-m,0), (m+1,1))` adds `(-m-1, 0)`;
  - `T_{(-m-1,1)} = ((-m-1,1), (-m,1), (m+1,0))` adds `(-m-1, 1)`.
  So the claim holds for `m + 1`.
Indices are mod `N`, so after `m = N/2` everything is in the set. QED

Exact enumeration agrees (`dihedral_two_seeds_out.txt`): `{e, s}` and `{e, r}`
percolate for `N = 2..15, 31, 64, 101`, and `perc.c` finds 2 seeds for
`N = 100, 1000, 10000` in three generator modes (`census_dih_out.txt`).

**Depth stability.** If `t_j -> r^m s`, then
`t_{j+1} = t_j a t_j^{-2} -> r^m s r = r^{m-1} s`, so `t_j -> r^{-j} s`.
Since `s -> r^{-j} s`, `r -> r` extends to an automorphism of `D_N`, the
L-set `D_N∘phi^j` is isomorphic to `D_N`, and its density is `1/N`.

**Kill K2.** Every free action with the regular `D_N` factors (via
`a -> r`, `b -> s`) for infinitely many `N` has `sigma_b(X∘phi^j) = 0` and
`Q_j = 0` for all `j`. Its abelianization image is finite, so K2 is not
covered by K1.

**Reading.** Witnesses with factor towers of type K1 or K2 die at the
single-label level at every depth, with `O(1)` seeds per level. These are
towers of cyclic or dihedral quotients, both virtually abelian. Other
virtually abelian towers are not treated here. By Corollary 2
of the w10 node, the floor needs witnesses `a_j` with `Q_j(a_j) >= c`. Such
witnesses cannot have factors of type K1 or K2, at any depth.

## 3. Census: congruence towers against controls

**Instances** (`gen.py`). `sl2 m` is the orbit of `I` in `SL2(Z/m)` under the
Sanov matrices `a = [[1,2],[0,1]]`, `b = [[1,0],[2,1]]`, which generate a free
subgroup of index 12 in `SL2(Z)`. Along `m = p^k` these are the levels of a
free profinite action of `L`, namely left translation on the closure of the
image of `L` in `SL2(Z_p)`. It is free because `L` embeds there. `sl2d m j` is
the same with `b` replaced by `t_j`, that is `Q_n∘phi^j` restricted to one
orbit. All orbits of `Q_n∘phi^j` are isomorphic, so this does not change the
density. The controls are:
- `rand n s`: two uniform random permutations;
- `cyc N t`: `Z/N` with `a = +1`, `b = +t`;
- `dih N mode`: regular `D_N`;
- `prod m N`: `sl2 m` times `cyc N 1`.

**Method** (`perc.c`). Greedy seeding picks, among 64 scanned uninfected
points, the one completing the most triples. Redundant seeds are then pruned.
Every reported seed set is **re-verified** by closing it from scratch
(`verified_closure = n`). So each `best_s` is a certified upper bound on
`r(Q)`, and by P, `sigma_b(X) <= best_s/n` for the profinite `X` over that
level. Nothing below is a lower bound.

| instance | n | best_s | density |
|---|---|---|---|
| sl2 3 / 9 / 27 / 81 (3-adic) | 24 / 648 / 17496 / 472392 | 7 / 77 / 1910 / 54338* | .292 / .119 / .1092 / .1150* |
| sl2 5 / 25 (5-adic) | 120 / 15000 | 17 / 1639 | .142 / .1093 |
| sl2 7 / 49 | 336 / 115248 | 43 / 13319* | .128 / .1156* |
| sl2 p, p = 11..29 | 1320..24360 | | .102 - .117 |
| rand, n = 500..10000 | | | .1075 - .1100 |
| rand, n = 50000 / 200000 | | 5758* / 23058* | .1152* / .1153* |
| cyc N 7, N = 1000 / 10000 | | 7 / 7 | .0070 / .0007 |
| dih N, modes 0-2, N = 100..10000 | 2N | 2 | 1/N |
| prod 7 x 50 / 13 x 20 | 16800 / 43680 | 339 / 2277 | .020 / .052 |

`*` marks one to three unpruned trials, which are weaker upper bounds. The
monotonicity in P says the true level densities are nonincreasing along each
tower, so `.1150 > .1092` at level 81 is greedy slack, not growth.

**Certified.**

```text
sigma_b(3-adic Sanov action) <= 1910/17496 < 0.1092
sigma_b(5-adic Sanov action) <= 1639/15000 < 0.1093
```

**Depth** (`census_depth_out.txt`, `sl2d m j`, pruned):

| m | j = 0 | j = 1 | j = 2 | j = 3 |
|---|---|---|---|---|
| 25 (orbit 15000) | .1105 | .1088 | .1061 | .0918 |
| 9 (orbit 648 at j = 0, then 54) | .119 | .167 | .167 | .167 |
| 27 (orbit 17496 at j = 0, then 486) | .1097 | .1111 | .1111 | .1111 |

For `j >= 1` the image of `L_j` in `SL2(Z/3^k)` has index 12 or 36 in the image
of `L`. `X∘phi^j` then splits into finitely many isomorphic profinite
`L`-actions, and P applies to each one.

**Depth continuation** (`census_depth2_out.txt`, level 25, pruned):

| j | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|
| orbit | 15000 | 15000 | 500 | 500 | 500 |
| density | .1092 | .0803 | .0960 | .1020 | .0960 |

**Level 125** (`census_depth3_out.txt`, n = 1875000, one unpruned trial): the
densities are .1152 at `j = 0`, .1153 at `j = 3` and .1047 at `j = 5`. These are
above the level-25 values, which by the monotonicity in P is greedy slack, not
growth. The relative dip at `j = 5` persists across levels.

**Borel absorption** (`borel_absorption.py`, `depth_structure.py`). Since
`a` is upper triangular, the Borel subgroup `B(F_p)` is absorbing for
`t -> t a t^{-2}`. Once `t_j` lies in `B` mod `p`, the image of `L_j` mod `p`
is solvable. This happens for `p = 3` (from `j = 1`), `5` (`j = 6`), `7`
(`j = 5`), `11` (`j = 3`), `29, 31, 41, 59`. It never happens for
`p = 13, 17, 19, 23, 37, 43, 47, 53`, where `t_j` mod `p` enters a cycle
outside `B`.

The absorbed levels (`m = 9, 27` for `j >= 1`, and `m = 25` for `j >= 6`) do
**not** collapse: their densities are .096 to .167. So a solvable reduction
mod `p` is not a kill. The `p`-adic levels above it still expand, by
Bourgain-Gamburd for Zariski-dense subgroups; this is not needed here. At a
fixed level, `t_j` is eventually periodic in `j`, so each level density is
eventually periodic in `j`, and its infimum over `j` is a minimum over one
period. That minimum is positive. So the question whether
`inf_j sigma_b(X∘phi^j)` is positive depends only on how these per-level
minima behave as the level grows. No finite-level census decides it.

## 4. What the census changes

1. **W-prof is now a finite problem, for one label.** The single-label part of
   hole W-prof (w10) is a question about a finite hypergraph invariant: whether
   `inf_n r(Q_n∘phi^j)/|Q_n|` stays bounded away from 0 in `j`. Through (D)
   this quantity is an upper bound for `Q_j`, not a lower bound. So, for a
   profinite witness, a positive single-label density at every depth is
   **necessary but not sufficient** for being a floor witness.
2. **The kill class.** Two kinds of profinite witness are dead at every depth:
   those with cyclic factors along a nonzero character (K1), and those with
   regular dihedral factors with `a -> r`, `b -> s` (K2). The census shows the
   same collapse for the `prod` instances: `prod 7 x 50` already has density
   .020, against .128 for `sl2 7`. The census also finds 2 seeds for the
   dihedral mode `a -> s`, `b -> s r`, but only numerically; it is not proved
   here. A floor witness must avoid K1 and K2 factors at every depth.
3. **Congruence witnesses survive the b-level test.** The 3-, 5- and 7-adic
   Sanov towers and the primes 5 to 29 all plateau near .11. This matches the
   random Schreier value (`rand`: .108 to .115, and the w8 greedy value of about
   .11 in `experiments/fpbs-fold-seed-floor-2026-09-17/`). The expander quotients
   look like random 2-of-3 hypergraphs for this problem. Depth `j <= 3` shows no
   collapse at `m = 9, 27`. At `m = 25`, depths `j <= 8` stay between .080
   (`j = 5`) and .110; see `census_depth2_out.txt`. At level 125 the dip at
   `j = 5` persists, but it is not a collapse.
4. **Conjecture (not claimed).** For a free ergodic profinite action `X` of `L`,
   `sigma_b(X) > 0` iff `X` is strongly ergodic, that is, iff its levels form
   an expander family. The direction "not strongly ergodic implies 0" is proved
   here only for the K1 and K2 types. The census does not distinguish
   Selberg-type congruence expanders from random ones.

## 5. Not claimed

- No lower bound on `sigma_b`, `Q_j` or `r` for any witness. Every census
  number is a certified **upper** bound.
- No statement about the Bernoulli shift `rho` itself. By Theorem M of the w10
  node, witnesses bound `Q_j(rho)` from below only through Corollary 2 there,
  and that needs `Q_j(a_j) >= c`, which is a full promotion cost, not the
  single-label `sigma_b`.
- The plateau value .11 is numerical. It has no proof and no claimed limit.
- The conjecture in §4.4.
