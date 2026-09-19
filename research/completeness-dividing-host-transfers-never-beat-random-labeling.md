---
rg: 2
id: completeness-dividing-host-transfers-never-beat-random-labeling
kind: claim
title: On Grassmann and Johnson hosts every unique game with alphabet k has value at least 1/k, planted shift games pin every algorithmic guarantee at completeness c' to at most c' + 1/K, so the orbit-split transfer (Corollaries T and BM, loss k) and the coset lift (loss (k-1)!) certify nothing beyond random labeling; the dominated orbit split repairs the transfer with loss tau(U) independent of k
distinct_from:
  unique-games-reduce-to-shifts-over-their-holonomy-group: that proves the holonomy reduction and states Corollaries T and BM and a class kill at soundness delta(c/k); this shows those guarantees are at most the 1/k random floor, so the kill is void, and replaces the loss k by the dominating number tau(U).
  general-unique-games-easy-on-globally-hypercontractive-graphs: that is the open root; this shows its literal statement (delta allowed to depend on k) holds trivially with delta = 1/k, and that the intended content needs delta independent of k.
  dummy-padding-cannot-beat-the-random-guessing-floor: that is a 2-to-1 padding floor; this is the unique-games random floor applied to host-preserving transfers.
  ugc-is-equivalent-to-affine-ugc: that is the KKMO equivalence, which changes the graph; this is about transfers on a fixed host and says nothing about KKMO.
artifacts:
  - experiments/ugc-random-floor-2026-09-17/check_random_floor.py
  - experiments/ugc-random-floor-2026-09-17/output.txt
---

**ESTABLISHED.** Route: `completeness-dividing-transfers-random-floor-proof`.

**Setting.** A host is `Grass(n, l)` (vertices the `l`-subspaces of `F_2^n`,
adjacent when `dim(L cap L') = l - 1`) or the Johnson graph `J(n, l, alpha l)`.
Both are loop-free, vertex-transitive and `d`-regular, with `d -> infinity` as
`n -> infinity` at fixed `l, alpha`. For Grassmann,
`d = (2^l - 1)(2^(n-l+1) - 2)`. A *guarantee* of an algorithm on a class `C`
of instances is a function `delta(c')` such that the algorithm finds a labeling
of value `>= delta(c')` on every instance in `C` of value `>= c'`.

**Theorem.**

1. *(Random floor.)* Every weighted unique game with alphabet `[k]` on a
   loop-free graph has value `>= 1/k`. A labeling of value `>= 1/k` is found
   deterministically in time `poly(|E|, k)` by conditional expectations. So the
   root claim `general-unique-games-easy-on-globally-hypercontractive-graphs`,
   as literally stated ("Fix `l`, the alphabet `k`, `alpha` and `c > 0`. There
   are `delta > 0` and a polynomial-time algorithm ..."), holds with
   `delta = 1/k`. The same goes for each of its rungs R1--R4 and for
   Corollary BM of `unique-games-reduce-to-shifts-over-their-holonomy-group`.
2. *(Planted ceiling.)* Let `A` be any group of order `K`, let `0 <= c' < 1` and
   `eps > 0`, and let the host have `N` vertices and degree `d` with
   `eps^2 d >= ln K + 1`. Then there is a left-shift game `x_v = b_e x_u` over
   `A` on the host with
   `c' <= val <= c' + (1 - c')/K + 2 eps`.
   Taking `c' = 0`, there is one with `val <= 1/K + eps`. Hence every guarantee
   on `A`-shift games on these hosts obeys
   `delta(c') <= c' + (1 - c')/K`. A guarantee that does not depend on the
   alphabet, like Bafna--Minzer Theorem 1.7's, obeys `delta(c') <= c'`.
3. *(Orbit-split transfer is void.)* The `c' = 0` instances of item 2 over
   `Z_k` have value `>= 1/k >= c/k` by item 1 and value `<= 1/k + eps`. So
   Corollary T certifies `min_(q <= k) delta(c/k, q) <= delta(c/k, k) <= 1/k`,
   and Corollary BM certifies `delta_BM(c/k) <= 1/k`. Neither beats item 1. The class kill
   in "What it kills" of the holonomy node ("no soundness below `delta(c/k)` is
   possible") is void, because every instance it covers has value
   `>= 1/k >= delta(c/k)`. So Gap-UG`[c, s]` with `s < 1/k` has an empty NO set.
4. *(Coset-lift transfer is void.)* The lift `U -> L(U)` sends a unique game
   with constraints `pi_e` to the `S_k`-left-shift game `x_v = pi_e x_u` on the
   same weighted graph. It satisfies
   `val(U)/(k-1)! <= val(L(U)) <= val(U)`, where the projection is
   `sigma_v = x_v(0)`. Every guarantee it transfers is therefore
   `delta_(S_k)(c/(k-1)!) <= c/(k-1)! + 1/k!`, and this is `< 1/k` for all
   `k >= 4` and `c <= 1` (at `k = 4, c = 1` it is `5/24 < 1/4`). The loss is
   genuine. On planted instances (`pi_e` uniform subject to
   `pi_e(sigma*_u) = sigma*_v` on a `p`-fraction of edges and uniform
   otherwise, with `eps^2 d >= ln k! + 1`), `val(U) >= p - eps` while
   `val(L(U)) <= p/(k-1)! + 1/k! + eps`.
5. *(Every loss tending to infinity dies.)* Suppose a transfer certifies a
   `k`-independent guarantee `delta` of an `A`-shift algorithm on the host,
   evaluated at completeness `c/L(k)`. Then by item 2 it certifies at most
   `c/L(k)`. If `L(k) -> infinity`, this tends to `0`, so the transfer yields no
   `k`-independent guarantee for general unique games.
6. *(Salvage: dominated orbit split.)* Let `H = Mon_r(U)`, with orbits
   `O_1, ..., O_t` in the tree gauge. There is an `H`-equivariant map
   `O_i -> O_j` iff a point stabilizer of `O_i` lies in a conjugate of a point
   stabilizer of `O_j`. Call `D` *dominating* if every orbit maps equivariantly
   into some orbit of `D`, and let `tau(U)` be the least `|D|`. Then
   ```text
   max_j val(U_j)  <=  val(U)  <=  sum_(j in D) val(U_j)  <=  tau(U) max_(j in D) val(U_j).
   ```
   For cyclic `H`, the orbit of size `m` has stabilizer the unique subgroup of
   index `m`, so `tau(U)` is the number of orbit sizes that are minimal under
   divisibility. In particular `tau = 1` for cyclic `p`-group holonomy, for
   equal orbit sizes, and when some label is fixed by `H` (then `val(U) = 1`).
   Orbit sizes `{2, 3}` give `tau = 2`. So on Bafna--Minzer hosts, every unique
   game with cyclic holonomy, `val >= c` and `tau(U) <= tau_0` has a labeling of
   value `>= delta_BM(c/tau_0)`, independent of `k`, in time `n^(D(l, k, c/tau_0))`.

## What it kills (impact type 3)

**Class.** Host-preserving transfers from general (or intransitive) unique
games to group-shift games on the same Bafna--Minzer host whose certificate is
a guarantee of the target algorithm at a reduced completeness `c/L(k)`. This
covers the orbit split with the plain bound `val(U) <= t max_i val(U_i)`
(`L = k`), the coset lift `S_k / S_(k-1) -> S_k` (`L = (k-1)!`), and any
composition of them.

**Invariant.** The certified value, set against the random floor `1/k` of the
source class (item 1) and the planted ceiling `c' + (1 - c')/K` of the target
class (item 2).

**Step where every member dies.** The final certificate, that is, the
projection back to the source. The target guarantee at completeness `c/L(k)`
is at most `c/L(k) + 1/K` on planted target instances, which is at most `1/k`
once `L(k) >= k`. With a `k`-independent guarantee, it tends to `0` as soon as
`L(k) -> infinity`.

**Consequences for the graph.**

* The root `general-unique-games-easy-on-globally-hypercontractive-graphs`
  is trivially true as literally quantified. Its open content is the
  `k`-independent version, "`delta = delta(c, l, alpha)` not depending on `k`",
  matching Bafna--Minzer Theorem 1.7 ("with value independent of the alphabet
  size"). Under that reading, R1 is **not** proved by Corollary BM (item 5, with
  `L = k`). The part of R1 that item 6 does prove is `tau(U)` bounded.
* A coset lift to `S_k`-shift games cannot carry R2 to R4, whatever is proved
  for group shifts, unless it is combined with a transfer that loses only a
  bounded factor.

**Survivors.**

* Transfers whose certificate is not "target guarantee at reduced
  completeness": direct analyses of the Bafna--Minzer SoS rounding on the
  source instance.
* Bounded-loss transfers, such as the dominated orbit split with `tau` bounded.
* Bounded-degree hosts (HDX walks of fixed degree), where item 2 needs
  `d >= (ln K + 1)/eps^2` and the relevant floor is about `2/d`.

**Artifact.** `check_random_floor.py` runs in about a minute and writes
`output.txt`. It checks item 1 on 200 random instances; tabulates the least
`n` at which item 2 applies on `Grass(n, l)` for `(l, K)` from `(2, 6)` to
`(5, 8!)`; checks item 6 by brute force for cyclic holonomy with orbit sizes
`{2, 4}` (`tau = 1`, equality `val(U) = val(U_2)`) and `{2, 3}` (`tau = 2`);
and checks the two-sided lift bound of item 4 on planted `S_3` instances.
