# Class II two-patch rules in the unit case: peelable windows give collisions

Lane w7-two-patch-unit, 2026-09-12. Status: candidate, held OPEN until w7-vf-nonlinear re-derives it.

**Scope.** This settles nothing outright. The seed is

```text
mu'(y_1, y_a, y_b) = y_1 + y_a - y_b + [y = (0,1,0)] - [y = (1,2,2)]      over F_3,
tau(x)(g) = mu'(x(g), x(ga), x(gb)),   M = {1, a, b} distinct,   H = <a, b>.
```

- **Class II.** The rules of class II have three distinct blind pairs. They have no finite collision over free
  memory (`pair-distinct-ternary-rules-pre-injective-on-free-memory`).
- **Non-unit case.** If `ell = 1 + a - b` is not a unit, injectivity already forces a linear strict automaton
  (`two-patch-ternary-rules-reduce-to-linear-strictness`).
- **What this artifact does.** It treats the unit case. It replaces the constant background of Proposition 5
  (`distinct-symbol-patch-collision-2026-09-12.md`) with a free background, fixed window by window. The
  result is a collision whenever a finite hypergraph built from the support of the inverse can be peeled
  (Theorem 2). Section 5 records where this stops.

## 0. Seed data, rechecked by hand

- **Table.** The linear part `y_1 + y_a - y_b` is balanced, 9 preimages each.
  - At `p = (0,1,0)` its value is `1`, and the patch moves it to `2`.
  - At `q = (1,2,2)` its value is `1`, and the patch moves it to `0`.
  - So the counts of `0, 1, 2` are `10, 7, 10`. The values are `mu'(p) = 2` and `mu'(q) = 0`.
- **Blind pairs.**
  - **Address `1`, pair `{0,1}`.** `mu'(0,1,0) = mu'(1,1,0) = 2` and `mu'(0,2,2) = mu'(1,2,2) = 0`.
  - **Address `a`, pair `{1,2}`.** `mu'(0,1,0) = mu'(0,2,0) = 2` and `mu'(1,1,2) = mu'(1,2,2) = 0`.
  - **Address `b`, pair `{0,2}`.** `mu'(0,1,0) = mu'(0,1,2) = 2` and `mu'(1,2,0) = mu'(1,2,2) = 0`.
  - The three pairs are distinct.
- **Restrictions.**
  - `a -> 1`: `mu'(y,y,z) = 2y - z`. Neither patch has `y_1 = y_a`, so this restriction is balanced.
  - `b -> 1`: `mu'(y,z,y) = z + [(y,z) = (0,1)]`, unbalanced.
  - `a -> b`: `mu'(y,z,z) = y - [(y,z) = (1,2)]`, unbalanced.
- **Breaking values.** `p` and `q` differ at every address. At address `m` the symbol used by neither
  patch is `beta_m`:

  ```text
  beta_1 = 2,   beta_a = 0,   beta_b = 1.
  ```

  A window whose site at address `m` reads `beta_m` shows neither patch. Since the two patches differ
  everywhere, a window's other two sites can match at most one of them.
- **Absorbed translates.** `hM = M` with `h != 1` forces `h` in `M`. A short case check leaves only
  `a^3 = 1` and `b = a^2`, where `M = <a>` is a subgroup. Then `H = <a, b> = Z/3`, which is finite, and there
  `tau` is not injective (unbalanced). So no candidate host has an absorbed translate.

## 1. The witness and its linear part

**Conventions.** These are those of `unbalanced-design-memory-collisions-2026-09-12.md`, Section 4.
- `(L x)(g) = x(g) + x(ga) - x(gb)` is the automaton of `ell`, and composition is the product in `F_3[H]`.
- Suppose `ell w = 1` with `w = sum_(n in N) k_n n`. Only a right inverse is used, which matters because
  direct finiteness of `F_3[H]` is open for nonsofic `H`.
- `K` is the automaton of `w`, so `L K = id`.
- `d = -K delta_1`, that is `d(s) = -k_(s^-1)`, with support `S = N^-1`.

**Lemma 1 (window identities).**
- (a) `L d = -delta_1`.
- (b) Every window `h != 1` that meets `S` meets it in at least two sites. Its `d`-pattern
  `(d(h), d(ha), d(hb))` is one of `(u,-u,0)`, `(u,0,u)`, `(0,u,u)`, `(u,u,-u)`, with `u != 0`.
- (c) If `x'|_M = p` and `x = x' - d`, then `x|_M` is neither `p` nor `q`.

*Proof.*
- (a) `L K delta_1 = delta_1`.
- (b) `(L d)(h) = 0` gives `d(h) + d(ha) - d(hb) = 0`, and one nonzero entry cannot solve this. The listed
  patterns are all nonzero solutions.
- (c) `d|_M != 0` by (a) at `h = 1`, so `x|_M != p`. If `x|_M = q`, then `d|_M = p - q = (2,2,1)`, and
  `(L d)(1) = 2 + 2 - 1 = 0 != -1`. QED

**Collision criterion.** Put `x' = x + d` and `D(y) = [y|_(hM) = p] - [y|_(hM) = q]` window by window, so
`tau = L + D`.
- Suppose `x'|_M = p`, and every window `h != 1` has the same patch contribution in `x` and `x'`.
- Then `tau(x') - tau(x) = L d + (D(x') - D(x)) = -delta_1 + delta_1 = 0`, and `x != x'`.
- A window missing `S` has `x = x'` on it, so it satisfies the criterion whatever the values.
- **The constraint windows** are therefore `W = S M^-1 \ {1} = (MN)^-1 \ {1}`, a finite set.

## 2. Fixing one window at a time

**Lemma 3 (one site fixes its window).** Let `h != 1` be a window and `s = hm` a site of it outside `M`.
Fix `x` (and so `x' = x + d`) at the other two sites of `h`.
- Some value of `x(s)` makes `h` show no patch in `x` and none in `x'`.
- If `d(s) = 0`, the value `beta_m` works, and it keeps `h` patch-free whatever the other two sites hold later.

*Proof.*
- In `x`, the other two sites match at most one patch `r` in `{p, q}`, so at most one value of `x(s)`,
  namely `r_m`, is bad.
- In `x'`, likewise at most one value of `x'(s)` is bad, so at most one value of `x(s)` is bad.
- That makes at most two bad values out of three.
- If `d(s) = 0`, then `x(s) = x'(s) = beta_m` shows neither patch in either configuration, by §0. QED

**Theorem 2 (deletion criterion).** Build a hypergraph whose vertices are the sites outside `M`, with one edge
`e_h = hM \ M` for each `h` in `W`. By §0, no candidate host has an empty edge. Delete edges one at a time
by two moves:
- **(i) Private vertex.** Delete an edge that contains an unused vertex lying in no other remaining edge.
- **(ii) Free breaker.** Delete an edge that contains an unused vertex `v` with `d(v) = 0`, and mark `v` used.

Suppose every edge of `W` can be deleted. Then `tau_mu'` is not injective over `H`. The two configurations
differ exactly on the finite set `S = N^-1`, so `tau_mu'` is not even pre-injective.

*Proof.*
1. **Setup.** List the deletions `e_(h_1), ..., e_(h_k)` with their vertices `v_i`. A move-(i) vertex `v_i`
   lies in no `e_(h_j)` with `j > i`. Put `x'|_M = p` and `x|_M = p - d|_M`, and set every other site to `0` in
   `x`, with `x' = x + d`.
2. **Free breakers.** For every move-(ii) step, set `x(v_i) = beta_(m_i)`, where `v_i = h_i m_i`. Distinct steps
   use distinct vertices, and by Lemma 3 these windows stay patch-free from now on.
3. **Private vertices.** For the move-(i) steps, go through `i = k, k-1, ..., 1` and reset `x(v_i)` by Lemma 3
   for the window `h_i`.
   - A later reset changes some `v_j` with `j < i`, and `v_j` is not in `e_(h_i)`.
   - Free breakers never change again.
   - So every `h_i` ends patch-free in both configurations.
4. **Remaining windows.** Windows outside `W` miss `S`, so `x = x'` on them. Window `1` shows `p` in `x'` and
   nothing in `x` (Lemma 1(c)). The collision criterion of §1 gives `tau(x) = tau(x')`. QED

**Remarks.**
- **Where deletion can start.** A site `s` in `S \ M` lies in all three windows `s, s a^-1, s b^-1`, and all
  three are in `W`. So a move (i) can use an `S`-site only after two of its windows are gone. At the start, only
  sites outside `S` can be private or free.
- **Non-full windows.** By Lemma 1(b), a window of `W` other than the full pattern `(u,u,-u)` has exactly one
  site outside `S`: `hb`, `ha` or `h`.

**Corollary 4 (a usable sufficient condition).** Let `F` be the full windows of `W`.
- Suppose the non-full windows have a system of distinct representatives by their unique site outside `S`,
  and those sites are outside `M`.
- Suppose the hypergraph with edges `hM \ M` for `h` in `F` can be peeled by move (i) alone.
- Then `tau_mu'` is not injective.

*Proof.* Delete the non-full windows by move (ii) with the representatives, then peel `F`. QED

**Corollary 5 (what an injective host must carry).** Suppose `tau_mu'` is injective over `H` and `1 + a - b` has
a right inverse `w` with support `N`. Then `W` contains a nonempty 2-core `C`: every site of `CM \ M` lies in at
least two windows of `C`. In particular `2 |CM \ M| <= 3 |C|`.

*Proof.*
- **The core.** Peel by move (i) until it stops. What remains, `C`, is nonempty, since otherwise Theorem 2
  gives a collision. Every vertex of `C` then lies in at least two edges of `C`.
- **The bound.** Count incidences: `3 |C|` of them, and at least two for each vertex. QED

- **Reading.** A counterexample host in class II needs, near the support of the inverse of `1 + a - b`, a
  finite set of windows with no degree-one site. Its site set also grows by at most a factor `3/2`.
- **Compared with Proposition 5.** That residue was every window meeting `M ∪ N^-1` at a single address.

## 3. Calibration by hand on Z/4 and Z/5

These test the conventions of §1: the orientation of `K delta_1`, the sign of the created defect, and
Lemma 1(c). They do **not** test the deletion of Theorem 2. In a finite group `W` is almost everything and
carries a 2-core, so both collisions below were completed by hand at the core. Calibrating the deletion needs
an infinite host with a right inverse, and none was available by hand.

- **Z/4.** Take `a = 1`, `b = 2`, written additively. Then `1 + t - t^2` has inverse `w = 2 + t + t^2` in
  `F_3[t]/(t^4 - 1)`.
  - **Inverse check.** The coefficients of the product are `(2+0-1, 1+2-0, 1+1-2, 0+1-1) = (1,0,0,0)`.
  - **Correction.** `d(s) = -k_(-s)` gives `d = (1,0,2,2)` on sites `0..3`, and `L d = (2,0,0,0) = -delta_0`.
  - **Configurations.** `x' = (0,1,0,0)` and `x = x' - d = (2,1,1,1)`.
  - **Outputs.** `tau(x')` reads windows `(0,1,0), (1,0,0), (0,0,0), (0,0,1)`, giving `(2,1,0,2)`. `tau(x)`
    reads `(2,1,1), (1,1,1), (1,1,2), (1,2,1)`, giving `(2,1,0,2)`. Collision.
  - **The core.** The only vertex is site `3`, and it lies in all three windows of `W`. The value
    `x'(3) = 1` fails, since window `2` then shows `p` in `x'` and `q` in `x`. The values `0` and `2` work.
- **Z/5.** Take `a = 1`, `b = 2`. Then `w = 2 + 2t + 2t^3 + t^4`.
  - **Inverse check.** The coefficients are `(2+1-2, 2+2-1, 0+2-2, 2+0-2, 1+2-0) = (1,0,0,0,0)`.
  - **Correction.** `d = (1,2,1,0,1)` and `L d = -delta_0`. Window `4` is full, with pattern `(1,1,2)`.
  - **Configurations.** `x' = (0,1,0,u,v)` and `x = (2,2,2,u,v-1)`.
  - **Constraints.** Window `2` forbids `(u,v) = (1,0)`. Window `3` forbids `(0,1)` and `(1,0)`. Window `4`
    forbids `v = 2`. So `(u,v) = (0,0)` works.
  - **Outputs.** `tau(x') = (2,1,0,0,2)` and `tau(x) = tau(2,2,2,0,2) = (2,1,0,0,2)`. Collision.
  - **Hall fails.** The three non-full windows `1, 2, 3` share their unique site outside `S`, namely site `3`.
    So Corollary 4 does not apply.
- **Units.** In both cases `1 + a - b` is a unit because every character value `1 + chi(a) - chi(b)` is
  nonzero. On Z/5, `x^2 - x - 1` is irreducible over `F_3`, and `F_9` has no primitive fifth roots of unity.

## 4. Host constraints and the Kaplansky link

- **Amenable quotients** (from `rigid-two-patch-seed-relation-moves-2026-09-12.md`, §5). Injectivity descends
  to marked quotients, and the restrictions `b -> 1` and `a -> b` are unbalanced. So every amenable quotient
  `Q` of an injective host has `a -> 1`, and `Q = <b>`.
- **Odd order.** A right inverse maps to an inverse of `2 - b = -(1 + b)` in the commutative ring `F_3[Q]`.
  So `Q = Z/n` with `n` odd. Hence `H^ab = Z/n`, `n` odd, and `H` has no infinite amenable quotient.
- **Unique products.**
  - If `H` has unique products, a product of two elements of `F_3[H]` with at least two terms each has at least
    two terms, so `1 + a - b` has no right inverse. A host is therefore not a unique-product group, and if it is
    torsion-free, `1 + a - b` is a nontrivial unit over `F_3` in the sense of the unit conjecture.
  - A degree-one site of `C` is a product `hm`, with `h` in `C` and `m` in `M`, that has a unique
    representation. So Corollary 5 asks for a pair `(C, M)` whose unique products all lie in `M`.
- **Known nontrivial units.** Gardam (2021) and Murray (2021) found them in the Promislow group, over `F_2` and
  over `F_p` respectively. That group is amenable, so it is not a host.
- **Direct finiteness.** It is not used: only a right inverse enters §1.

## 5. Where it stops

- **Proved on paper, not yet verified.**
  - Lemmas 1 and 3.
  - Theorem 2: a deletable window hypergraph gives a finite collision.
  - Corollaries 4 and 5: an injective class-II seed host carries a 2-core in `W = (MN)^-1 \ {1}`, one that
    violates unique products away from `M`.
  - The hand calibrations on Z/4 and Z/5.
- **Not proved.** Class II is not settled. A right inverse whose window set has a 2-core with no deletion
  sequence is not excluded. Such cores exist in every finite quotient, but finite quotients are not hosts.
- **Local lemma fails.** A random assignment with full windows gives failure probability up to `4/27` per
  window with dependency degree `6`. That is above the bound `5^5/6^6`.
- **Freedoms not used.**
  - The `q`-witness: `x'|_M = q`, `L d = +delta_1`. It has the same `W` but different bad values.
  - Several created defects `e = sum_g t_g delta_g`, which change `S = supp(K e)`.
  - Sites outside `S` with `d = 0` that break no window of `W`, used to reroute breakers.
- **Other rules of class II.** The argument used only three facts: distinct pairs, the breaking values `beta_m`,
  and the fact that `p` and `q` differ at every address. Extending it to the other 29 rules needs the census
  data for each rule, and that was not attempted here.
- **Next lead.** Decide whether a right inverse of `1 + a - b` can have `W` with a 2-core that resists deletion.
  Lemma 1(b) fixes the `d`-pattern on each window of a core. Combining that with "every site has two windows"
  is the first thing to try.
