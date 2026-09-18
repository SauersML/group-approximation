# Fold bootstrap for the Gamma_mal stage pair, and an explicit cost-2 action of Gamma_mal

Agent swarm-0917-w7-w7-fp-follow, 2026-09-17/18. Scripts are in
`experiments/fpbs-fold-bootstrap-2026-09-17/`.

## 0. Summary

Pair: `L = F(a, b)`, `K = <a, k>` with `k = b a b^{-2}`. Every stage pair
`H_n ≤ H_{n+1}` of `Gamma_mal = <a, b_1, b_2, ... | b_n = b_{n+1} a b_{n+1}^{-2}>`
has this form with `b = b_{n+1}`.

For a free p.m.p. action of `L` and a measurable `A`, put
`R' = R_K ∨ b|_A` and `D = { w : w R' b w }`.

1. **Fold theorem (§1).** `D = cl(A)`, the closure of `A` under the 2-of-3
   rule on the triples `T_w = { w, a w, b w }`. So
   `R_K ∨ b|_A = R_L` iff `cl(A)` is conull, and
   `relC(R_L; R_K) ≤ σ_b := inf { μ(A) : cl(A) conull }`.
2. **Abelian odometer (§2).** If the action has the factor
   `z ↦ z + χ(g)` on `Ẑ` for a character with `χ(a) = 1` (any `χ(b) = t`),
   then `σ_b = 0`. For `Gamma_mal` the character
   `χ(a) = 1, χ(b_odd) = −1, χ(b_even) = 2` exists. So `β × Ẑ_χ` has cost `2`
   for every free action `β` of `Gamma_mal`. In particular `C(Gamma_mal) = 2`.
3. **Exact iid single-site threshold (§3).** For iid seeds of density `p`,
   `cl(A)` is conull iff `p > 5/32`. At `p = 5/32` the closure has density
   `11/27`. Hence for the Bernoulli shift of `Gamma_mal`,
   `relC(E_{H_2}; E_{H_1}) ≤ 5/32`, and single-site sprinkling repairs a stage
   iff its density exceeds `5/32`. This compares with the proven
   `2^{-27}` for `|W| = 1` in `fpbs-mal-stage-block-sprinkling-threshold`.
4. **Nonabelian finite factors (§4).** These are strictly worse than abelian
   ones. The best certificate is `848/8192` on the Zassenhaus quotient
   `(p, c) = (2, 4)`. Deeper pairs scale about linearly (§5).
5. **Open (§6).** The Bernoulli shift has no finite or compact factor, so §2
   says nothing about it. No lower bound on `σ_b` is known.

## 1. The fold theorem

**Lemma 1.1 (easy half).** `A ⊆ D`, and `D` satisfies the 2-of-3 rule on
every triple `T_w`. Hence `cl(A) ⊆ D`.

*Proof.* Two facts hold for all `w`:
- `w ~ a w`, because `a ∈ K`;
- `b^2 w ~ b a w`, because `k (b^2 w) = b a w` and `k ∈ K`.

Membership in `D` reads: `w ∈ D` iff `w ~ bw`; `aw ∈ D` iff `aw ~ baw`;
`bw ∈ D` iff `bw ~ b^2 w`. Now use the two facts:
- `w, bw ∈ D`: `aw ~ w ~ bw ~ b^2 w ~ baw`.
- `w, aw ∈ D`: `bw ~ w ~ aw ~ baw ~ b^2 w`.
- `aw, bw ∈ D`: `w ~ aw ~ baw ~ b^2 w ~ bw`. ∎

If `D` is conull then `b ∈ [[R']]`, and with `a, k` this gives `R' = R_L`.
So `relC(R_L; R_K) ≤ μ(A)` whenever `cl(A)` is conull.

**Theorem 1.2 (exactness).** For a free action, `D = cl(A)`.

*Proof.* Work in one orbit, identified with `L` by `g ↦ g x_0`. Write
`z = g^{-1}`. Then the `R_K`-class of `g x_0` becomes the left coset `zK`.
The generator `s ∈ {a, b}` moves `z` to `z s^{-1}`. Let `T'` be the right
Cayley tree (edges `z — z s`), on which left multiplication acts by
automorphisms. The triple `T_w` becomes `{ z, z a^{-1}, z b^{-1} }`.

*Hull types.* The Stallings core `Γ_K` has vertices `0, v_1, v_2` and edges:
- an `a`-loop at `0`;
- `b : 0 → v_1`;
- `a : v_1 → v_2` and `b : v_1 → v_2`.

It reads `k = b a b^{-1} b^{-1}` as `0 → v_1 → v_2 ← v_1 ← 0`. The hull of
`zK` in `T'` is `z · hull(K)`, which is the universal cover of `Γ_K`. A vertex
`y` of `T'` lies in the hull of at most three cosets, with types:
- type 0: in the hull of `c_0(y) = yK`;
- type 1: in the hull of `c_1(y) = y b^{-1} K`;
- type 2: in the hull of `c_2(y) = y b^{-2} K = y a^{-1} b^{-1} K`.

The two expressions for `c_2` agree because `b a b^{-2} ∈ K`.

*Abstract model.* Let `W_0` be the disjoint union of abstract copies of all
hulls `hull(zK)`, together with one extra `b`-edge for each seed. The seed
`g x_0 ∈ A` gives the extra edge `x → x b`, with `x = z b^{-1}`, from the
type-0 copy at `x` to the type-0 copy at `x b`. Each copy is connected and
contains its coset. So the components of `W_0` are exactly the `R'`-classes,
viewed as sets of cosets. There is a label-preserving map `W_0 → T'`.

*Folding rules.* Identifying two copies at a vertex `y` forces the
identifications below. For each identified pair, compare the edges with the
same label and direction at `y`:
- `(0,1)` at `y` forces `(0,2)` at `y a` (out-`a`) and `(1,2)` at `y b`
  (out-`b`);
- `(0,2)` at `y` forces `(0,1)` at `y a^{-1}` (in-`a`);
- `(1,2)` at `y` forces `(0,1)` at `y b^{-1}` (in-`b`).

Put `d(y) := [ c_0(y) and c_1(y) are identified ]`. Then:
- `(0,2)` at `y` holds iff `d(y a^{-1})` holds;
- `(1,2)` at `y` holds iff `d(y b^{-1})` holds.

Transitivity at `y` is therefore exactly the 2-of-3 rule on
`{ y, y a^{-1}, y b^{-1} }`. A seed edge at `x` coincides with the hull edge
`x → x b` once `d(x b)` holds, and `x b = z`. So the seeds are `d(z)` for the
points `z = g^{-1}` with `g x_0 ∈ A`, which is the set `A` in the original
coordinates. Likewise `d(z)` for `z = g^{-1}` says that `g x_0` and
`b g x_0` have `R'`-related cosets, i.e. `g x_0 ∈ D`.

*Closing.* Let `S` be the 2-of-3 closure of the seeds, and identify copies at
each `y` by the partition generated by the pairs that `S` prescribes. This
identification is closed under all the folding rules, and it is consistent
because `S` is 2-of-3 closed. So the quotient `W` is a folded graph mapping to
`T'`, i.e. an immersion. A connected graph immersing into a tree embeds: a
nontrivial reduced path maps to a reduced path, which has distinct endpoints.

Components of `W` are components of `W_0`, i.e. `R'`-classes. So if two
cosets at `y` lie in one class, their copies at `y` are identified in `W`. In
particular `w ∈ D` (cosets `c_0(y)`, `c_1(y)` in one class) implies
`d(y)`, i.e. `w ∈ S = cl(A)`. ∎

**Numerical check.** `certify.py` (`exactness_tests`) computes `D` by
union-find on `R'`, truncated to the radius-9 ball of the Cayley tree of
`F_2`. It uses 30 random seed sets inside the radius-2 ball and finds
`D = cl(A)` every time (`certify_out.txt`).

**Warning.** Finite quotients are not valid tests of exactness. There `L`
does not act freely and `K` may surject. The first attempt failed on
`PSL2(5)` with `|D| = 60` and `|cl(A)| = 1`.

**Finite factor bound.** If the action factors onto `L ↷ Q` (a finite
transitive action) and `S ⊆ Q` has `cl(S) = Q` for the triples
`{q, a q, b q}`, then `cl(π^{-1} S) ⊇ π^{-1} cl(S)`. Hence
`relC(R_L; R_K) ≤ r(Q) / |Q|`, where `r(Q)` is the minimal seed count.

**Double cosets.** Pieces of a graphing with labels in `K b^{±1} K` are
`R_K`-equivalent to `b|_{A'}` with `μ(A') ≤` their mass. So
`relC_{K b^{±1} K}(R_L; R_K) = σ_b`: the fold closure is the complete answer
for graphings that use one double coset.

## 2. The abelian odometer

**Lemma 2.1.** Let `χ : L → Z` have `χ(a) = 1` and `χ(b) = t ∈ Z`. Suppose a
free action `L ↷ X` has the factor `π : X → Ẑ` onto `z ↦ z + χ(g)`. Put
`m = max(|t|, 1)` and `A_N = { x : π(x) mod N ∈ {0, ..., m} }`. Then for
every `N > m`:
- `cl(A_N) = X`;
- `μ(A_N) = (m+1)/N`.

Hence `relC(R_L; R_K) = 0`.

*Proof.* The triple `T_w` has `Z/N`-coordinates `{q, q+1, q+t}`, where `q`
is the coordinate of `w`. Let `S_j` be the set of points with coordinate in
`{0, ..., j}` (mod `N`). We show `S_j ⊆ cl(A_N)` implies
`S_{j+1} ⊆ cl(A_N)` for `j ≥ m`. Let `u` have coordinate `j+1`.
- `t ≥ 2`: `u = b w` with `w = b^{-1} u` of coordinate `j+1−t`, and `a w` of
  coordinate `j+2−t`. Both lie in `[0, j]`. So `w, aw ∈ cl` and `u = bw ∈ cl`.
- `t ≤ 0`: `u = a w` with `w = a^{-1} u` of coordinate `j`, and `b w` of
  coordinate `j+t`, which lies in `[0, j]` because `|t| ≤ m ≤ j`. So
  `w, bw ∈ cl` and `u = aw ∈ cl`.
- `t = 1`: go downwards instead. Let `u` have coordinate `N−1`, i.e. `−1`.
  Then `a u` and `b u` both have coordinate `0`, so they lie in `cl`, and
  `u ∈ cl`. Repeating gives every coordinate. (Here one seed class `{0}`
  suffices.)

Induction up to `j = N−1` gives `cl(A_N) = X`. Now Lemma 1.1 applies. ∎

In the `t = 1` case the three points `w, aw, bw` are distinct although two of
them share a coordinate. That is why the finite check in
`odometer_threshold.py` counts triple members with multiplicity; the
`Bootstrap` class does so too.

**Theorem 2.2.** Define `χ : Gamma_mal → Z` by `χ(a) = 1`,
`χ(b_n) = −1` for odd `n` and `χ(b_n) = 2` for even `n`. For every free p.m.p.
action `β` of `Gamma_mal` on `(X, μ)`, the product action
`g(x, z) = (g x, z + χ(g))` on `X × Ẑ` is free and p.m.p., and

```text
C(β × Ẑ_χ) = 2,    relC(E_{H_{n+1}}; E_{H_n}) = 0  for every n.
```

In particular `C(Gamma_mal) = inf_free C = 2 < ∞`.

*Proof.*
1. **χ is a homomorphism.** `Gamma_mal` is the directed union of the free
   groups `H_n = F(a, b_n)`, with the inclusion `b_n = b_{n+1} a b_{n+1}^{-2}`.
   A character is a compatible family of characters of the `H_n`, and
   compatibility is `χ(b_n) = χ(a) − χ(b_{n+1}) = 1 − χ(b_{n+1})`. This holds
   for both parities: `−1 = 1 − 2` and `2 = 1 − (−1)`.
2. **Freeness and measure.** The product is free because `β` is. It preserves
   `μ × Haar`.
3. **One stage.** For the stage `K = H_n ≤ L = H_{n+1}`, with `b = b_{n+1}`,
   the pair is the pair of §1 and `t = χ(b_{n+1}) ∈ {−1, 2}`. So `m ∈ {1, 2}`,
   and Lemma 2.1 gives sets `B_n = A_{N_n}` (in the `Ẑ` coordinate) with
   `E_{H_n} ∨ b_{n+1}|_{B_n} = E_{H_{n+1}}` and `μ(B_n) ≤ 3/N_n`.
4. **Telescoping.** Choose `N_n` with `Σ 3/N_n < ε`. The graphing consisting
   of `a`, `b_1` and the pieces `b_{n+1}|_{B_n}` generates `E_{H_1}`, then each
   `E_{H_{n+1}}` by induction, hence `∪_n E_{H_n} = E`. Its cost is below
   `2 + ε`.
5. **Lower bound.** By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`
   with `c*(Gamma_mal) = 2`, the finite cost is exactly `2`. Alternatively,
   Gaboriau's bound `C ≥ 1 + β_1^(2)` applies with `β_1^(2)(Gamma_mal) = 1`
   (`locally-free-groups-first-l2-betti-equals-c-star-minus-one`). ∎

**Consequences for the graph.**
- **Finite cost of Γ_mal.** The conditional "if some free action has finite
  cost" in `fpbs-locally-free-free-action-costs-are-c-star-or-infinite` is
  now unconditional for `Gamma_mal`. Every free action of `Gamma_mal` has
  pseudocost exactly `2`, and `Gamma_mal` has fixed price iff every free
  action has finite cost.
- **Stakes of the Bernoulli floor.** `fpbs-mal-bernoulli-single-stage-floor`
  now implies that `Gamma_mal` is a counterexample to fixed price: Bernoulli
  would have cost `∞` and `Bernoulli × Ẑ_χ` cost `2`. It also refutes
  `fpbs-relative-fixed-price-free-pairs`.
- **The free-pair claim.** `fpbs-relative-fixed-price-free-pairs` holds, with
  `relC = 0`, for every free `F_2`-action with a `χ`-odometer factor
  (`χ(a) = 1`, any `χ(b)`). This covers the Bernoulli shift times `Ẑ_χ`.
- **Not circular.** This is no descent step of the kind killed by
  `fpbs-extension-routes-to-finite-cost-are-circular`. It certifies that
  `C(Gamma_mal) < ∞`, which that node takes as a hypothesis. By its item 1,
  every free action `b` of `Gamma_mal` has a free extension of cost `2`,
  e.g. `b × Ẑ_χ`.
- **Why abelian quotients.** The factor cost `r(Q)/|Q|` is at most
  `(m+1)/N` on `Q = Z/N` through `χ`, which tends to 0. Every nonabelian
  quotient tried in §4 stays near `0.1`. With `χ(a) = 1`, the characters of
  `Gamma_mal` are `χ(b_n) = u, 1−u, u, 1−u, ...` for `u ∈ Z`. Lemma 2.1 applies
  to every one of them. Theorem 2.2 uses `u = −1`.

**Literature.** A web search (2026-09-18) found no statement that `Gamma_mal`
has finite infimal cost. The graph treated it as unknown: see the
"First test" in `fpbs-locally-free-free-actions-have-finite-cost` and the
conditional remark in
`research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md`.
The argument is elementary, so it may be folklore. It is recorded here as
new relative to the graph.

## 3. Exact threshold for iid single-site seeds

**The triple hypergraph is a hypertree.** Take the triples
`{ w, a w, b w }` on the vertex set `F_2`. The moves inside a triple are
`a`, `b` and `c = b a^{-1}`. These triples are the 2-cells of the universal
cover of the presentation complex `<a, b, c | c = b a^{-1}>` of `F_2`.
- That complex is aspherical, since it is a one-relator presentation with a
  relator that is not a proper power. So its universal cover is contractible.
- Each generator occurs once in the relator, so each edge lies in exactly one
  triangle.
- Replacing every triangle by a tripod (a cone point joined to its three
  vertices) is a homotopy equivalence rel vertices.

So the vertex–triple incidence graph is contractible, i.e. a tree. Every
vertex lies in 3 triples and every triple has 3 vertices.

**Recursion.** On a hypertree, `z ∈ cl(A)` iff `z ∈ A` or some triple
`T ∋ z` has both other vertices in the closure of their own branches.
- Branches of the hypertree minus `T` are joined only through `T`, and `T`
  cannot fire before `z` is added.
- For iid seeds of density `p` (with `q = 1 − p`), let `y` be the probability
  that a branch root lies in the closure of its branch.
- A branch root has 2 child triples with 2 child roots each, so
  `y = f(y) := p + q (1 − (1 − y^2)^2)`.
- `y` is the least fixed point of `f` in `[0, 1]`, as the increasing limit of
  depth truncations, because derivations are finite.

**Threshold.** Write `f(y) − y = (1 − y)(1 − q h(y))` with
`h(y) = (1 − y)(1 + y)^2`. On `[0, 1]`, `h` has maximum `32/27` at `y = 1/3`.
- So `f(y) > y` on `[0, 1)` iff `q < 27/32`, i.e. `p > 5/32`. Then `y = 1`,
  and `P(z ∈ cl) = 1`.
- For `p ≤ 5/32` there is a fixed point `y* < 1` (`y* = 1/3` at
  `p = 5/32`). Then
  `P(z ∈ cl) = p + q (1 − (1 − y*^2)^3) < 1`, which equals `11/27` at
  `p = 5/32`.

**Consequences.** Let `β` be the Bernoulli shift of `Gamma_mal`, with a
non-atomic base, and `B = { x : x(e) ∈ U }` with `ν(U) = p`. The points
`g x`, for `g` in a stage, carry iid labels `x(g^{-1})`. By Theorem 1.2:
- `E_{H_1} ∨ b_2|_B = E_{H_2}` iff `p > 5/32`;
- hence `relC(E_{H_2}; E_{H_1}) ≤ 5/32` for the Bernoulli shift.

The same holds for the Bernoulli shift of `F_2` and the pair
`K ≤ F_2`. For single-site sprinkles (`|W| = 1`), this replaces the proven
first-moment bound `2^{-27}` of `fpbs-mal-stage-block-sprinkling-threshold`
by the exact threshold `5/32`.

It does **not** give finite Bernoulli cost. The per-stage value is constant
in `n`, so the telescoped graphing costs `2 + Σ 5/32 = ∞`, consistent with
that node's corollary.

Check: `odometer_threshold.py` (`odometer_threshold_out.txt`).
- It verifies `f(5/32, 1/3) = 1/3`, tangency and the density `11/27` in
  exact rationals.
- Iterating from `y = 0` gives `y = 0.2662` at `p = 0.15`, `0.3333` at
  `5/32`, and `1.0` at `p = 0.1575`.
- Monte Carlo on the radius-7 ball is included only as a sanity check. The
  finite radius strongly suppresses the closure.

## 4. Nonabelian finite factors

The Zassenhaus/Magnus quotient `Q = <1+X, 1+Y>` of `F_p<X,Y>/(deg > c)` is
compatible with the shift. The Magnus kernel is invariant under the stage
endomorphism, and the endomorphism is onto every finite `p`-quotient by the
Burnside basis theorem (determinant `−1` on `H_1`).

Certificate (`certify.py 2 4 6 seeds_zass_p2_c4.json`, `certify_out.txt`):
- `p = 2`, `c = 4`, `|Q| = 8192`, with 848 seeds;
- closure full, verified independently by union-find (1 class);
- ratio `0.1035`;
- seeds saved as Magnus coefficient vectors in `seeds_zass_p2_c4.json`.

The greedy ratio stays near `0.11–0.13` for `PSL2(q)` and other Zassenhaus
quotients. So nonabelian quotients do far worse than the cyclic quotients of
§2, where `r(Z/N) ≤ 3` for `|t| ≤ 2`.

## 5. Deep pairs

`deep_pairs.py 4 2` (rng seed 4242, `deep_pairs_out.txt`) treats the pair
`H_1 ≤ H_{1+m}`, with the generator of `H_1` written in `H_{1+m}`. The table
gives the best seed ratio on each quotient.

| Q | n | m=1 | m=2 | m=3 | m=4 |
|---|---|---|---|---|---|
| Zass(2,3) | 128 | 0.1875 | 0.367 | 0.570 | 0.742 |
| Zass(3,3) | 2187 | 0.122 | 0.230 | 0.329 | 0.440 |
| Zass(2,4) | 8192 | 0.119 | 0.229 | 0.331 | 0.462 |
| Zass(5,3) | 3125 | 0.122 | 0.250 | 0.390 | 0.542 |
| PSL2(13) | 1092 | 0.127 | 0.258 | 0.385 | 0.505 |
| PSL2(19) | 3420 | 0.109 | 0.278 | 0.405 | 0.526 |

The growth is roughly additive in `m`. These are heuristic upper bounds (with
greedy seeding) and give no evidence that deep pairs beat single stages.

## 6. What remains open

- **Bernoulli.** The Bernoulli shift of `Gamma_mal` is weakly mixing, so it
  has no nontrivial compact factor and §2 does not apply. The best
  single-double-coset bound is `σ_b ≤ 5/32`, from §3. Whether `σ_b = 0` for
  Bernoulli is open, and so is whether multi-double-coset graphings do better.
- **No lower bound.** The BLPS-type mass-transport argument that bounds
  2-neighbour bootstrap on `T_3` from below (density `≥ 1/4`) fails here. It
  would need cores with branching, and core-free complements of the 2-of-3
  closure can be many-ended. No positive lower bound on `σ_b` is known for any
  free action.
- **Fixed price of Gamma_mal.** By §2 it is equivalent to: every free action
  of `Gamma_mal` has finite cost.
