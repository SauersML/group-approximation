# The stage coset graph of Gamma_mal is a nerve of hull translates, and sparse block sprinkling cannot repair a stage

Worker b-p-fp2, swarm-0917, September 17, 2026. Family: probability-random.
Target hole: `fpbs-locally-free-free-actions-have-finite-cost`, first test
"does every free action of `Gamma_mal` have finite cost".

Script: `experiments/fpbs-mal-stage-coset-nerve-2026-09-17/coset_nerve.py`.
Run it as `python3 coset_nerve.py 8:6 10:6 10:7` (arguments are
`radius:maxlength`).

## 1. The mechanism being tested

`Gamma_mal = union H_n`, where `H_{n+1} = <a, b_{n+1}>` is free on `a, b_{n+1}`
and `b_n = b_{n+1} a b_{n+1}^{-2}`. Every stage pair `H_n < H_{n+1}` is
isomorphic to

```text
H = <a, s a s^{-2}>  <  F = F(a, s),      s = b_{n+1}.
```

The most direct attempt to show that the Bernoulli action of `Gamma_mal` has
finite cost is **stagewise telescoping**:
- take a cost-2 graphing `Phi` of `E_{H_1}`;
- at stage `n`, add the `b_{n+1}`-edges `Theta_n = {(x, b_{n+1} x) : x in B_n}`
  on a set `B_n`, chosen so that `E_{H_n} v Theta_n = E_{H_{n+1}}`;
- ask for `sum_n mu(B_n) < infinity`.

The resulting graphing `Phi ∪ ⋃ Theta_n` generates the orbit relation and has cost
`2 + sum mu(B_n)`. By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
the cost would then be exactly 2.

The finite-contact obstruction (`fpbs-malnormal-subgroup-relations-finite-contacts`,
artifact `research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md`)
rules out repairing a stage through *infinitely many* contacts between two
`E_{H_n}`-classes. The mechanism here is different: each pair of adjacent
classes has exactly one potential `Theta`-edge, and connectivity comes from
long detours through other classes. Section 4 shows that sparse random
sprinkling with bounded-range dependence cannot provide those detours.

## 2. The class graph

Fix a free p.m.p. action of `F` and `B ⊆ X`. Put
`Theta_B = {(y, s y) : y in B}`. The `E_H`-classes inside `F x` are the sets
`H gamma x`. Using `H gamma <-> gamma^{-1} H`, the class graph of
`E_H v Theta_B` at `x` is the graph `Cos` described below, with edge `k` open
iff `k^{-1} x in B`:

```text
vertices   left cosets kH           (k in F)
edges      one edge per k in F, joining  kH  and  k s^{-1} H.
```

The pair `(x, s x)` lies in `E_H v Theta_B` iff the vertices `X = H` and
`Y = s^{-1} H` are joined by an open path. The direct edge between them is
`e = 1`, which is open iff `x in B`.

## 3. Structure: `Cos` is the intersection graph of translates of the hull

`T` is the right Cayley tree of `F` on `{a, s}`, with `F` acting on the left.
The Stallings core of `H` has vertices `v0, v1, v2` and edges
`v0 -a-> v0`, `v0 -s-> v1`, `v1 -a-> v2`, `v1 -s-> v2`.
`T_H` is the set of reduced words readable from `v0` in the core. It is an
`H`-invariant subtree with vertex set `V = H ∪ H s ∪ H s a`.

- **(N1) Multiplicity 3.** Each vertex `p` of `T` lies in exactly three
  translates: `p T_H`, `p s^{-1} T_H` and `p a^{-1} s^{-1} T_H`. These are the
  cosets `p c^{-1} H` for `c in {1, s, sa}`, and they are distinct because the
  three words end at different core states.
- **(N1') Each tree edge lies in exactly two translates.** A tree edge labelled
  `x` lies in `k T_H` iff its initial vertex corresponds to a core state with
  an outgoing `x`-edge. For both `x = a` and `x = s`, exactly two core states
  have one (script output: `2 2`).
- **(N2) Adjacency is intersection.** `V V^{-1} = H ∪ H s H ∪ H s^{-1} H`
  (using `s a s^{-1} = b s`). So `kT_H` and `k'T_H` meet iff
  `k^{-1} k' in H s^{±1} H`, i.e. iff they are adjacent in `Cos`.
  - Edge `k` joins two translates that both contain the tree vertex `k`,
    since `1, s in V`.
  - By malnormality there are at most two edges between two vertices, one
    from each double coset.
  - The script finds no edge-element conflicts on balls of radius up to 10.
- **(N3) Bounded intersections.** The off-diagonal part of the pullback
  `core x core` has two components, `{(0,1),(0,2),(1,2)}` and
  `{(1,0),(2,0),(2,1)}`. Each is a tree with 3 vertices (script output).
  - Trees certify malnormality.
  - The map `p -> (state of p, state of k^{-1} p)` is injective on
    `T_H ∩ k T_H` for `kH ≠ H`.
  - So two distinct translates share at most 3 vertices. The script sees
    maximum 3, with `T_H ∩ s^{-1} T_H = {1, a, s}`.

So the nerve of the cover of `T` by translates of `T_H` is contractible: all
intersections are subtrees. Its 1-skeleton is `Cos`, with triangles at the
tree vertices.

## 4. Theorem (block sprinkling below threshold does not repair the stage)

Let `Gamma ⊇ F` be countable, with the Bernoulli shift
`(gamma x)(delta) = x(gamma^{-1} delta)` on `(Z^Gamma, nu^Gamma)`. Let
`W ⊆ Gamma` be finite, and let `B` be measurable with respect to `x|_W`, with
`mu(B) = epsilon`. If

```text
epsilon <= 2^{-27 |W|^2},
```

then `mu{x : (x, s x) in E_H v Theta_B} <= epsilon + 1/3 < 1/2`. In
particular `E_H v Theta_B ≠ E_F`.

The proof is in route `fpbs-mal-stage-block-sprinkling-threshold-proof`. Its
only nontrivial step is the circuit lemma:

> **Circuit lemma.** For `m >= 1`, the number `c_m` of vertex-simple edge
> paths `X = X_0, X_1, ..., X_m = Y` in `Cos` that do not use `e` satisfies
> `c_m <= 2^{25 m}`.

Proof sketch. Encode the path by its edge elements `p_i = k_i`, with `p_0 = 1`.
Consecutive edge elements lie in a common translate. The segments
`[p_i, p_{i+1}] ⊂ X_i` form a closed walk in `T` through `m+1` distinct
translates. Their union is a finite subtree `S`.
- Every edge of `S` is traversed an even number of times. Each traversal is by
  a segment in a translate containing that edge, and at most two translates
  contain it (N1'). So every edge is traversed exactly twice.
- Mark the `p_i` and the branch points. There are at most `2m` marks.
- An unmarked arc is covered by two segments in distinct translates, so by
  (N3) it has at most 2 edges.
- So `|E(S)| <= 4m - 2`, and the total walk length is at most `8m - 4`.
- A path is determined by the reduced words of its first `m` segments. Hence
  `c_m <= 4^{8m} 2^{9m}`.

## 5. Computation of `c_m`

The counts are of vertex paths in the simple nerve graph of translates meeting
the ball of radius `R` in `T`, with the pair `{X, Y}` removed. There are at
most two edges per pair, so the edge-path count is at most `2^m` times larger.
The counts are lower bounds for the true vertex-path counts. They are exact once
`R >= 4m - 2`, because by the lemma every edge element of a qualifying path
lies in `S`, within distance `4m - 2` of `1`.

| m | c_m (R=8) | c_m (R=10) |
|---|-----------|------------|
| 2 | 3 | 3 |
| 3 | 12 | 12 |
| 4 | 60 | 60 |
| 5 | 336 | 336 |
| 6 | 2014 | 2016 |
| 7 | — | ≥ 12670 |

The three length-2 detours are the triangles at the tree vertices `1`, `a`
and `s` of `T_H ∩ s^{-1} T_H`. The successive ratios are 4, 5, 5.6, 6.0 and
6.3.

This suggests a true growth rate of about 7. For iid sprinkles
(`|W| = 1`), that would put the first-moment threshold near `epsilon ≈ 0.1`,
far above the proved `2^{-27}`. The proved constant is not optimized. Only
its existence matters for the corollary.

## 6. What this kills and what survives

**Corollary (stagewise telescoping for Bernoulli `Gamma_mal`).** Suppose
`Theta_n` consists of `b_{n+1}`-edges on sets `B_n` measurable with respect to
windows `W_n`, and `E_{H_n} v Theta_n ⊇ E_{H_{n+1}}` for each `n`. Then
`mu(B_n) > 2^{-27|W_n|^2}` for every `n`.
- **iid sprinkles** (`|W_n| = 1`): every stage costs more than `2^{-27}`, so
  the telescoped graphing has infinite cost. The Borel–Cantelli programme dies
  at the first-moment step: below the threshold, the expected number of open
  detours is at most `1/3`.
- **Bounded range** (`|W_n| <= r`): same conclusion.
- **Summable cost:** needs `|W_n| >= sqrt(log_2(1/mu(B_n)) / 27) -> infinity`.
  Repair sets must use correlations over windows growing at least like the
  square root of the logarithm of the inverse density.

The named invariant is the pair (multiplicity of tree edges in hull
translates = 2, maximal pairwise intersection = 3 vertices). It forces
exponential growth of detours, `c_m <= 2^{25 m}`, in the stage coset graph.

**Not killed.**
1. Repair sets that are factors of iid with windows growing faster than
   `sqrt(log(1/epsilon))`, or measurable sets in non-Bernoulli free actions.
   The first-moment bound does not see correlations. No positive lower bound
   on `relC(E_{H_{n+1}} : E_{H_n})` is known: the relative `L²` bound is 0.
2. **Non-stagewise unions.** Later `b_m`-edges (`m > n+1`) can reconnect
   `E_{H_{n+1}}`-classes through `H_m`-cosets. The theorem only says that no
   single stage is repaired by its own sparse sprinkle.
3. Multi-label sprinkles `Theta` with edges `x -> gamma x` for `gamma` in a
   finite set `L ⊆ F \ H`. The same argument applies with constants depending
   on `L`, but the lengths of the translates between adjacent classes grow
   with `L`. This was not written out.

**Contrast with the tree case.** For `<a> < <a> * <s>`, the coset graph is a
tree, every edge is a cut, and no invariant repair of relative cost below 1
exists. For the `Gamma_mal` stage pair, `Cos` has triangles at every tree
vertex and exponentially many detours per edge. Cuts are not finite. What
fails is only the *independent* use of the detours.
