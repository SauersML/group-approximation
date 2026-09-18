---
rg: 2
id: fpbs-mal-stage-block-sprinkling-threshold-proof
kind: route
title: Count detours in the nerve of hull translates, then apply a first-moment bound over an independent subfamily of edges
target: fpbs-mal-stage-block-sprinkling-threshold
requires: [fpbs-mal-stage-bernoulli-shift-free-for-non-dirac-base]
artifacts:
  - research/artifacts/fpbs-mal-stage-coset-nerve-2026-09-17.md
  - experiments/fpbs-mal-stage-coset-nerve-2026-09-17/coset_nerve.py
---

**Audit note (2026-09-17).** Referee lens 2 refuted the target as first
stated: it omitted `W` nonempty (step 4 divides by `|W|^2`) and `nu` not a
point mass (step 2 uses freeness). The target now carries both hypotheses.
Step 2 takes freeness of the Bernoulli action as the open prerequisite
`fpbs-mal-stage-bernoulli-shift-free-for-non-dirac-base`. Lenses 1 and 3
found the remaining steps sound, and lens 2 agreed on the mathematics.

Direct proof (artifact §§2–4). Notation is as in the target.
Words are reduced in `F = F(a, s)`. `T` is the right Cayley tree, with `F`
acting on the left.

**0. Stage pairs.** `Gamma_mal = lim(F_2 -> F_2 -> ...)` along `a -> a`,
`b -> b a b^{-2}`, and `H_{n+1}` is the image of the `(n+1)`-st copy. It is
free on `a, b_{n+1}`, and `H_n = <a, b_{n+1} a b_{n+1}^{-2}>`. So
`(H_n < H_{n+1})` is isomorphic to `(H < F)` via `s -> b_{n+1}`. The
corollary is the theorem applied to `F = H_{n+1}`, `Gamma = Gamma_mal` and
`B = B_n`.

**1. Stallings core and hull.** The core `C` of `H` has vertices `0, 1, 2` and
edges `0 -a-> 0`, `0 -s-> 1`, `1 -a-> 2`, `1 -s-> 2`. It is folded, reads
`a` and `b = s a s^{-2}` as loops at `0`, and has rank 2, so it is the core of
`H`.
- Let `T_H` be the set of words readable from `0` in `C`. This set is
  prefix-closed, so `T_H` is a subtree. It is `H`-invariant because `C` is
  folded.
- The end state of a readable word `g` is its `H`-orbit. So
  `V = V(T_H) = H ∪ H s ∪ H s a`.
- **(N1)** A vertex `p` of `T` lies in `k T_H` iff `k^{-1} p in V`, i.e. iff
  `k H in {p H, p s^{-1} H, p a^{-1} s^{-1} H}`. These three cosets are
  distinct because `1, s, sa` end at distinct states.
- **(N1')** The tree edge `(p, p x)` lies in `k T_H` iff the state of
  `k^{-1} p` has an outgoing `x`-edge in `C`. For `x = a` the states with one
  are `{0, 1}`, and for `x = s` they are also `{0, 1}`. So every tree edge
  lies in exactly two translates.
- **(N3)** For `k H ≠ H`, the map `p -> (state of p, state of k^{-1} p)` sends
  `T_H ∩ k T_H` into the off-diagonal part of `C x C`. The map is off-diagonal
  because equal states would give `k in H`.
  - The off-diagonal part consists of two trees, `{(0,1),(0,2),(1,2)}` and
    `{(1,0),(2,0),(2,1)}`, each with 3 vertices and 2 edges.
  - The map is injective on the subtree `T_H ∩ k T_H`: two vertices with the
    same image would give a nontrivial reduced closed path in a tree.
  - So `|T_H ∩ k T_H| <= 3`, and the same holds for any two distinct
    translates.

**2. Class graph.** In the free action of `F` on `Z^Gamma`, the
`E_H`-classes inside `F x` are `H gamma x`. A `Theta_B`-edge at
`gamma x in B` joins `H gamma x` and `H s gamma x`. Write `k = gamma^{-1}`.
Then the class graph is `Cos`, with vertices `kH` and edge `k` joining `kH`
and `k s^{-1} H`, and edge `k` is open iff `k^{-1} x in B`. The pair
`(x, s x)` lies in `E_H v Theta_B` iff `X = H` and `Y = s^{-1} H` are joined
by an open path.
- Edge `k` is incident to translates that both contain the tree vertex `k`,
  since `1, s in V`. So if edges `k` and `k'` share an endpoint `Z`, then
  `k, k' in Z T_H` (writing a coset for its translate).
- Distinct edges have distinct elements.

**3. Circuit lemma: `c_m <= 2^{25 m}` for `m >= 1`.** Let
`X = X_0, ..., X_m = Y` be a vertex-simple path with edges
`k_1, ..., k_m ≠ 1`. Put `p_0 = 1` and `p_i = k_i`. By step 2, `p_i` and
`p_{i+1}` lie in `X_i` (indices mod `m+1`, with `p_{m+1} = p_0`, since `1` lies
in both `X_0` and `X_m`). So the geodesic segment `sigma_i = [p_i, p_{i+1}]`
lies in `X_i` for `i = 0, ..., m`.

The segments form a closed walk in `T`, through `m+1` distinct translates. Let
`S` be the union of the segments, a finite subtree.
1. **Each edge of `S` is traversed exactly twice.** A closed walk in a tree
   crosses each edge of its trace an even, positive number of times. A
   geodesic crosses a given edge at most once. A segment crossing `f` lies in
   a translate containing `f`. Distinct segments lie in distinct translates,
   and by (N1') at most two translates contain `f`.
2. **Marks.** The leaves of `S` are turning points of the walk, so they lie
   among the `p_i`. Mark the `p_i` and the vertices of degree `>= 3`. There
   are at most `(m+1) + (m-1) = 2m` marks.
3. **Arcs.** `S` is a union of at most `2m-1` arcs whose interior vertices are
   unmarked and of degree 2. Each segment contains an arc entirely or shares
   no edge with it.
4. **Arc length.** By item 1, an arc lies in two distinct segments, hence in
   the intersection of two distinct translates. By (N3) it has at most 2
   edges. So `|E(S)| <= 4m - 2`.
5. **Walk length.** By item 1, the total length is
   `sum_i |sigma_i| = 2|E(S)| <= 8m - 4`.
6. **Encoding.** The path is determined by the words of
   `sigma_0, ..., sigma_{m-1}`. Recursively `p_{i+1} = p_i sigma_i`, and
   `X_{i+1}` is the endpoint of edge `p_{i+1}` other than `X_i`.
   - There are at most `2^{9m}` tuples of lengths with sum `<= 8m`, namely
     `binom(9m, m)`.
   - There are at most `4^ℓ` reduced words of length `ℓ`.
   - So `c_m <= 2^{9m} 4^{8m} = 2^{25m}`.

**4. First moment.** For an open path with edges `k_1, ..., k_m`, the event
that `k_i` is open lies in `sigma(x|_{k_i W})`, because
`(k^{-1} x)(w) = x(k w)`.
- Join `k_i ~ k_j` when `k_i W ∩ k_j W ≠ ∅`, i.e. when
  `k_i^{-1} k_j in W W^{-1}`. This graph has degree at most `|W|^2 - 1`.
- So it contains an independent set of size `>= m/|W|^2`, whose events are
  independent.
- Hence `P(path open) <= epsilon^{m/|W|^2} <= 2^{-27 m}`.

**5. Conclusion.** A shortest open path from `X` to `Y` is vertex-simple.
Either it is the edge `e = 1`, which is open with probability `epsilon`, or it
avoids `e`. Therefore

```text
mu{x : (x, s x) in E_H v Theta_B} <= epsilon + sum_{m>=1} 2^{25m} 2^{-27m}
                                   = epsilon + 1/3 < 1/2.
```

**Corollary.** If `E_{H_n} v Theta_n ⊇ E_{H_{n+1}}`, then
`(x, b_{n+1} x) in E_{H_n} v Theta_n` for every `x`, which is impossible when
`mu(B_n) <= 2^{-27|W_n|^2}`. With `|W_n| <= r`, each stage costs more than
`2^{-27 r^2}`, so `sum mu(B_n) = ∞`.
