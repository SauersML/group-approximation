# Linear perimeter for coset cycles over a malnormal free stage

Supporting proof for `fpbs-malnormal-coset-cycles-linear-perimeter`. This
resolves the "precise open step" of
`research/artifacts/fpbs-malnormal-coset-cycles-2026-09-17.md` §4. That note
observes that in a tree many long sides can pass through a short star region,
so the line argument does not transfer directly. The argument below does not
bound how many sides pass through a region. It bounds two other quantities:
the number of arcs of the union tree, and the number of sides through a
single edge.

## 0. Setup and imports

The setup follows `fpbs-malnormal-coset-cycles-bounded-syllables-proof`:
- `F` acts on the left on `T = Cay(F, S)`, and `r = |S|`;
- the hull of `gH` is `gY`;
- a simple coset cycle with `k` `t`-edges has distinct vertex cosets
  `g_0 H, ..., g_{k-1} H`, with sides as follows:
  - coset sides `σ_i = [p_i, q_i]`, where `q_i = p_i h_i`, so `σ_i ⊂ g_i Y`;
  - `t`-sides `τ_i = [q_i, p_{i+1}]`, where `p_{i+1} = q_i t^{ε_i}` and
    `p_k = p_0`.

All sides are geodesics. `|σ_i| = |h_i|_S` and `|τ_i| = τ := |t|_S`. The
perimeter is `P = sum_i |h_i|_S + k τ`.

**Import (I1)**, Item 1 of `fpbs-malnormal-coset-cycles-bounded-syllables`,
verbatim: "For distinct cosets `gH != g'H`, the convex hulls of `gH` and `g'H`
in `T` meet in a subtree of diameter less than `D`."

**Parity fact.** A closed edge path in a tree crosses every edge an even
number of times. A geodesic crosses each edge at most once.

## 1. The union tree has at most 4k-3 short arcs

Let `Σ` be the union of the `2k` sides. It is a finite subtree of `T`, and it
is connected because the polygon is closed. Call the polygon vertices
`p_i, q_i` *marked*. There are at most `2k` of them.

**Leaves are marked.** An unmarked vertex `v` of `Σ` lies in the interior of
every side through it. Such a side uses two edges at `v`, so `deg_Σ(v) >= 2`.

**Suppression.** Let `V'` be the set of marked vertices together with the
vertices of degree at least 3. The leaves number `L <= 2k`, and
`#{deg >= 3} <= L - 2`. So `#V' <= 4k - 2`. Cutting `Σ` at `V'` gives
`#V' - 1 <= 4k - 3` *arcs*: maximal segments whose interior vertices are
unmarked and of degree 2. (If `Σ` is a single vertex, `P = 0`.)

**Sides are unions of arcs.** Suppose a side contains an edge of an arc. At
each interior vertex of the arc the side cannot end, since the vertex is
unmarked. It also cannot turn, since the vertex has degree 2. So the side
contains the whole arc.

**Arc length.** Take an arc `α`. By the parity fact, the closed polygon path
crosses an edge of `α` an even number of times. The edge lies in some side,
and each side crosses it at most once. So at least two distinct sides contain
`α`.
- **Two of them are coset sides `σ_i, σ_j`.** Then `i != j`, so
  `g_i H != g_j H`. The arc `α ⊂ g_i Y ∩ g_j Y`, so by (I1), `|α| <= D - 1`.
- **Otherwise.** Some `t`-side contains `α`, so `|α| <= τ`.

Therefore

    |Σ| <= (4k - 3) max(D, τ).                                   (1.1)

## 2. Bounded multiplicity at an edge

Fix an edge `e = {u, v}` of `T`. Let `B_e` be the set of vertices within
distance `D` of `u` or `v`. For a geodesic `σ ∋ e`, its *trace* is the maximal
subsegment of `σ` inside `B_e` that contains `e`.

**Lemma 2.1.** Coset sides of distinct cosets through `e` have distinct traces.

*Proof.* Suppose `σ_i ⊂ g_i Y` and `σ_j ⊂ g_j Y`, with `g_i H != g_j H`, have
the same trace `ρ`.
- **An endpoint of `ρ` is not an endpoint of `σ_i`.** Then `σ_i` continues
  past it, so that endpoint is at distance exactly `D` from `e`, and
  `|ρ| >= D + 1`. But `ρ ⊂ g_i Y ∩ g_j Y`, which contradicts (I1).
- **Both endpoints of `ρ` are endpoints of `σ_i`.** The same argument applies
  to `σ_j`, so `σ_i = ρ = σ_j` as segments. An endpoint of `σ_i` lies in
  `g_i H`, and an endpoint of `σ_j` lies in `g_j H`. Distinct left cosets are
  disjoint, which is a contradiction. QED.

A trace is determined by its two endpoints. One endpoint lies on the `u`-side
of `e`, the other on the `v`-side, each within distance `D`. So there are at
most `(sum_{j=0}^{D} (2r-1)^j)^2 <= (2r)^(2D+2)` traces. Since the cosets on a
simple cycle are distinct, at most `(2r)^(2D+2)` coset sides contain `e`.

**`t`-sides.** A `t`-side is `y·[1, t]` or `y·[1, t^{-1}] = (y t^{-1})·[1, t]`,
a translate `z·[1, t]`. If `e ⊂ z·[1,t]`, then `e` is the translate of the
`j`-th edge of the reduced word `t`, for some `j <= τ`, and `z` is determined
by `j` and `e`. So at most `τ` segments `z·[1, t]` contain `e`. A segment is
used by at most two `t`-sides. Otherwise the same coset-graph edge would be
traversed twice in the same direction, and the simple cycle would visit its
initial coset twice. Hence at most `2τ` `t`-sides contain `e`.

**Multiplicity bound.**

    mult(e) := #{sides containing e} <= B := (2r)^(2D+2) + 2τ.         (2.1)

## 3. Linear perimeter

Every side is a geodesic inside `Σ`. So `P = sum_{e ⊂ Σ} mult(e)`, and by
(1.1) and (2.1),

    sum_i |h_i|_S + k τ = P <= B (4k - 3) max(D, τ).                    (3.1)

This is Item 1. It improves the `O(k^2)` perimeter of the earlier node to
`O(k)`.

## 4. Counting cycles: the packing growth is finite

Put `K = 4 B max(D, τ)`, `c = K + 2` and `A = (2r+3)^c`. Fix `e(g)`.
Read the cycle starting with the `t`-side `e(g)`, traversed from `g` to `gt`
or from `gt` to `g`. There are two choices. After that, the cycle is
determined by the string

    h_1 ε_1 h_2 ε_2 ... ε_{k-1} h_k,

which lists, in cyclic order after `e(g)`, the reduced syllable words over
`S^{±1}` and the signs of the remaining `t`-sides. Its
length is at most `P + k <= (K + 1) k`. The alphabet has `2r + 2` symbols.
Strings of length at most `L` number at most `(2r+3)^L`. Hence

    M(k) <= 2 (2r+3)^((K+1)k) <= A^k.                                 (4.1)

**Packing count.** Take an edge-disjoint detour family for `e(g)` with `k_i`
`t`-edges. By the imported loop-erasure step, it gives pairwise distinct simple
cycles through `e(g)` with `j_i <= k_i + 1` `t`-edges. So

    N(R) = #{i : k_i <= R} <= sum_{j=2}^{R+1} A^j <= 2 A^(R+1),
    h = limsup log N(R) / R <= log A < infinity.                      (4.2)

By (2.5) of `research/artifacts/fpbs/small-cancellation-family.md`, the best
packing threshold is `q_* = exp(-h) >= 1/A > 0`. This is Item 2.

## 5. A positive floor for every packing certificate

Let `0 < q <= 1`, and consider any finite or infinite edge-disjoint family.
Since `k_i >= 1` and the cycles are distinct,

    sum_i q^(k_i) <= sum_i q^(j_i - 1) <= sum_{j>=2} A^j q^(j-1).

- **Case `q >= 1/(8A^2)`.** The bound `q + (1-q) prod(...)` is at least
  `q >= δ := 1/(8A^2)`.
- **Case `q < 1/(8A^2)`.**
  - Here `Aq <= 1/2`, so the sum is at most `2A^2 q < 1/4`. Each
    `q^(k_i) <= 1/2`.
  - Using `1 - x >= exp(-2x)` on `[0, 1/2]`, we get
    `prod_i (1 - q^(k_i)) >= exp(-1/2) > 1/2`.
  - Hence the bound is at least `(1-q)/2 >= 1/4 >= δ`.

So (2.1) never yields `mu(A) < δ - η`. Letting `η -> 0`, no packing
certificate gives `relC(E_F; E_H) < δ`. This is Item 3.

The proof of the packing lemma §2.2 uses only three properties: disjoint
supports, the identity lies in no support, and the closing identity of each
detour. So it reads the same for arbitrary detour words `h_0 t^{ε_1} ... h_k =
t`. The floor is an obstruction to that argument, whichever way it is read.

## 6. Uniform floor for `Gamma_mal`

`Gamma_mal` is the union of `H_0 ⊂ H_1 ⊂ ...`. Here `H_m` is free on
`{a, b_m}`, and `b_{m-1} = b_m a b_m^{-2}`. So `H_{m-1} = <a, b_m a b_m^{-2}>`.
For `n < m`, `a ∈ H_n ⊂ H_m`. Hence
`H_m = <a, b_m> = <H_n, b_m>`, and `b_m` is a legitimate single new generator
for the pair `(H_m, H_n)`.

**Reduction to the top pair.** Take a detour
`h_0 b_m^{ε_1} h_1 ... b_m^{ε_k} h_k = b_m` with `h_i ∈ H_n ⊂ H_{m-1}`. It is a
detour over `H_{m-1}` with the same `b_m`-letters at the same group elements.
So edge-disjoint families stay edge-disjoint, with the same `k_i`, and Section
5 applies to `(H_m, H_{m-1}, b_m)`. With basis `{a, b_m}`, this triple is
literally `(F_2, <a, b a b^{-2}>, b)`. There the Stallings graph has 3
vertices, so `D = 9` (computed in `research/artifacts/fpbs-malnormal-coset-cycles-2026-09-17.md`
§2), `τ = 1` and `r = 2`. So the floor is the single constant
`δ_mal = δ(F_2, <a, b a b^{-2}>, b)`, independent of `n < m`.

**Double-coset generators.** Let `t' = h b_m^{ε} h'` with `h, h' ∈ H_n`.
Substituting this expression turns a `t'`-detour into a `b_m`-detour with the
same number of new letters. The `t'`-edge at `z` goes to the `b_m`-edge at
`z h` (or at `z h b_m^{-1}` when `ε = -1`), and this map is injective. So the
same floor holds.

**Strategies killed.**
- **Stage sums.** `C(Gamma_mal action) <= 2 + sum_n relC(H_{n+1}; H_n)`, with
  each term certified by packing, is at least `2 + sum_n δ_mal = infinity`.
- **Subsequences.** `relC(H_{m}; H_n) -> 0` along `m - n -> infinity`, certified
  by packing with `b_m` or with any `t' ∈ H_n b_m^{±1} H_n`, is impossible.

These are the positive detour-packing routes that the earlier nodes left open.
The earlier node killed only the bounded-length regime. This kills every
growth regime, for these generators.

## 7. What remains

**Long generators.** For `(H_m, H_n)`, other generators `t'` with
`<H_n, t'> = H_m` may lie outside `H_n b_m^{±1} H_n`. For example `t'` may be a
long product with many `b_m`-syllables. Then `τ' = |t'|` is unbounded, and the
proven floor `δ(τ') = (2r+3)^{-2c(τ')}/8` tends to zero. This floor is only
a lower bound on what packing can certify. Packing proves
`relC(H_m; H_n) = 0` for some pair only if some such `t'` has infinite growth
`h_{t'}`. By Item 2 that is impossible for each fixed `t'`. So the packing
lemma, taken as a single-generator certificate, **never** gives
`relC(H_m; H_n) = 0` at a malnormal stage. The most it can give is
`relC <= inf_{t'} exp(-h_{t'})`. Whether this infimum is `0` is the open
decomposition `fpbs-mal-long-generator-packing-growth`.

**Multi-generator repairs.** Repairs that keep several generators on
correlated sets are not covered by (2.1). Neither are repairs that are not
Bernoulli colorings.
