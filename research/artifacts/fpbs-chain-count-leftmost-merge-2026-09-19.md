# Uniform exponential count of vertex-simple relative-position chains: closed tree walks and leftmost merges

Worker `swarm-0917-w16-w16-fp-pull`, target
`fpbs-mal-simple-chain-count-uniform`. Code:
`experiments/fpbs-chain-count-leftmost-merge-2026-09-17/`.

## 0. Setting and standing facts

`F = F(a, b)`, `K = <a, c>`, `c = b a b^{-2}`, malnormal of rank 2, with
Stallings core `Γ`: vertices `0, 1, 2`, edges `0 -a-> 0`, `0 -b-> 1`,
`1 -a-> 2`, `1 -b-> 2`. `T` is the right Cayley tree of `F` (edges
`y — ys`), with `F` acting freely on the left. `T_K` is the convex hull of
`K`. The class `Ky` has hull `X(Ky) = y^{-1} T_K`. Every vertex of a hull
has a *type* in `{0, 1, 2}` (its image in `Γ = K \ T_K`).

The following are proved in `fpbs-mal-two-step-relative-position-rigidity-proof`
(steps 1 to 3) and are re-derived here only where needed.

- **(S)** `Ky -> X(Ky)` is a bijection onto the translates of `T_K`, and
  `Stab(X(Ky)) = y^{-1} K y` acts freely on vertices.
- **(T0)** Two distinct hulls never share a vertex of the same type: if
  `v in X ∩ gX` has type `t` in both, then `v = u r` and `g^{-1} v = u k r`
  with `k in K` (`K` is transitive on type-`t` vertices of `T_K`), and
  freeness gives `g = u k^{-1} u^{-1}`, which stabilizes `X = u T_K`.
- **(F1)** Distinct hulls share at most 2 edges. The common subtree
  immerses, as a labelled graph, into the off-diagonal part of the fibre
  product `Γ ×_F Γ` (by (T0)). `offdiag.py` shows this part is two trees
  with 3 vertices and 2 edges each. A labelled immersion of a tree into a
  folded tree is injective.
- **(P)** The stabilizer in `F` of an ordered pair `(X, Y)` of distinct
  hulls is trivial: it lies in `y^{-1}Ky ∩ z^{-1}Kz`, which is trivial by
  malnormality when `Ky ≠ Kz`.
- **(O)** Relative positions are the orbits of the diagonal action. The
  map `(Ky, Kz) -> D = K z y^{-1} K` induces a bijection from diagonal
  `F`-orbits of ordered pairs of distinct classes to double cosets
  `D ≠ K`. Right multiplication of classes by `g` matches left
  multiplication of hulls by `g^{-1}`.

  *Proof of (O).* `D` is invariant under `(A, B) -> (Ag, Bg)`. If
  `D(Ky, Kz) = D(Ky', Kz')`, move both pairs by `y^{-1}` and `y'^{-1}` to
  `(K, Kh)` and `(K, Kh')` with `KhK = Kh'K`, so `h' = k h k'`. Then
  `g = k'` maps `(K, Kh)` to `(K, K h k') = (K, Kh')`.

## 1. Canonical connectors

For every ordered pair `(X, Y)` of distinct hulls fix vertices
`out(X, Y) in X` and `in(X, Y) in Y`, as follows.
- If `X ∩ Y = ∅`, they are the endpoints of the bridge (the unique shortest
  geodesic from `X` to `Y`). The bridge meets `X` only in `out(X, Y)` and
  `Y` only in `in(X, Y)`.
- If `X ∩ Y ≠ ∅`, pick one vertex `v` of `X ∩ Y` for one representative
  pair of each diagonal orbit, transport it by the unique group element
  (by (P)), and put `out = in = v`.

Both rules are `F`-equivariant: `out(gX, gY) = g out(X, Y)`, and the same
for `in`. Write `br(X, Y)` for the geodesic from `out(X, Y)` to
`in(X, Y)`. It is empty exactly when `X ∩ Y ≠ ∅`.

**Lemma 1.1 (exit vertices determine the neighbour).** Fix a hull `X` and a
double coset `D ≠ K`. The map `Y -> out(X, Y)`, on the hulls `Y` at
relative position `D` from `X`, is injective.

*Proof.* By (O) and (S), these `Y` form one orbit `Stab(X) Y_0`, on which
`Stab(X)` acts freely. Equivariance gives `out(X, κ Y_0) = κ out(X, Y_0)`,
and `Stab(X)` acts freely on the vertices of `X`. ∎

## 2. The walk of a chain

A *chain* is a sequence of pairwise distinct hulls `X_0, ..., X_n`. Its
label sequence is `D_i = D(X_{i-1}, X_i)`. For `1 <= i <= n` put
`x_i = out(X_{i-1}, X_i)`, `y_i = in(X_{i-1}, X_i)` and
`β_i = br(X_{i-1}, X_i)`. For `1 <= i <= n-1` let `p_i` be the geodesic
from `y_i` to `x_{i+1}`. It lies in `X_i`, because hulls are convex. Call
`p_i` the *hull path* of `X_i`, and call `X_i` *short* if `|p_i| <= 4`.

**Lemma 2.1 (closed walk forces a short hull).** Suppose
`X_0 ∩ X_n ≠ ∅` and `n >= 2`. Then some interior hull `X_i`
(`1 <= i <= n-1`) is short.

*Proof.* Fix `z in X_0 ∩ X_n`. Let `p_0` be the geodesic from `z` to `x_1`
(inside `X_0`) and `p_n` the geodesic from `y_n` to `z` (inside `X_n`). Then

```text
Π = p_0 β_1 p_1 β_2 p_2 ... p_{n-1} β_n p_n
```

is a closed walk in the tree `T` at `z`. Its label word therefore freely
reduces to the empty word. Suppose, for a contradiction, that
`|p_i| >= 5` for all `1 <= i <= n-1`. Drop the empty `β_i`. Look at each
junction of consecutive segments, and at the maximal cancellation `c`
there between the end of the left segment and the start of the right one.

1. *Junction `p_{i-1} | β_i`, with `β_i` nonempty.* Here `c = 0`. The last
   edge of `p_{i-1}` lies in `X_{i-1}`. The first edge of `β_i` is not in
   `X_{i-1}`, since a bridge meets `X_{i-1}` only in `x_i`. A cancellation
   would make them the same edge. If `p_{i-1}` is empty, then `i = 1`,
   `p_0` is the empty prefix, and nothing lies to the left.
2. *Junction `β_i | p_i`, with `β_i` nonempty.* By the same argument at
   `y_i`, `c = 0`. If `p_n` is empty there is nothing to the right.
3. *Junction `p_{i-1} | p_i`, with `β_i` empty.* Here `c <= 2`. The
   cancelled edges are traversed by `p_{i-1}`, inside `X_{i-1}`, and by
   `p_i`, inside `X_i`. So they are common edges of two distinct hulls, and
   (F1) bounds them by 2.

Every interior hull path loses at most 2 letters at each end, so at least
`5 - 4 = 1` letter survives. Every nonempty `β_i` loses nothing. The end
segments `p_0` and `p_n` can be used up only against their single
neighbour, and nothing lies beyond them, so no cancellation cascades. After
these local cancellations every junction is between surviving letters. They
do not cancel, by maximality at type-3 junctions and by items 1–2 at the
others. So the result is reduced, and it is nonempty because `p_1` keeps a
letter (`n >= 2`). This contradicts free reduction to the empty word. ∎

## 3. Merging a short hull

**Lemma 3.1 (merge).** Let `X_{i-1}, X_i, X_{i+1}` be consecutive hulls of a
chain, with labels `D_i`, `D_{i+1}`, and let `w` be the label word of the
hull path `p_i`. Then the triple `(X_{i-1}, X_i, X_{i+1})` is determined, up
to the diagonal `F`-action, by `(D_i, w, D_{i+1})`. Consequently:
- `D' = D(X_{i-1}, X_{i+1})` is a function `M(D_i, w, D_{i+1})`;
- `X_i` is determined by `(X_{i-1}, X_{i+1})` together with
  `(D_i, w, D_{i+1})`.

*Proof.*
1. Fix, once and for all, a reference pair `(R_0, R_1)` in the orbit `D_i`.
   By (O) and (P) there is a unique `g` with `g(R_0, R_1) = (X_{i-1}, X_i)`.
2. Then `y_i = g in(R_0, R_1)`, and `x_{i+1}` is the endpoint of the path
   with word `w` starting at `y_i`. So `x_{i+1} = g u` with `u` depending
   only on `(D_i, w)`.
3. By Lemma 1.1, applied to `X_i = g R_1` and `D_{i+1}`, the vertex
   `x_{i+1}` determines `X_{i+1}`. By equivariance `X_{i+1} = g R_2`, where
   `R_2` is the unique hull at position `D_{i+1}` from `R_1` with
   `out(R_1, R_2) = u`. So `R_2` depends only on `(D_i, w, D_{i+1})`.
4. Hence `(X_{i-1}, X_i, X_{i+1}) = g (R_0, R_1, R_2)`, which proves the
   first claim, and `D' = D(R_0, R_2)`.
5. For the second claim, `R_0 ≠ R_2` because `X_{i-1} ≠ X_{i+1}`. By (P)
   there is a unique `g'` with `g'(R_0, R_2) = (X_{i-1}, X_{i+1})`. It
   equals `g`, so `X_i = g' R_1`. ∎

The number of possible words `w` of a short hull is small. `T_K` covers the
core `Γ`, whose vertex degrees are 3, 3 and 2. So a vertex of `T_K` starts
at most `3 * 2^{l-1}` reduced paths of length `l >= 1`. The words of length
at most 4 number at most `1 + 3 + 6 + 12 + 24 = 46`.

## 4. Leftmost merge sequences and the count

**Theorem 4.1.** For all right cosets `A ≠ B` of `K` with
`X(A) ∩ X(B) ≠ ∅`, all `n >= 1`, and all double cosets `D_1..D_n ≠ K`,

```text
N_n^{A,B}(D_1..D_n) = #{ vertex-simple A = C_0, ..., C_n = B : D(C_{i-1}, C_i) = D_i }
                   <= 4^{n-2} * 46^{n-1}     (n >= 2),   and N_1 <= 1.
```

In particular `A = K`, `B = Kb` qualifies: `1 in T_K`, and
`b in T_K` (the hull contains the path `1, b, ba, bab^{-1}, bab^{-2}` to
`c in K`), so `1 = b^{-1} b in X(Kb) = b^{-1} T_K`. Hence
`fpbs-mal-simple-chain-count-uniform` holds with `rho = 184`.

*Proof.* `N_1 <= 1` because `C_1 = B` is fixed. For `n >= 2`, apply the
following *leftmost-merge reduction* to a chain `X_0..X_n`. It is the image
of `C_0..C_n` under the bijection (S), so it is a chain of pairwise distinct
hulls with `X_0 ∩ X_n ≠ ∅`.

- While the current chain has length `m >= 2`, Lemma 2.1 provides a short
  interior hull. Let `i` be the least such index, let `w` be its hull-path
  word, and delete `X_i`. The result is again a chain of pairwise distinct
  hulls with the same endpoints. Its labels are those of the old chain with
  `D_i, D_{i+1}` replaced by `M(D_i, w, D_{i+1})`. Record `(i, w)`.
- Stop at length 1.

The *code* of the chain is the record `(i_1, w_1), ..., (i_{n-1}, w_{n-1})`.

*The code determines the chain.* Given `D_1..D_n` and the code, the label
sequence of every intermediate chain follows by applying the `M(·)` of the
recorded merges in order. The final chain is `(X_0, X_n)`, which is fixed.
Undo the merges in reverse order. By Lemma 3.1 the deleted hull `X_i` is
determined by its two current neighbours, by the two labels it had (known
from the label sequence before that merge), and by `w`. So the code
determines the chain, and `N_n` is at most the number of codes that occur.

*Words.* Each `w_k` has length at most 4, so it is one of at most 46
words.

*Indices.* The chain before merge `k` has length `n - k + 1`, so
`1 <= i_k <= n - k`, and `i_{n-1} = 1`. The key constraint is
`i_{k+1} >= i_k - 1`. Deleting `X_i` changes neither the neighbours nor
the two labels of any hull `X_j` with `j <= i - 2`. The hull path of `X_j`
depends only on `X_{j-1}, X_j, X_{j+1}`, through the canonical connectors,
so it is unchanged, and it is still not short because `j < i` and `i` was
least. The new index of `X_j` is `j`. Hence the next least short index is
at least `i - 1`.

Put `d_k = i_{k+1} - i_k + 1 >= 0` for `1 <= k <= n-2`. Then
`sum d_k = i_{n-1} - i_1 + (n - 2) <= n - 2`, and `i_1` is recovered from
the `d_k` as `i_1 = 1 + (n - 2) - sum d_k`. The number of vectors of
`n - 2` nonnegative integers with sum at most `n - 2` is
`binom(2n - 4, n - 2) <= 4^{n-2}`.

Hence `N_n <= 4^{n-2} * 46^{n-1} <= 184^n`. ∎

**Remarks.**
1. *Where the earlier worry dissolves.* The artifact
   `research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md` §4 feared
   an unbounded attachment offset when a bridge runs along a third hull
   `X_j`. The proof never locates any hull relative to anything but its two
   chain neighbours. The only geometric input is that a closed walk in a
   tree must fold somewhere, and folding is possible only across a short
   hull path (length at most 4) or inside a two-hull overlap (at most 2
   edges). A long bridge running along a third hull is allowed. It just
   never needs to be counted.
2. *Uniformity.* Nothing depends on the lengths of the `D_i`: the bound
   `184^n` is uniform over all label sequences, as Corollary 1 of the
   union-bound artifact requires. With `rho = 184` that corollary gives
   the uniform floor `epsilon_0 = 1/(6 * 184) = 1/1104`.
3. *Disjoint endpoints.* For `X_0 ∩ X_n = ∅` the same walk, closed by the
   bridge from `X_n` to `X_0`, shows that every chain with no short
   interior hull has, after the local cancellations, a reduced word equal
   to the fixed bridge word. So such chains are determined by where their
   segments sit in that word. That count is polynomial in the bridge
   length, not uniform. It is not needed for Lemma 1 of the union-bound
   artifact, whose endpoints `K`, `Kb` intersect.
4. *Generality.* The argument used only: a free group `F`, a malnormal
   finitely generated `K` (hence (S), (T0) and (P)), and a uniform bound
   `e` on the number of edges two distinct hulls share (finite for every
   finitely generated malnormal `K`, by the same fibre-product argument,
   since the off-diagonal part of `Γ ×_F Γ` is then a finite forest). With
   hull paths of length at most `2e` counted as short and `W_K` the number
   of such words, it gives `N_n <= 4^n W_K^n` for any intersecting
   endpoints.
