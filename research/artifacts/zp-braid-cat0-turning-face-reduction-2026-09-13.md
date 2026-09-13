# Turning-face reduction for the CAT(1) diagonal links of NCP_n (lane z3-06-braid-cat0, 2026-09-13)

Status: written derivation assembling published lemmas of Haettel–Kielak–Schwer (HKS, arXiv:1304.5990v2)
with two small lemmas proved here (face version of HKS Lemma 4.15; Kreweras duality extends to the building).
Unreviewed. It feeds `diagonal-links-cat1-from-turning-face-conditions`.

## Setup

- `NCP_n`: noncrossing partitions of `U_n = Z/n` (points on a circle), ordered by refinement, rank `n - #blocks`.
  A *block* means a non-singleton block. A partition is *universal* when it has exactly one block and that block is
  a cyclic interval.
- `X_n`: the diagonal link `LK(e_01, |NCP_n|)` of the orthoscheme complex, with the spherical orthoscheme metric.
  Its vertices are `NCP_n \ {0, 1}` and its faces are chains `F = (P_1 < ... < P_k)`.
- `V = {y in F^n : sum y_i = 0}`, `f(x) = {y in V : sum_{i in Q} y_i = 0 for every block Q of x}` (HKS Lemma 2.24).
  `f` is an injective rank-preserving poset map `NCP_n -> S(V)`, and `X_n` is linearly embedded (HKS Definition 3.8)
  in `B_n = LK(e_01, |S(V)|)`, a spherical building of type `A_{n-2}` (HKS Proposition 2.18), which is CAT(1).
- For a chain `F` and `i in U_n`: `F_i` is the smallest block containing `i` among partitions of `F`, or `U_n` if `i`
  is a singleton in every partition of `F`; `F'_i = F_i ∩ {i-1, i+1}`. Gaps of `F`: `(0, P_1)`, `(P_j, P_{j+1})`,
  `(P_k, 1)`; a partition in a gap forms a chain with `F`.
- `x, y` *fail modularity* when `f(x) + f(y)` or `f(x) ∩ f(y)` is not `f(z)` for a noncrossing `z` (HKS
  Definition 2.7). Combinatorially: `f(x) + f(y) = f(x v_P y)` (join in the full partition lattice), so the join fails
  iff `x v_P y` is crossing; the meet fails iff `b(x) + b(y) - b(x v_P y) != b(x ^ y)`, where `b` counts blocks
  including singletons and `x ^ y` is the common refinement (always noncrossing).

## The four conditions on a chain F

- **I.** `{1, ..., n-2} \ rk(F)` contains two consecutive integers.
- **II.** Some partition of `F` is not universal.
- **III'.** Some gap of `F` contains two partitions that fail modularity. (Jeong's III asks instead for two crossing
  partitions in a gap; his Theorem 9 shows III' implies III.)
- **IV.** There is a maximal chain `C` of `NCP_n` with `F'_i ∩ C'_i = ∅` for every `i`.

## Theorem R

Let `n >= 5` and suppose `X_m` is CAT(1) for `3 <= m < n`. If no chain `F` of `NCP_n \ {0, 1}` is such that both `F`
and its Kreweras dual `F*` satisfy I, II, III' and IV, then `X_n` is CAT(1).

*Proof.*

0. `X_n` is locally CAT(1). The link of a face of `X_n` is the link in `|NCP_n|` of a simplex containing `e_01`, a
   spherical join of diagonal links of intervals of `NCP_n`. Those intervals are products of smaller noncrossing
   partition lattices, so by hypothesis the join is CAT(1) (Brady–McCammond §5, as used in HKS Theorem 2.34 and in
   Jeong §4; numbering of the Brady–McCammond statement to be read from the source).
1. If `X_n` is not CAT(1), Bowditch's theorem (HKS Theorem 2.32) gives an unshrinkable short loop `l`, which we may
   take locally geodesic of length `L < 2π`. By HKS Lemma 3.7, `l` has at least three turning points in `B_n`. Fix one,
   `t`, with image `x`, and let `F` be its turning face (HKS Definition 3.10).
2. **I** holds by HKS Lemma 3.12.
3. **II** holds: if every vertex of `F` were universal, `x` would be a universal point and `l` would be shrinkable by
   HKS Lemma 4.8.
4. **III'** holds. Let `E^±` be the minimal faces containing `l([t, t ± ε))` and `C^±` chambers containing them with
   `F = C^+ ∩ C^-`. By HKS Lemma 3.13 the simplicial convex hull of `E^+ ∪ E^-` is not contained in `X_n`, so by HKS
   Lemma 4.9 two vertices `u, u'` of `E^+ ∪ E^-` fail modularity. Vertices of one face are comparable, and the join and
   meet of comparable vertices are among them, so `u ∈ E^+ \ E^-` and `u' ∈ E^- \ E^+`, say. If `u ∈ F ⊆ C^-`, then
   `u, u'` lie in `C^-` and are comparable, which is impossible; so `u ∉ F`, and likewise `u' ∉ F`. Each is adjacent to
   every vertex of `F` (it shares a chamber with `F`), so each lies in a gap of `F`. Vertices in different gaps are
   comparable, so `u, u'` share a gap.
5. **IV** holds. Suppose not. Let `y = l(t + L/2)` and `C` a chamber of `X_n` containing `y`. Since IV fails for `F`,
   there are `i` and `j = i ± 1` with `j ∈ F_i ∩ C_i`. By Lemma A (below) and HKS Lemma 4.15 there are apartments
   `A, A' ⊆ X_n` with `F, v, w ⊆ A` and `C, v, w ⊆ A'`, where `v = {{i, j}}` and `w = {{i}, U_n \ {i}}` are universal
   and opposite in `B_n`. Exactly as in the proof of HKS Theorem 4.17: `d(x, v) + d(x, w) = π = d(y, v) + d(y, w)`, so
   one of them, say `v`, has `d(x, v) + d(v, y) <= π`. The geodesics `[x, v] ⊆ A` and `[v, y] ⊆ A'` lie in `X_n`. The
   two loops formed with the halves of `l` have length `< π + L/2 < 2π` and pass through the universal vertex `v`, so
   they shrink (HKS Lemma 4.8), and then `l` shrinks by Bowditch's three-path theorem (HKS Theorem 2.33). This
   contradicts the choice of `l`.
6. **Duality.** By Lemma D the Kreweras complement extends to an isometry `Φ` of `B_n` with `Φ(X_n) = X_n` that maps
   the face `F` to `F*`. So `Φ ∘ l` is an unshrinkable short locally geodesic loop with turning point `t` and turning
   face `F*`, and steps 2–5 give I, II, III', IV for `F*`. This contradicts the hypothesis. ∎

## Lemma A (HKS Lemma 4.15 for faces)

Let `F` be a face of `X_n` and `i, j` consecutive with `j ∈ F_i`. Then some chamber `C ⊇ F` has `C_i = F_i`, so
`j ∈ C_i` and HKS Lemma 4.15 gives an apartment of `X_n` containing `C` (hence `F`), `v` and `w`.

*Proof.* If `F_i = U_n`, then `i` is a singleton in every vertex of `F`, so every vertex is `<= w = {{i}, U_n \ {i}}`
and `F ∪ {w}` is a face. Any chamber through it keeps `i` a singleton below `1`, so `C_i = U_n`.
Otherwise let `x = P_s` be the lowest vertex of `F` in which `i` is not a singleton, so `F_i` is its block containing
`i`. If `rk(x) = 1`, or the previous vertex of `F` has rank `rk(x) - 1`, every chamber through `F` has `C_i = F_i`:
vertices below `x` refine the previous vertex (or `0`), where `i` is a singleton. Otherwise let `x^-` be `x` with `i`
removed from its block. Then `x^-` is noncrossing, `rk(x^-) = rk(x) - 1`, and `x^- < x`; the previous vertex of `F`
(where `i` is a singleton) is `<= x^-` and of smaller rank. So `F ∪ {x^-}` is a face, and every chamber through it has
`C_i = F_i`. ∎

## Lemma D (Kreweras duality is orthogonality)

For `y ∈ V` let `s_k(y) = y_1 + ... + y_k` (so `s_n = 0`), and define `<y, z> = sum_{k=1}^{n} s_k(y) z_k` on
`V × V`. Label the point between `k` and `k+1` by `k`, and let `K(x)` be the Kreweras complement: `k, l` share a block
iff the chord between the in-between points `k'`, `l'` meets no block of `x`. Then:

1. `<,>` is nondegenerate on `V × V`: if `<y, z> = 0` for all `z ∈ V`, then `s(y)` is constant, hence `0`, and
   `y = 0`.
2. `f(K(x)) = f(x)^⊥`. For `k < l` in one block of `K(x)`, every block of `x` lies inside `{k+1, ..., l}` or outside
   it, so `<y, e_l - e_k> = s_l(y) - s_k(y) = sum_{i=k+1}^{l} y_i = 0` for `y ∈ f(x)`. Vectors `e_l - e_k` over such
   pairs span `f(K(x))`, so `f(K(x)) ⊆ f(x)^⊥`. Dimensions: `dim f(K(x)) = n - b(K(x)) = b(x) - 1` (since
   `rk K(x) = n - 1 - rk x`) and `dim f(x)^⊥ = (n - 1) - (n - b(x)) = b(x) - 1`.
3. `U ↦ U^⊥` is an order-reversing, rank-complementing bijection of `S(V)`. Reversing a maximal chain is an isometry of
   the orthoscheme simplex (`(t_1, ..., t_m) ↦ (1 - t_m, ..., 1 - t_1)`), and it swaps `0, 1`. So `U ↦ U^⊥` induces an
   isometry `Φ` of `B_n`, and by item 2 it preserves `f(NCP_n)`, so `Φ(X_n) = X_n` and `Φ(F) = F*`. ∎

## What is left to decide

Theorem R turns "X_n is CAT(1)" into a finite search over chains of `NCP_n`. HKS did it by hand for `n <= 6` (with a
dominant-vertex version of IV), Jeong for `n = 7` (arXiv:2009.09350, Theorem 1, with Jeong's III in place of III').
A mechanical check of both variants for `n = 5, ..., 8` is running on MSI (program `nc_turning.py`, lane dir).
