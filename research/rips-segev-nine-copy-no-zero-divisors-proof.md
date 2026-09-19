---
rg: 2
id: rips-segev-nine-copy-no-zero-divisors-proof
kind: route
title: Replace Greendlinger's single shell by the whole curvature budget of the port-cycle disc; a shell with at most two interior arcs has a long enough arc for the window criterion at N = 9, and otherwise at least six three-arc shells of length 42..54 each carry at least 21 b-edges, which is more than the 117 active cosets of a nine-copy covering can supply
target: rips-segev-nine-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-eight-copy-configurations-carry-no-zero-divisors, rips-segev-six-copy-configurations-carry-no-zero-divisors, rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors]
artifacts: [experiments/rips-segev-nine-copy-2026-09-17/nine_copy_counts.py]
---

**Conventions.**
- [8C] is `rips-segev-eight-copy-no-zero-divisors-proof`.  [6C], [3C], [TC] and [LG] are as there.
- Notation and the standing hypothesis (H_N) are those of [8C]: `alpha != 0`, `w != 0`, `alpha (u + w b) = 0`,
  `X = alpha u`, `Y = alpha w`, and `supp X ∪ supp Y ⊆ V_1 ∪ ... ∪ V_N` for covering copies `C_1, ..., C_N`.
- Fix a directed port cycle through `L` distinct active cosets `T_0, ..., T_{L-1}` ([3C] Lemma 6), its closed path
  `pi`, its label `W = b a^{n_0} ... b a^{n_{L-1}}` with cyclic reduction `W'`, and a minimal diagram `D` for `W'`
  in the standing reading of [LG] Lemma 3, as in [3C] §5 and [8C] §1.

What is new against [8C]: [8C] uses one face from Greendlinger's lemma, whose arc has only more than `5l/8`
syllables when `D` has more than two faces.  Here the whole curvature budget of `D` is used.  Either some shell is
much better than Greendlinger's (at most two interior arcs), or there are many shells, and together their arcs
carry more `b`-edges than the port cycle has.

## 1. The diagram is a disc with `L` boundary `b`-edges

**Lemma 1.**
- (a) `pi` is a simple closed path with exactly `L` `b`-edges.
- (b) `D` is a disc: it has no cut vertex, and its boundary path is simple.
- (c) The exterior arcs of distinct faces of `D` have no edge in common.  So the numbers of `b`-edges on the
  exterior arcs of any set of faces add up to at most `L`.

*Proof.*
- (a) The vertices of `pi` are the vertices of the `a`-segments `a^{n_j}` inside the cosets `T_{j+1}`, one
  segment per coset.  The cosets are pairwise distinct and a segment is a simple path in its coset, so no vertex
  repeats.  `W` has exactly `L` letters `b`.  Cyclic reduction only regroups `b b` into the syllable `b^2` when
  `n_j = 0`.  It cancels no letter, because `W` is positive in `b`.
- (b) The boundary path of `D` maps onto `pi`.  A cut vertex, or any repeated vertex of `∂D`, would be a repeated
  vertex of `pi`.
- (c) An exterior arc of a face `f` is a maximal subpath of `∂D ∩ ∂f`.  In a disc, a boundary edge lies on exactly
  one face. ∎

## 2. Curvature

Assume `D` has at least two faces.  Forget the vertices of degree 2, so that every vertex has degree `>= 3`.
- The boundary of each face is then a cycle of *arcs*.
  - An *interior arc* is a maximal path shared by two faces.  In a minimal diagram it is a piece.
  - An *exterior arc* is a maximal subpath of `∂D ∩ ∂f`.
- By `Gr'_*(1/8)`, every interior arc of a face `f` of syllable length `l(f)` has syllable length `< l(f)/8`.
  Syllable length is subadditive under concatenation.  This is the same input as Greendlinger's lemma in [LG]
  Lemma 3.

Put angles on corners:
- `2 pi / d` at an interior vertex of degree `d`;
- `pi / (d - 1)` at each of the `d - 1` corners of a boundary vertex of degree `d`.

Then every vertex has curvature 0.  Let `κ(f) = 2 pi - sum over corners c of f of (pi - angle(c))`.

**Lemma 2 (Gauss–Bonnet).**  `sum_f κ(f) = 2 pi`.

*Proof.*  Let `F` be the number of faces, `E` the number of edges, and `V_int`, `V_∂` the numbers of interior and
boundary vertices.
- The number of corners is `sum_{v int} d(v) + sum_{v ∂} (d(v) - 1) = 2E - V_∂`.
- The angles sum to `2 pi V_int + pi V_∂`.
- So `sum κ(f) = 2 pi F - pi (2E - V_∂) + 2 pi V_int + pi V_∂ = 2 pi (V - E + F) = 2 pi`, since `D` is a disc
  (Lemma 1(b)). ∎

**Lemma 3 (face curvature).**  Let `f` have `k` exterior arcs and `i` interior arcs.
- (a) If `k = 0`, then `i >= 9` and `κ(f) <= - pi`.
- (b) If `k >= 2`, then `κ(f) <= 0`.
- (c) If `k = 1`, then `i >= 1`, `κ(f) <= (4 - i) pi / 3`, and the exterior arc has more than `(8 - i) l(f) / 8`
  syllables.  Call such an `f` a *shell with `i` interior arcs*.

*Proof.*  `f` has `k + i >= 2` arcs and as many corners.
- A corner at an interior vertex has `pi - angle >= pi - 2 pi/3 = pi/3`.  A corner at a boundary vertex has
  `pi - angle >= pi - pi/2 = pi/2`.
- Two exterior arcs of `f` are never consecutive: they would meet at a boundary vertex with a single corner of `f`,
  so they would be one arc, or else the vertex would be a cut vertex.  Hence `i >= k`.
- The `2k` corners at the ends of exterior arcs are pairwise distinct and lie on `∂D`.
- (a) `l(f)` is less than `i · l(f)/8`, so `i >= 9`, and `κ(f) <= 2 pi - 9 pi/3 = - pi`.
- (b) `κ(f) <= 2 pi - 2k · pi/2 - (i - k) · pi/3 <= 2 pi - k pi <= 0`.
- (c) If `i = 0`, then `∂f = ∂D` and `D` would have one face.  Otherwise
  `κ(f) <= 2 pi - 2 · pi/2 - (i - 1) pi/3 = (4 - i) pi/3`.  The arc bound comes from `l(f) <= |s| + i · max`,
  with each piece `< l(f)/8`. ∎

**Corollary 4.**  If `D` has at least two faces, then `sum over shells of (4 - i) >= 6`.  So either some shell has
`i <= 2`, or at least six shells have `i = 3`.

*Proof.*  Lemmas 2 and 3 give `2 pi <= sum over shells of (4 - i) pi/3`.  Shells with `i >= 4` contribute
`<= 0`.  If no shell has `i <= 2`, the six units come from shells with `i = 3`, one each. ∎

## 3. Short and long shells close by a window

[8C] Lemmas 1-3 apply to *every* face `M` of `D` with an exterior arc `s`, not only to the one chosen there.
- Lemma 1(a)-(b) is about the relator of `M`.
- Lemma 2 is about windows in any exterior arc; its copy is `C_M`, the copy carrying `∂M`.
- Lemma 3 is about one such window.

So under (H_9) no exterior arc of any face contains a window with `E* <= 39` and `n* + max(0, e* - 9) >= 18`.

Recall from [8C] Lemma 1(b) that a face of length `l` has at most `t_1 <= l - 42` single `b`-syllables.

**Lemma 5 (short shells).**  Under (H_9), no shell has `i <= 2`.

*Proof.*  By Lemma 3(c) the arc has at least `floor(3l/4) + 1` syllables.  That is 32, 34, 35 and `>= 37` for
`l` = 42, 44, 46 and `>= 48`.  In each case below, take a window of the stated length at one end of the arc.
- *`l = 42`, 32 syllables.*  One end is a `b`-syllable.  So `n* = 16` and `e* >= 15`, since all syllables are
  `b^2` by [8C] Lemma 1(b).  Then `E* <= 31` and `16 + 6 = 22 >= 18`.
- *`l = 44`, 34 syllables.*  `n* = 17` with one half end, and `t_1 <= 2`, so `e* >= 14`.  Then `E* <= 34` and
  `17 + 5 = 22`.
- *`l = 46`, 35 syllables.*  `t_1 <= 4`.
  - `a`-ends: `n* = 17`, `e* >= 13`, `E* <= 34`.  Then `17 + 4 = 21`.
  - `b`-ends: `n* = 18`, `E* <= 36`.
- *`l >= 48`, 36 syllables.*  `n* = 18` and `E* <= 36`.

Each case violates [8C] Lemma 3. ∎

**Lemma 6 (long shells).**  Under (H_9), every shell with `i = 3` has `l <= 54`.

*Proof.*  For `l >= 56` the arc has at least `floor(5l/8) + 1 >= 36` syllables.  A 36-syllable window has
`n* = 18` and `E* <= 36`, against [8C] Lemma 3. ∎

**Diagrams with one face.**  Then `s = ∂D` has `l >= 42` syllables, and a 36-syllable window closes as in Lemma 6.
(This, together with Lemma 5 for two faces, recovers the "at most two faces" remark of [8C] §4.)

## 4. Six shells against 117 cosets

**Lemma 7 (`b`-edges on a three-arc shell).**  A shell with `i = 3` and length `l` carries at least `beta(l)`
`b`-edges on its exterior arc, where

| `l` | 42 | 44 | 46 | 48 | 50 | 52 | 54 |
|---|---|---|---|---|---|---|---|
| `sigma(l) = floor(5l/8) + 1` | 27 | 28 | 29 | 31 | 32 | 33 | 34 |
| `t_1 <= l - 42` | 0 | 2 | 4 | 6 | 8 | 10 | 12 |
| `beta(l)` | 26 | 25 | 24 | 24 | 23 | 22 | 21 |

*Proof.*  Take a subarc of exactly `sigma(l)` syllables, possible by Lemma 3(c).
- Let `n` be its number of `b`-syllables and `t` the number of whole single `b`'s.  Let `p` be the number of end
  syllables that are `b`-syllables, which bounds the number of partly covered ones.
- Each `b`-syllable contributes at least one edge.  A whole one that is not single is `b^2` and contributes two.
  So the arc has at least `n + (n - p - t)` `b`-edges, with `t <= t_1`.
- The minimum over the two end types is the table.
  - `sigma` odd with `a`-ends: `n = (sigma - 1)/2` and `p = 0`.
  - `sigma` odd with `b`-ends: `n = (sigma + 1)/2` and `p = 2`.
  - `sigma` even: `n = sigma/2` and `p = 1`.
  - For example, at `l = 54`: `n = 17`, `p = 1`, `t = 12`, so the bound is `17 + 4 = 21`.
- `experiments/rips-segev-nine-copy-2026-09-17/nine_copy_counts.py` recomputes the table. ∎

**Theorem (nine copies).**  Let `k` be a field, `u, w in k[<a>]` and `alpha in k[K]`, with `alpha != 0`,
`w != 0` and `alpha (u + w b) = 0`.  Then `supp(alpha u) ∪ supp(alpha w)` lies in no union of nine copies
`h_m g(V(Gamma))`, `h_m in K`.  The same holds in `k[G]`, with `h_m in G`.

*Proof.*  Assume (H_9).  Smaller `N` reduce to this by repeating a copy.  The port cycle exists and `D` has faces
([3C] Lemma 6).  One face is excluded by §3, so `D` has at least two faces.
- By Corollary 4 and Lemma 5, at least six shells have `i = 3`.
- By Lemma 6 their lengths lie in `42..54`.
- By Lemma 7 each of their exterior arcs carries at least 21 `b`-edges.
- By Lemma 1(c), `L >= 6 · 21 = 126`.

On the other side, every active coset meets `supp X ∪ supp Y ⊆ V_1 ∪ ... ∪ V_9`, so it is clean or dirty.
- There are at most 9 clean ones ([3C] Proposition 4(i)) and at most `3 · 36 = 108` dirty ones ([3C] Lemma 5).
- The port cycle visits distinct active cosets, so `L <= 117 < 126`.  Contradiction. ∎

*In `k[G]`.*  As in [3C] §4 and [8C] §4: split `alpha` over the left `K`-cosets and translate each piece into `K`.

## 5. Checks and limits

- *Calibration.*
  - Lemma 3(c) with `i = 3` is Greendlinger's `5l/8`, and with `i = 1` it is the two-face `7l/8` of [LG].  So at
    `N <= 8` the windows of §3 are those of [8C], and the new ingredient is the curvature count of §2.
  - In the free product `<a> * <b>` there are no relators.  There the positive word `W` is already `!= 1`, so no
    diagram exists and the argument never starts.  This is the correct answer for a torsion-free free product.
    Lemmas 2-3 are the standard curvature proof of Greendlinger's lemma, and they reproduce its constants.
  - Nothing here uses coefficients beyond [8C] Lemma 3, which uses the rank-one lemma ([3C] Corollary 2).
- *Where it stops.*  At `N = 10` the criterion needs `n* + max(0, e* - 10) >= 20`.
  - Three-arc shells survive for `l <= 62`, and two-arc shells for some `l`, for example `l = 50` with 38 syllables.
  - Six three-arc shells carry about `6 · 20 = 120 < 145 = A(10)` `b`-edges.
  - The shortfall grows with `N`: surviving shells carry about `2N` `b`-edges, and `12 N` is far below
    `A(N) ~ 1.5 N^2`.
  So this is the last `N` that curvature plus the active-coset bound reaches.  The general case still needs the
  coefficient-aware extremal-copy step of [6C] §6.
- *Girth uses.*  All windows have `E* <= 36 < 40`, as [8C] Lemma 2 requires (`E* + 2 < 42`).
