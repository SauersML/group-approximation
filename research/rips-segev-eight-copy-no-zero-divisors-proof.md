---
rg: 2
id: rips-segev-eight-copy-no-zero-divisors-proof
kind: route
title: Measure the shell arc against its own face rather than the global minimum gamma, count partial end syllables, and charge a covering copy three arc cosets only as often as there are distinct b^2-syllables it can share; since a short face is forced to be almost all b^2 by the girth of Phi, every face length closes every covering by at most eight copies
target: rips-segev-eight-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-six-copy-configurations-carry-no-zero-divisors, rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors]
---

**Conventions.**
- [6C] is `rips-segev-six-copy-no-zero-divisors-proof`, [3C] is `rips-segev-three-copy-no-zero-divisors-proof`,
  [TC] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`, [LG] is
  `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`, and [FL] is
  `rips-segev-steenbock-few-line-a-supports-are-regular-proof`.
- Notation and the standing hypothesis (H_N) are those of [6C]: `alpha != 0`, `w != 0`, `alpha (u + w b) = 0`,
  `X = alpha u`, `Y = alpha w`, and `supp X ∪ supp Y ⊆ V_1 ∪ ... ∪ V_N` for covering copies `C_1, ..., C_N`.
  `Phi` is 8-regular with `girth(Phi) >= 42`, and every relator of the presentation of `K` read along a cycle of
  `Gamma` has syllable length `>= gamma >= 42`.

What is new against [6C]: [6C] used a fixed window of 12 full `b`-syllables, sized from the global bound
`gamma`.  Here the window is sized from the length `l` of the shell face itself, it may begin and end inside a
syllable, and the union bound is sharpened from `2n + e_2` to `2n + min(n, e_2)`.  A short face gives a short
arc, but then the girth of `Phi` forces almost all of its `b`-syllables to be `b^2`, and this is exactly what the
sharpened bound pays for.  The two effects balance at `N = 8` for every `l`.

## 1. The shell face and its `b^2`-syllables

Fix the port cycle, its closed path `pi`, the cyclically reduced label `W'`, the minimal diagram `D` and the shell
face `M` with copy `C_M = h_M g(Gamma)`, as in [3C] Lemma 8 and [6C] §1.  Let `c_M` be the cycle of `Gamma` whose
relator labels `M`, and `l` the syllable length of that relator.

**Lemma 1 (face shape).**
- (a) `l` is even, `l = 2L`, and `l >= 42`.  The relator has `L` `a`-syllables and `L` `b`-syllables, alternating.
- (b) Let `t_1` and `t_2` be the numbers of its `b`-syllables equal to `b^{±1}` and to `b^{±2}`.  Then
  `t_2 >= 42 - L` and `t_1 <= l - 42`.  In particular, if `l = 42` every `b`-syllable of `c_M` is `b^{±2}`.
- (c) `M` has an exterior arc `s` whose label has syllable length at least `sigma(l) = floor(5 l / 8) + 1`.

*Proof.*
- (a) The label is cyclically reduced in `<a> * <b>`, so syllables alternate and `l` is even ([FL] Corollary).
  `l >= gamma >= 42`.
- (b) By [FL] Corollary (and Lemma B) the `b`-edges of `c_M` project to a closed non-backtracking walk in `Phi` of
  length `m = t_1 + 2 t_2`, with `t_1 + t_2 = L`.  A nontrivial closed non-backtracking walk contains a cycle, so
  `m >= girth(Phi) >= 42`.  Hence `t_2 = m - L >= 42 - L`, and `t_1 = L - t_2 <= 2L - 42`.
- (c) This is the face-case analysis in the proof of [LG] Lemma 3, which [3C] Lemma 8 applies with the face's own
  length before bounding it below by `gamma`.
  - If `D` has more than two faces, some shell face has an exterior arc with `|omega(s)| > (1 - 3 lambda) l = 5l/8`.
  - If `D` has two faces, the exterior arc has `|omega(s)| > 7l/8`.
  - If `D` has one face, the arc is the whole boundary.
  In every case `|omega(s)| >= floor(5l/8) + 1`. ∎

## 2. Windows

A *window* is a subarc `s*` of `s`.  Its syllable length counts a partially covered syllable at either end as one
syllable.  Let
- `n*` be the number of `b`-syllables of `s*`, partial ones included;
- `e*` the number of `b`-syllables of `W'` equal to `b^{±2}` whose two edges both lie in `s*`;
- `E* = n* + e*` the number of `b`-edges of `s*`.

Write `v_0, ..., v_{E*}` for the cosets that the part of `pi` read along `s*` visits between its `b`-edges, as in
[6C] §1.

**Lemma 2 (window cosets).**  Assume `E* <= 39`.
- (a) The `v_r` are pairwise distinct, and each meets `V_M` in its own line `l_r`, with the `l_r` pairwise distinct.
- (b) Every `v_r` is active and meets some covering copy.
- (c) The indices `0 < r < E*` at which the `a`-syllable is `a^0` are exactly the middles of the `e*` whole
  `b^{±2}`-syllables of `s*`.
- (d) A copy `C_m != C_M` shares at most three of the `v_r` with `C_M`, and if three, they are the three cosets
  of one whole `b^{±2}`-syllable of `s*`.
- (e) For a family of `n` copies other than `C_M`, at most `2n + min(n, e*)` of the `v_r` lie in `S(C_M, C)` for a
  member `C` of the family.

*Proof.*
- (a)-(c) These are the proofs of [6C] Lemma 1, applied to `s*`.
  - Every `b`-edge of `s*` is an edge of `pi`, hence a port edge, even when it belongs to a `b^2`-syllable only half
    covered by `s*`.  So both of its endpoints lie in `supp X ∪ supp Y`, and every `v_r` is active and covered.
  - The projection of `s*` to `Phi` is a non-backtracking walk of length `E* <= 39 < 42`, so its vertices are
    pairwise distinct.
  - A half-covered `b^2` at an end of `s*` contributes one `b`-edge and no interior index `r`.
- (d) This is the proof of [6C] Lemma 2.  The only numerical input there is that the walk-plus-run cycle has length
  `<= E* + 2 <= 41 < 42`.
- (e) Let `x` members of the family meet three of the `v_r`.  By (d) they use `y` distinct whole
  `b^{±2}`-syllables of `s*`, where `y <= x <= n` and `y <= e*`.  The union then has at most
  `2 (n - x) + 3 y <= 2n + y` elements. ∎

## 3. The criterion

**Lemma 3 (window criterion).**  Under (H_N), no window `s*` with `E* <= 39` satisfies
`n* + max(0, e* - N) >= 2N`.

*Proof.*
- *Shell outside the covering.*  All `E* + 1` cosets `v_r` lie in `S(C_M, C_m)` for covering copies
  `C_m != C_M` (Lemma 2(a)-(b)).  Lemma 2(e) with `n = N` gives `n* + e* + 1 <= 2N + min(N, e*)`, that is
  `n* + 1 + max(0, e* - N) <= 2N`.
- *Shell inside the covering.*  As in [6C] Lemma 5: at most one `v_r` is pure ([3C] Corollary 2 with Lemma 2(a)).
  Every impure one is linked to one of the other `N - 1` covering copies, by a shared coset or by the unique
  bridge of the pair ([TC] Corollary 2).  Lemma 2(d)-(e) then gives `n* + e* <= 2(N - 1) + min(N - 1, e*)`, that is
  `n* + max(0, e* - N + 1) <= 2N - 2`.
- If `n* + max(0, e* - N) >= 2N`, the outside inequality fails.  So does the inside one, because
  `max(0, e* - N + 1) >= max(0, e* - N)` and `2N > 2N - 2`. ∎

## 4. The eight-copy theorem

**Theorem.**  Let `k` be a field, `u, w in k[<a>]` and `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then `supp(alpha u) ∪ supp(alpha w)` lies in no union of eight copies
`h_m g(V(Gamma))`, `h_m in K`.  The same holds in `k[G]`, with `h_m in G`.

*Proof.*  Take (H_N) with `N = 8`; smaller `N` reduce to this by repeating a copy.  A port cycle exists ([3C]
Lemma 6), so `D` has faces and the shell face `M` exists.  In each case below a window of `s` meets Lemma 3's
criterion `n* + max(0, e* - 8) >= 16` with `E* <= 39`, which is impossible.  Windows are taken with exactly the
stated syllable length inside `s`, which is possible by Lemma 1(c).  The `a`- and `b`-syllables of a window alternate.

- *`l = 42`.*  `sigma = 27`, and every `b`-syllable of `c_M` is `b^{±2}` (Lemma 1(b)).  Take 27 syllables.
  - If both ends are `a`-syllables: `n* = 13`, all whole, `e* = 13`, `E* = 26`.  Then `13 + 5 = 18 >= 16`.
  - If both ends are `b`-syllables: `n* = 14`, at most two half covered, `e* >= 12`, `E* <= 28`.  Then
    `14 + 4 = 18 >= 16`.
- *`l = 44`.*  `sigma = 28` and `t_1 <= 2`.  Take 28 syllables.  Then `n* = 14`, and exactly one end is a
  `b`-syllable.  A `b`-syllable of the window is not a whole `b^2` only if it is one of the `t_1` singles or is the
  half-covered end, so `e* >= 14 - 2 - 1 = 11`.  `E* <= 28`, and `14 + 3 = 17 >= 16`.
- *`l = 46`.*  `sigma = 29` and `t_1 <= 4`.  Take 29 syllables.
  - `a`-ends: `n* = 14`, `e* >= 10`.  Then `14 + 2 = 16`.
  - `b`-ends: `n* = 15`, `e* >= 15 - 4 - 2 = 9`.  Then `15 + 1 = 16`.
  - In both, `E* <= 30`.
- *`l = 48`.*  `sigma = 31` and `t_1 <= 6`.  Take 31 syllables.
  - `a`-ends: `n* = 15`, `e* >= 9`.  Then `15 + 1 = 16`.
  - `b`-ends: `n* = 16`.  Then `16 >= 16`.
  - In both, `E* <= 32`.
- *`l >= 50`.*  `sigma >= 32`.  Take 32 syllables: `n* = 16` and `E* <= 32`, so `16 >= 16`. ∎

*In `k[G]`.*  As in [3C] §4 and [6C] §4: split `alpha` over the left `K`-cosets, translate each piece into `K`,
and note that each piece is supported in the at most eight copies lying in its coset.

**Faces with at most two faces in `D`.**  Here Lemma 1(c) gives more than `7l/8 >= 36.75` syllables.  Windows
of 37 syllables have `n* >= 18` and `E* <= 38`, so these diagrams are excluded for every `N <= 9`.

## 5. What is left

- *Exact `N = 9` residue.*  Lemma 3 at `N = 9` needs `n* + max(0, e* - 9) >= 18`.
  - It holds for `l >= 56`: `sigma >= 36`, so there is a window with `n* = 18` and `E* <= 36`.
  - It holds whenever `D` has at most two faces (§4).
  - It can fail for `42 <= l <= 54` when `D` has more than two faces.  For example at `l = 42` the best window gives
    `13 + 4 = 17` or `14 + 3 = 17`, one short.
  So a counterexample with nine copies has a shell face of length `42..54` in a diagram with at least three faces.
  At `l = 42` it is all `b^2` and meets the covering with equality in Lemma 2(e) up to one coset.
- *The next sharpening.*  Consecutive whole `b^2`-syllables of a window share their end cosets.  So copies that
  realise the `+1` of Lemma 2(e) on consecutive syllables overlap.  Charging runs of consecutive shared syllables,
  rather than syllables, should bound the union by `2n + rho`, with `rho` the number of such runs.  That would give
  `N = 9` at `l = 42`.  It has not been checked.
- *Counting alone is bounded.*  Lemma 3 needs `E* <= 39`, and `n* + max(0, e* - N) >= max(n*, E* - N)`.  So even for
  long faces this method stops near `N = 12` (`E* = 38`, `38 - N >= 2N`).  The general case of
  `rips-segev-groups-satisfy-kaplansky-zero-divisor` needs the induction of [6C] §6: an extremal copy of a minimal
  covering with at most two dirty cosets.  Its coefficient-free form is false
  (`rips-segev-coefficient-free-extremal-copy-lemma-fails`).  A coefficient-aware form, for example an extremal
  active coset chosen by a height function on the Bass-Serre tree of `<a> * <b>` together with the rank-one
  lemma, is untried.

## 6. Checks

- *Calibration against [6C].*  A 12-syllable window of full `b`-syllables is the case `n* = 12` with ends not
  counted.  Lemma 3 then reads `12 + max(0, e_2 - N) >= 2N`, which gives `N <= 6` with the old bound `2n + e_2`.
  The gains are: (i) the face's own length in place of `gamma`; (ii) partial end syllables; (iii) `min(n, e*)` in
  place of `e*`; (iv) the girth forcing short faces to be `b^2`-rich (Lemma 1(b)).
- *Arithmetic of `sigma`.*  `floor(5l/8) + 1` is 27, 28, 29, 31 and 32 for `l` = 42, 44, 46, 48 and 50.  For
  `l = 48`, `5l/8 = 30` exactly, and the strict inequality gives 31.
- *Girth uses.*  Distinct window cosets need `E* < 42`.  Lemma 2(d) needs `E* + 2 < 42`.  Lemma 1(b) needs the
  projected face walk to have length at least 42.  All windows used have `E* <= 32`.
- *Coefficient input.*  As in [6C], only [3C] Corollary 2 (rank-one) and the port equations `X(z b) = - Y(z)` are
  used.  Rigidity is not used.
