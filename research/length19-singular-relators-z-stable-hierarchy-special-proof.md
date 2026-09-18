---
rg: 2
id: length19-singular-relators-z-stable-hierarchy-special-proof
kind: route
title: Top Magnus intersection by a line-of-groups immersion, Collins for conjugates, level-one sZ by pullbacks, kbmag for hyperbolicity, then Linton
target: length19-singular-relators-z-stable-hierarchy-special
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
  - unit-alexander-singular-hidden-free-pieces-special
  - length19-singular-relators-small-cancellation-sofic
artifacts:
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_magint.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1_32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/kbhyp.sh
  - experiments/one-relator-top-magnus-intersection-2026-09-18/kbhyp32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_kb.out
---

Date: 2026-09-18. A computation followed by cited theorems.

Fix one of the 32 relators `w` in `rel32.txt`. The exponent sums are `(e_a, e_t) = (+-1, 0)`.

## 0. The hierarchy

Write `a_i = t^i a t^-i`. The Magnus–Moldavanskii rewriting of `w` along `t` gives the
one-relator splitting

    G = B_0 *_psi,  B_0 = <a_0, a_1, a_2 | W_0>,  A = F(a_0,a_1),  B = F(a_1,a_2),  psi(a_i) = a_(i+1).

(`basis_search.magnus`; `|W_0| = 9`, `n = 2`, printed in `magint32.out`.) `W_0` is cyclically
reduced and involves `a_0` and `a_2`, so `A` and `B` are Magnus subgroups, free on the given
letters by the Freiheitssatz.

Take a letter `s` of `W_0` of exponent sum 0 and rewrite `W_0` along it. This gives
`B_0 = V *_phi`, where:
- `V = <u_h : u != s, m_u <= h <= M_u | R>`;
- `phi(u_h) = u_(h+1)`, from `<u_h : h < M_u>` to `<u_h : h > m_u>`.

When `R` is primitive, `V` is free and the hierarchy stops: `V -> B_0 -> G` is a one-relator
hierarchy of length two ending in a free group, as in Linton's Example 6.12.

## 1. Top level: A cap B = <a_1>

`magint.decide` picks a letter `s` that lies in exactly one of `S = {a_0,a_1}` and
`T = {a_1,a_2}` and has exponent sum 0 in `W_0`:
- `s = a_0` when `e_(a_0) = 0`;
- otherwise `s = a_2`, with the roles of `A` and `B` swapped.

Let `M` be the Magnus subgroup that contains `s`, and `N` the other one. The decision has
five steps.

1. **Free vertex group.** Rewrite `W_0` along `s` with raw heights. This gives
   `B_0 = <V, s | s^-1 u_h s = u_(h+1)>`, where `u_h = s^h u s^-h` and `V` is as in §0.
   Whitehead minimisation with tracking finds `R` primitive, so `V` is free, and it records
   each `u_h` as a word in the free basis.
2. **The kernel part of `M`.** Let `K` be the kernel of the `s`-exponent map on `B_0`. Then
   `M cap K = <u_h : u in M \ {s}, h in Z>`.
   - `K` is the fundamental group of the line of groups with vertex groups `V_k = s^-k V s^k`.
   - Its edge groups are `E^+-` (the copies `u_h` with `h > m_u`, resp. `h < M_u`).
   - Put `Y = <u_h : u in M\{s}, m_u <= h <= M_u> <= V`, and `Y^+-` for its edge copies.
3. **The immersion test.** `magint` checks `Y cap E^+ = Y^+` and `Y cap E^- = Y^-` in free
   `V`, by Stallings pullback and graph equality (`sub_eq`).
   - When both hold, the line of groups with vertex groups `Y_k` maps to the line of `V_k`.
     This map is injective on vertex groups, and locally injective at each edge, because the
     sub-edge group equals the intersection of the vertex group with the edge group.
   - By Bass–Serre theory (an immersion of graphs of groups is `pi_1`-injective and preserves
     vertex stabilisers), `(M cap K) cap V_0 = Y`.
4. **`N` inside `V`.** `N` does not contain `s`. Its letters have raw-height ranges with a
   common height `h_0`, and then `s^h0 N s^-h0 = <u_h0 : u in N> <= V`.
   - `M` is normalised by `s`, so `M cap N` is conjugate to `M cap s^h0 N s^-h0`.
   - That group lies in `K cap V_0`, so it equals `Y cap <u_h0 : u in N>`.
5. **Pullback in free `V`.** `magint` computes `Y cap <u_h0 : u in N>` and compares it with
   `<(a_1)_h0>`.

All 32 relators end in `NONEXC` with rank 1 (`magint32.out`): the (D) relators through
`s = a_0` or `s = a_2`, and the 8 open ones through `s = a_0`. Hence `A cap B = <a_1>`, and the
intersection is not exceptional in Collins' sense.

**Calibration.** `calib_magint.out` covers two cases.
- `W_0 = [a_0,a_1][a_2,a_1]`. Here `[a_0,a_1] = [a_1,a_2]` lies in `A cap B` but not in
  `<a_1>`, and both sides report EXCEPTIONAL-CANDIDATE with rank 2.
- `W_0 = a_0 a_2 A_0 A_2 a_1`. Here `B_0 = F(a_0,a_2)` and `a_1 = a_2 a_0 a_2^-1 a_0^-1`, and the
  script reports NONEXC.

## 2. Top level: sZ(psi) = 2

Collins (Geom. Topol. Monogr. 14 (2008) 135–171), Theorem 2: "Let `G = <X : r = 1>`, where
`r` is cyclically reduced, be a one-relator group and let `M = F(S)`, `N = F(T)` be Magnus
subgroups of `G`, allowing `M = N`. For any `g in G`, either `gMg^-1 cap N` is cyclic
(possibly trivial) or `g in NM`." If `g = nm`, then `gMg^-1 cap N = n(M cap N)n^-1`.

Apply this in `B_0` with `(M, N) = (B, A)` and with `(A, B)`. Every `A cap hBh^-1` and every
`B cap hAh^-1` is then cyclic, since either it is cyclic directly or it is a conjugate of
`A cap B = <a_1>`.

In Linton's definition (p. 23, quoted in [[linton-z-stable-one-relator-hierarchy-theorem]]):
- the first class `[psi(A cap B_0)] = [B]` is non-cyclic;
- every class at the next step is cyclic.

So `sZ(psi) = sZ(psi^-1) = 2 < infinity`.

## 3. Level one: sZ(phi) finite

`level1.py` handles each letter `s` of `W_0` of exponent sum 0 in the same way.
- It builds `V` and the tracked free basis as in §1.
- It passes `(V, <u_h : h < M_u>, <u_h : h > m_u>, phi)` to `lintongraph.certify`, the landed
  Linton-graph script.
- That script enumerates the pure-direction stabiliser classes of Linton's definition by
  Stallings pullbacks. It returns `sZ(phi)` and `sZ(phi^-1)`, or a depth-cap failure.

Only the `sZ` values are used. The graph-of-cyclic-stabilisers verdict, which covers
BS-freeness through Theorem 6.14 and is certified only for rank 2 or less, is not used; §4
replaces it.

The results are in `level1_32.out`.
- **Each of the 32** has a letter with `V` free and finite `sZ`:
  - for the 24 (D): `s = a_0` or `a_1`, with `sZ` in `{(1,1), (2,2), (3,3)}`;
  - for the 8 open: `s = a_0`, with rank-3 edge groups and `sZ = (3,3)`. For these, `s = a_1`
    gives a non-free `V`, with Whitehead-minimal length 7.
- **Cross-check.** On the letter used by `mmcert19.out` (its `stable=y`, which is `a_1` here),
  the (D) values agree with the landed `mmcert` run.

## 4. Hyperbolicity, hence no Baumslag–Solitar subgroups

`kbhyp.sh` runs two kbmag (D. Holt) programs on `<a,t | w>`, with shortlex order on
`a, A, t, T`.
- `autgroup` runs `kbprog -wd`, `gpmakefsa` and `gpaxioms`. So a shortlex automatic structure
  is computed and its axioms are verified.
- `gpgeowa` then computes the geodesic word acceptor and the geodesic-pairs automaton. By the
  kbmag manual (`autgp.tex`, section `gpgeowa`), "if it succeeds, then the group has been
  proved to have this property", meaning word-hyperbolicity. The reason is Papasoglu,
  *Strongly geodesically automatic groups are hyperbolic*, Invent. Math. 121 (1995) 323–334.

`kbhyp32.out` reports `AUTOMATIC HYPERBOLIC` for 30 of the 32, with geodesic acceptors of
about 1200 states. `autgroup` stops at its equation cap on `AAtataTAtaTTattAATT` and on
`AAttAATTatAtaTataTT`. Both are `C'(1/6)` by
[[length19-singular-relators-small-cancellation-sofic]], hence hyperbolic by Gruber.

**Calibration** (`calib_kb.out`).
- `Z^2`: `autgroup` succeeds, and `gpgeowa` times out, as the manual predicts for a group
  that is not hyperbolic.
- `BS(2,3)` and Baumslag–Gersten: `autgroup` fails.

**No BS subgroups.** Suppose `BS(m,n) = <a, t | t a^m t^-1 = a^n>` embeds in a hyperbolic
group, with `m, n != 0`. Then `a` has infinite order, so its stable translation length is
`tau(a) > 0`. Conjugation invariance gives `|m| tau(a) = |n| tau(a)`, so `|m| = |n|`.

Inside `BS(m, +-m)`, the subgroup `<a^m, t>` (for `+`) or `<a^m, t^2>` (for `-`) is free
abelian of rank 2. Hyperbolic groups contain no `Z^2`.

Hence `G` has no Baumslag–Solitar subgroup, `Z^2 = BS(1,1)` included.

## 5. Conclusion

`V -> B_0 -> G` is a one-relator hierarchy (§0). It is Z-stable (§2 and §3), and `pi_1` has
no BS subgroup (§4). By Linton's Theorem 7.1, (3) implies (1): as quoted in
[[linton-z-stable-one-relator-hierarchy-theorem]], the hierarchy is quasi-convex, `G` is
hyperbolic, and `G` is virtually special.

A virtually compact special group is linear over `Z` (Haglund–Wise; as used in
`unit-alexander-singular-hidden-free-pieces-special-proof`). So `G` is residually finite,
hence sofic. ∎

## 6. Trust

- **§1 and §3.** Exact combinatorial group theory (Whitehead, Stallings) in Python, reusing
  the landed `whitehead.py` and `lintongraph.py`.
- **§4.** Rests on kbmag's correctness. `gpaxioms` checks the automatic structure, but the
  run is not independently reproduced.
- **§2 and §5.** Cited theorems, with the hypotheses checked above.
- **Not checked.** Whether Linton's definition of one-relator hierarchy allows the hierarchy
  to stop at a primitive relator after two steps. This is the same shape as the landed
  length-one certificates, which stop at a free vertex group.
