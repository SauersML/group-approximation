---
rg: 2
id: h4-case1-commutator-helly-holds-in-type-a-but-vc-fails
kind: claim
title: The commutator Helly property (H″) holds in every type A_n, yet vertex centres fail already in A_4, so VC cannot be the route to Case 1 in general; H_4 balls show no failure of either
distinct_from:
  h4-case1-helly-is-a-commutator-double-coset-problem: that reduces Case 1 to (H″) and states it for H_4; this proves the coset and nesting structure of the solution sets, proves (H″) in type A_n, and refutes the vertex-centre form VC in type A_4 with an exact certificate.
  h4-fibred-braid-shadows-cannot-certify-case1-counterexamples: that shows the braid images of H_4 hexagons always have centres; this is about type A_n itself, shows (H″) there, and finds that those centres can fail to be vertices, which gives a way to refute VC in H_4 by lifting.
  braid-pure-single-edge-hexagons-always-have-a-centre: that proves the centres exist in the arc model; this translates it into (H″) through the commutator dictionary and shows that the centres it gives are in general not hexagon vertices.
---

**Setting.** Notation is as in `h4-case1-helly-is-a-commutator-double-coset-problem`.
- `P` is the pure Artin group, `X = S∖{s_1}`, `Y = S∖{s_n}`, and `ρ_X, ρ_Y` are the parabolic retractions.
- `F = ker(ρ_X|P_Y)` and `N = ker(ρ_Y|P_X)`.
- `[x, y] = xyx^{-1}y^{-1}`, and `C_N(g)` is the centraliser of `g` in `N`.
- For `a ∈ F` and `k ∈ P`, put `U_a(k) = {u ∈ N : [u, a] = k}` and `τ_a : N → P, u ↦ [u, a]`.

Recall:
- (H″) says that for `a ≠ b` in `F` and `u, v ∈ N`, `[u, a] = [v, b]` implies `u^{-1}v ∈ C_N(a)C_N(b)`.
- By (K) of the cited node, (H″) is Case 1 of the target.
- VC fails for the tuple `(a, b, u, v)` iff `k = [u, a] ≠ 1`, `[u, b] ≠ k` and `[v, a] ≠ k`.

**Theorem.**

**(Q) Coset and nesting structure** (any type).
1. Each `U_a(k)` is empty or a single left coset `uC_N(a)`.
2. `[w, a] = [w, b]` iff `w ∈ C_N(b^{-1}a)`.
3. For fixed `(a, b, k)` with `U_a(k), U_b(k)` nonempty:
   - (H″) holds iff `U_a(k) ∩ U_b(k) ≠ ∅`;
   - equivalently, over all `k`, iff `τ_a(N) ∩ τ_b(N) = τ_a(C_N(b^{-1}a))`.
4. Let `k ≠ 1` and suppose `w ∈ U_a(k) ∩ U_b(k)`. Then VC holds for every `(u, v) ∈ U_a(k) × U_b(k)` iff
   `C_N(a) ⊆ C_N(b)` or `C_N(b) ⊆ C_N(a)`.
   - Explicitly, VC fails at `(u, v) = (wc, wd)` iff `c ∈ C_N(a)∖C_N(b)` and `d ∈ C_N(b)∖C_N(a)`.
   - So VC can fail only through incomparable centralisers. Where the centralisers are nested (for instance, where
     they are trivial), (H″) and VC are the same statement.

**(A) (H″) holds in type `A_n` for every `n ≥ 2`,** and so does (H) for every Case 1 tuple.
- Under the diagram flip `s_i ↦ s_{n+1-i}`, `(X, Y)` becomes the `k = 1` arc and spider model of
  `braid-pure-single-edge-hexagons-always-have-a-centre` in `B_{n+1}`.
- Part 3 of that node then gives a pure `A_Y`-centre for every Case 1 hexagon.

**(B) VC is false in type `A_4`** (certified by exact computation). In `B_5`, with Artin generators `σ_i`, put
- `p_0 = σ_1^2`, `p_1 = σ_1σ_2^2σ_1^{-1}` and `p_2 = σ_1σ_2σ_3^2σ_2^{-1}σ_1^{-1}`, which lie in `F`;
- `x_0 = σ_4^2`, `x_1 = σ_3σ_4^2σ_3^{-1}` and `x_2 = σ_2σ_3σ_4^2σ_3^{-1}σ_2^{-1}`, which lie in `N`;
- `a = p_1p_0`, `b = p_2p_0`, `w = x_2`, `c = x_0` and `d = x_0x_1x_0^{-1}`.

Then:
- `c ∈ C_N(a)∖C_N(b)` and `d ∈ C_N(b)∖C_N(a)`;
- `[w, a] = [w, b] = k ≠ 1`.

So `u = wc = x_2x_0` and `v = wd = x_2x_0x_1x_0^{-1}` give `[u, a] = [v, b] = k`, `[u, b] ≠ k` and `[v, a] ≠ k`.

Take the Case 1 tuple `α_1 = a^{-1}`, `α_2 = b`, `β_3 = u` and `β_1 = u^{-1}v = x_0x_1x_0^{-1}`. Then:
- it satisfies `(*)` and `α_1α_2 ≠ 1`;
- none of its three hexagon vertices is a pure centre;
- a pure bound still exists, as (A) says: it is `γA_Y` with `γ = u^{-1}w = x_0^{-1}`.

This is a shortest failure over `F`-words of length ≤ 2 and `N`-words of length ≤ 3, with total letter length 9
(`a, b, w, c, d`).
- These balls contain 8 failing pairs `{a, b}`.
- The four of length 9 are the sign variants `{p_1^{±1}p_0, p_2^{±1}p_0}`.
- The other four have length 11.

**(C) Searches.** Exact hash-class searches (`cchelly`, Garside normal forms, no hash collisions) over F-balls of
radius `LA` and N-balls of radius `LB`:

| type | LA | LB | tuples | VC failures | failures without a ball centre (HCAND) |
|---|---|---|---|---|---|
| A_3, B_3, H_3 and reversed | 3 | 5 | 910–4680 each | 0 | 0 |
| A_4 | 3 | 6 | 1300624 | 18720 | 160 |
| B_4 | 3 | 5 | 1867004 | 0 | 0 |
| H_4 | 2 | 4 | 155476 | 0 | 0 |
| H_4 | 3 | 4 | 954436 | 0 | 0 |
| H_4 reversed (`m_{s_1s_2} = 5`) | 2 | 4 | 111840 | 2688 | 0 |

Two facts about the A_4 row:
- the Artin-representation check `artinverify.py` independently confirms the commutator identity on all 210 printed
  lines, and the VC failure on 174 of them (the printed `u, v` are sample coset representatives, not always a
  failing pair);
- the 160 HCAND classes are false alarms by (A), since their centres lie outside the N-ball.

The H_4 rows use the orientation of the target (`m_{s_3s_4} = 5`, so `Y` is of type `A_3`). In the reversed
orientation, which the target does not cover and where the Coxeter-level check of the target already fails, VC fails
at the first radius tried, for example at `{a, b} = {p_5^{-1}p_0, p_5^{-1}p_2}`. All 2688 of those failures have a common
point of `U_a ∩ U_b` inside the ball (HBALL), so (H″) holds for every one of them.

Hence a ball search can confirm instances of (H″) but can never refute it. A refutation needs an argument about all
of `N`, for instance a finite quotient in which the images of the cosets `U_a(k)` and `U_b(k)` are disjoint.

**Consequences for Case 1 of the target.**
- No uniform proof of Case 1 can produce the centre as a hexagon vertex, since that fails in type A_4.
- A type-free proof must reach the non-vertex centres, as the Z/2 Helly argument does in the arc model.
- **(L) A lifting test for VC in H_4.** A type-preserving simplicial map of layers sends hexagon vertices to
  hexagon vertices and preserves adjacency, so it sends a vertex centre to a vertex centre. Hence if a fibred braid
  shadow `ρ_V : P ↠ P_5` of `h4-fibred-braid-shadows-cannot-certify-case1-counterexamples` maps an H_4 Case 1
  hexagon onto a `P_5`-translate of the flipped A_4 hexagon of (B), then VC fails in H_4.
- In H_4, in the target orientation, no VC failure occurs in the balls searched (187 `F`-elements, 305265 `N`-elements). By (Q.4), VC and
  (H″) agree for H_4 pairs whose centralisers are nested. The ball data show only small centralisers: `x_0` commutes with `p_2, p_3`, and `x_4,…,x_11` commute with
  nothing in the F-ball of radius 2.
