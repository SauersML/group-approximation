---
rg: 2
id: h4-case1-vertex-centres-fail-by-orthogonal-parabolics-proof
kind: route
title: Three conjugates of A_{s_4}, each orthogonal to a conjugate of A_{s_1s_2} containing a, b or b^{-1}a, give a Case 1 tuple whose cosets meet off the vertices; exact normal forms certify the inequalities
target: h4-case1-vertex-centres-fail-by-orthogonal-parabolics
requires:
  - h4-case1-commutator-helly-holds-in-type-a-but-vc-fails
  - h4-case1-helly-is-a-commutator-double-coset-problem
  - h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple
artifacts:
  - experiments/h4-helly-2026-09-19/vc1.py
  - experiments/h4-helly-2026-09-19/vc2.py
  - experiments/h4-helly-2026-09-19/burau.py
  - experiments/h4-helly-2026-09-19/nlen.py
  - experiments/h4-helly-2026-09-19/nlen_H4.log
  - experiments/h4-helly-2026-09-19/roots.py
  - experiments/h4-helly-2026-09-19/modular.py
---

Notation is as in the target. Generators are numbered `1..4 = s_1..s_4`, and a negative number is an inverse.

**Membership.**
- `a = p_2p_3 = s_1s_2^2s_1` and `b = p_1p_3` lie in `P_Y`, and `ρ_X` sends them to 1. So `a, b ∈ F`, and
  `a ≠ b`.
- `c, d, w` are conjugates of `s_4^2` by elements of `A_{s_2s_3}`. So they lie in `P_X`.
- `ρ_Y` kills `s_4^2`, since it is a pure generator not in `P_Y`. Hence `c, d, w ∈ N`.

**Part 1 (structure; uses only `m_{s_1s_4} = m_{s_2s_4} = 2`).**
- **`[c,a] = 1`.** `s_4` commutes with `s_1` and `s_2`, and `a ∈ A_{s_1s_2}`.
- **`b = s_3^{-1}as_3`.** Both `p_1p_3` and `s_3^{-1}p_2p_3s_3` equal `s_1s_2s_3^2s_2^{-1}s_1`, since `s_3`
  commutes with `s_1`. This is checked in `vc1.py`.
- **`[d,b] = 1`.** It is the `s_3^{-1}`-conjugate of `[c,a] = 1`.
- **`[w, b^{-1}a] = 1`.** By `vc2.py`, `g := (s_2s_3)^{-1}b^{-1}a(s_2s_3)` equals `Δ_{12}^{-2}s_1^2s_2^2s_1^2`, with
  `Δ_{12} = s_1s_2s_1`. This element lies in `A_{s_1s_2}`, so it commutes with `s_4^2`.
  Conjugating by `s_2s_3` gives `[w, b^{-1}a] = 1`.
  - The identity is checked in the H_4 and A_4 Garside normal forms. It involves only `s_1, s_2, s_3`, so it holds
    in `A_{A_3}` and hence for every `m`.
- **The commutators.** By (Q.2) of w14, `[w,a] = [w,b] =: k`. Then:
  - `[u,a] = [wc,a] = w[c,a]w^{-1}·[w,a] = k`;
  - `[v,b] = w[d,b]w^{-1}·[w,b] = k`.
  So `w ∈ U_a(k) ∩ U_b(k)`, and by (Q.1) `u ∈ U_a(k)` and `v ∈ U_b(k)`.

**Part 2 (certificates).**
- `vc1.py H4|B4|A4` computes Garside normal forms (Charney normal form in the spherical Artin group, which solves the
  word problem exactly) of:
  - `k`;
  - `[u,b]k^{-1}` and `[v,a]k^{-1}`;
  - `[c,b]` and `[d,a]`.
- None of them is the identity, for `m = 3, 4, 5`. The same run re-checks every equality of Part 1.
- `burau.py` repeats the inequalities in an exact linear representation over `ℚ(√5)` at `t = 2`:
  - `s_i e_i = -te_i`, and `s_ie_j = e_j + a_{ij}e_i` for `i ≠ j` adjacent;
  - `a_{ij} = 1` for `i < j`, and `a_{ji} = t(2 + 2cos(2π/m_{ij}))`;
  - the script first verifies the braid relations.
- Inequality of images implies inequality in the group, so this is an independent certificate. All outputs are True.

**Part 3.**
- VC fails by Part 2.
- By (Q.4) of w14, a failure at `(wc, wd)` is the same as `c ∈ C_N(a)∖C_N(b)` and `d ∈ C_N(b)∖C_N(a)`. So the
  centralisers are incomparable, which Part 2 shows directly.
- `u^{-1}v = c^{-1}w^{-1}wd = c^{-1}d` with `c^{-1} ∈ C_N(a)` and `d ∈ C_N(b)`. This is (H″) for the tuple.
  By (K) of `h4-case1-helly-is-a-commutator-double-coset-problem` and
  `h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple`, the corresponding hexagon has a pure centre.
  The centre is given by the common point `w`, which is not one of `u, v, 1`.

**Part 4.**
- `nlen.py H4 3` builds the ball of radius 3 in the 12 meridian generators of `N`: 13273 elements, the letters of
  w14's `dumpgen.py`. It finds no factorisation `d = gh^{-1}` with both factors in the ball, so the N-length of `d`
  is greater than 6 (`nlen_H4.log`).
- The same script gives length at most 5 in B_4 and at most 3 in A_4.
- So `v = wd` has N-length at least 5 in H_4. The tuple lies outside the radius-(3,4) search of w14, which is why
  that search found no VC failure.

**Aside (supporting, not used above).** `modular.py` with `roots.py` checks the line `L` fixed by `W_X`:
- It counts pairs `H, H'` of reflection hyperplanes not containing `L` such that no hyperplane containing `L` (an
  X-wall) contains `H ∩ H'`.
- There are 510 such pairs in H_4, 1167 in the reversed orientation, and 0 in A_4 and B_4.
- So `L` is not modular in H_4 (the corank-1 modularity criterion), and `ρ_X` is not a fibre-type projection.
- Hence the free-fibre arc model behind the type-A proof of (H″) has no direct H_4 analogue. This is why a
  non-vertex H_4 Helly argument cannot simply be transported from `braid-pure-single-edge-hexagons-always-have-a-centre`.
