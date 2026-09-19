---
rg: 2
id: h4-case1-helly-is-a-commutator-double-coset-problem
kind: claim
title: Case 1 pure bounds of the H_4 hexagon are the solutions of one commutator equation in N, and the Helly property (H) is the double-coset statement β_1 ∈ C_N(α_1)C_N(α_2)
distinct_from:
  h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple: that reduces pure bounds to "some P_X-conjugate γFγ^{-1} contains the corners"; this solves that membership problem exactly (conjugation by N fixes every element it keeps in P_Y), turning (H) into a centraliser double-coset condition and a commutator equation, and settles the diagonal pairs.
---

**Setting.** Notation is as in `h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple`.
- `ρ_X, ρ_Y` are the parabolic retractions of the pure H_4 Artin group `P`, and `F = ker(ρ_X|P_Y) ≅ F_3`.
- `N = ker(ρ_Y|P_X)`, so `P_X = N ⋊ P_Z`.
- A Case 1 tuple is `α_1, α_2 ∈ F` and `β_1, β_3 ∈ N` with `α_1α_2 ≠ 1` and
  `(*)  β_3^{-1}(α_1α_2)β_3 = α_1β_1α_2β_1^{-1}`.
- `C_N(g)` is the centraliser of `g` in `N`, and `[x, y] = xyx^{-1}y^{-1}`.

**Theorem.**

**(R) Rigidity.** If `γ ∈ N`, `g ∈ P_Y` and `γgγ^{-1} ∈ P_Y`, then `γgγ^{-1} = g`. Hence, for `γ ∈ N`,
`F ∩ γFγ^{-1} = C_F(γ)` and `F ∩ γ^{-1}Fγ = C_F(γ)`.

**(H′) Exact form of the pure bounds.** For a Case 1 tuple, the pure `ŝ_4` upper bounds are exactly the cosets `γA_Y` with
`γ ∈ C_N(α_1) ∩ β_1C_N(α_2)`.
So (H) holds for the tuple iff `β_1 ∈ C_N(α_1)·C_N(α_2)`.

**(K) Commutator form.** Put `a = α_1^{-1}`, `b = α_2`, `u = β_3` and `v = β_3β_1`. Then:
- `(*)` holds iff `[u, a] = [v, b]`. Call this common value `k`. It lies in `ker ρ_X ∩ ker ρ_Y`.
- The pure bounds correspond one-to-one to the `w ∈ N` with `[w, a] = [w, b] = k`, via `γ = u^{-1}w`.
- The three hexagon vertices correspond to the three free choices of `w`:

  | `w` | `γ` | vertex | condition |
  |---|---|---|---|
  | `1` | `β_3^{-1}` | `y_3` | `k = 1` |
  | `u` | `1` | `y_1` | `[u, b] = k` |
  | `v` | `β_1` | `y_2` | `[v, a] = k` |

  So VC fails iff `k ≠ 1`, `[u, b] ≠ k` and `[v, a] ≠ k`.

**(D) Diagonal pairs.** If `α_1 = α_2`, then (H) holds iff VC holds iff `β_1 ∈ C_N(α_1)`. The vertex `y_2` is then a pure centre.

**Computation (exact, certified per hit).** `chelly.py` hashes `u ↦ [u, f]` over a ball of `N`, once for each `f` in a
ball of `F`. It then reads off every Case 1 tuple of the box as a coincidence between the hash classes of `a` and of
`b`, and re-verifies each one in Garside normal form.
- **Box.** `u, v` range over the 13273 elements of `N` of length ≤ 3 in the 12 meridians. The pairs `(α_1, α_2)` range
  over all ordered pairs of `F`-elements of length ≤ `LA` with `α_1α_2 ≠ 1`.
- **Result.** With `LA = 2` the box has 32548 genuine tuples with `k ≠ 1`. The search found **0** VC-failures among
  them, so **0** HCAND. The per-box counts are in the proof.
- **Diagonal pairs.** This covers the two diagonal pairs `α_1 = α_2 = p_i^{±1}` that the w12 `vsearch3` could not
  finish.
- **Selftest.** An independent test of (R) against the `fmem.in_F` membership test gave 0 violations on 2400 pairs.
