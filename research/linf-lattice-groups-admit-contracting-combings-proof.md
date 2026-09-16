---
rg: 2
id: linf-lattice-groups-admit-contracting-combings-proof
kind: route
title: Clamp the translation part coordinatewise at radius m, and step back by clamping at radius m minus C/2
target: linf-lattice-groups-admit-contracting-combings
requires: []
artifacts:
  - research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md
---

Complete proof: artifact Sections 2 and 3 (Lemma 2, Theorem 3). Condensed here.

Notation: `‖·‖ = ‖·‖_∞`, `c = ⌊C/2⌋`, `κ_r(v)_i = max(−r, min(r, v_i))`.

**Lemma (clamp inequality).** Let `x, y ∈ Z`, `r' <= r` and `0 <= c <= min(r, C)`. If
`|κ_r(x) − κ_{r'}(y)| <= C`, then `|κ_{r−c}(x) − κ_{r'}(y)| <= C`.

*Proof.* Put `a = κ_r(x)`, `b = κ_{r'}(y)`, `a' = κ_{r−c}(x) = κ_{r−c}(a)`; note
`|b| <= r' <= r`.
- If `|a| <= r − c`, then `a' = a`.
- If `a > r − c`, then `a' = r − c`.
  - When `b <= r − c`: `0 <= a' − b < a − b <= C`.
  - When `b > r − c`: `0 < b − a' <= r − (r − c) = c <= C`.
- The case `a < −(r − c)` is symmetric. ∎

**Proof of (a).** `t_g = g(0)`, `t_{gh} = t_g + A_g t_h`, and
`t_{g^-1 h} = A_g^-1 (t_h − t_g)`. Since signed permutations preserve `‖·‖`:
- `t_g = t_{g'}` iff `g^-1 g'` fixes `0`, so each fibre of `g ↦ t_g` is a coset of the
  finite stabilizer, and `S` is finite. `‖t_{g^-1}‖ = ‖t_g‖`, so `S` is symmetric.
- If `k = s_1 ⋯ s_L` with `s_i ∈ S`, then `t_k = Σ_i A_{s_1⋯s_{i−1}} t_{s_i}`, so
  `‖t_k‖ <= L`.
- Conversely let `k ≠ 1` and `L = ‖t_k‖`. If `L = 0`, then `k ∈ S`. If `L >= 1`, use
  transitivity to pick `g_i` with `t_{g_i} = κ_i(t_k)`, `g_0 = 1`, `g_L = k`. Then
  `t_{g_{i−1}^-1 g_i} = A_{g_{i−1}}^-1 (κ_i(t_k) − κ_{i−1}(t_k))` has norm at most
  `1`, so `g_{i−1}^-1 g_i ∈ S ∪ {1}`, and `|k| <= L`.
- So `|k| = max(‖t_k‖, 1)` for `k ≠ 1`, `S` generates, and
  `d(g, h) = |g^-1 h| = max(‖t_h − t_g‖, 1)` for `g ≠ h`. ∎

**Proof of (b).** In every case `t_{s(g)(m)} = κ_m(t_g)`.
- *Combing.* `κ_m(t_g)` and `κ_{m+1}(t_g)` differ by at most `1` in norm, so by (a)
  consecutive values are at distance at most `1`. The path starts at `1` and is
  constant equal to `g` from time `max(‖t_g‖, 1)` on, which is `|g|` for `g ≠ 1`. So
  it is geodesic.
- *Contracting.* Let `C >= 2`, `n' <= n`, `c <= n`, and
  `d(s(g)(n), s(h)(n')) <= C`. By (a), `‖t‖` of a difference is at most `d`, so
  `‖κ_n(t_g) − κ_{n'}(t_h)‖ <= C`. Since `c <= min(n, C)`, the lemma applied
  coordinatewise gives `‖κ_{n−c}(t_g) − κ_{n'}(t_h)‖ <= C`. By (a),
  `d(s(g)(n − c), s(h)(n')) <= max(C, 1) = C`. ∎

**Examples.** Each is checked against the hypotheses in artifact Section 3.
- `Z^n ⋊_ρ F` acts by `(v, f) : w ↦ ρ(f) w + v`, with stabilizer `F`.
- The Klein bottle group `(m, k)(m', k') = (m + (−1)^k m', k + k')` acts simply
  transitively by `(x, y) ↦ ((−1)^k x + m, y + k)`.
- The screw group `{(a, b, k)}` acts simply transitively by `v ↦ R^k v + (a, b, k)`.

**Numerical check.** Evidence only:
`experiments/zaremsky-4-01-contracting-combings-2026-09-16/check_combings.py`,
Parts 1 and 2.
- The lemma was checked exhaustively on a box, with 0 failures in 762300 cases.
- The metric formula and the contracting condition were checked for `C = 2..5` on
  balls in `Z^2`, `Z^2 × Z/3`, `Z^2 ⋊ B_2`, the Klein bottle group and the screw group.
