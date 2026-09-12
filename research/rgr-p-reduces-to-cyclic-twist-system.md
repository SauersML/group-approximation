---
rg: 2
id: rgr-p-reduces-to-cyclic-twist-system
kind: claim
title: RGR_p reduces, up to one further amplification, to a cyclic scalar system in |e| matrix unknowns
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
  - research/artifacts/gk-vf-linear-b-verification-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `rgr-p-cyclic-twist-system-proof`, in the corrected form below. Verified by
`w4-vf-linear-b` (Section 30.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`).

Fix `Fbar` algebraically closed of characteristic `p`, and a word `w(t) = c_0 t^(e_1) c_1 ... t^(e_l) c_l`
with `c_i in GL_d(Fbar)` and `e = e_1 + ... + e_l != 0`.

**Statement.**
- **Setup.** Amplify by `k = |e|`. On `W = W_0 (+) ... (+) W_(|e|-1)`, with each `W_j = Fbar^d`, let `t` be the
  twisted cyclic shift `t|_(W_j) = b_j : W_j -> W_(j+1 mod |e|)`, with `b_j in GL_d`.
- **Block-diagonality.** `w(t)` is block-diagonal, and
  `rank(w(t) - lambda 1_(d|e|)) = sum_(m=0)^(|e|-1) rank(P_m - lambda 1_d)`, where

```text
P_m = c_0 . B_1(m) . c_1 . ... . B_l(m) . c_l,
```

  and `B_i(m)` is the ordered product of the twists met by the `i`-th syllable, started at block `m`.
- **The cyclic system.** A solution of the following system is an RGR_p witness at this amplification: choose
  `b_0, ..., b_(|e|-1) in GL_d` and `lambda` making the `|e|` cyclic products `P_m` simultaneously scalar, up to
  total rank `eps d|e|`.
- **Coupling.** For a positive word each `B_i(m)` is a free element of `GL_d`. The equations are coupled only
  through the cyclic reuse of the `b_j`.

**No loss, up to one further amplification.**
- Let `t in GL_(dk)(Fbar)` be an RGR_p witness at amplification `k`, and `S` the cyclic permutation matrix of `|e|`
  blocks.
- Then `t~ = t (x) S` is a twisted cyclic shift with every twist equal to `t`. Its coefficients are
  `c_i (x) 1_k (x) 1_(|e|)`, so `w(t~) = w(t) (x) S^e = w(t) (x) 1`, with the same normalized error.
- So RGR_p holds for the word iff, for every `eps`, some amplification `c_i (x) 1_k` of the coefficients admits an
  `eps`-solution of the cyclic system.

**Correction (w4-vf-linear-b, 2026-09-12).** An earlier version titled this claim "RGR_p at amplification by
the total exponent is exactly a cyclic scalar system", said "any RGR_p witness at amplification `e` has this
block form", and amplified by `k = e`. That is false as written.
- A general `t in GL_(de)` is not a twisted cyclic shift. For `c_0 t c_1 t c_2`, a block-diagonal `t = diag(u, u)`
  with `u c_1 u = c_0^(-1) lambda c_2^(-1)` is a witness at amplification 2 but not a shift.
- The corrected equivalence is the one in "No loss" above.

## Attempts

- The `e` rotations are **not** mutually conjugate, because the fixed `c_i` do not rotate with the
  starting block. The coefficient-free conjugacy collapse does not apply.
- Rank slack over the `e` blocks lets one drop a fixed number of blocks, not an `eps`-fraction growing
  with amplification, because block-diagonality pins the cycle length to `e`.
