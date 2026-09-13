---
rg: 2
id: two-piece-left-inverses-are-corner-left-inverses
kind: claim
title: A combination u0 P + u1 (1-P) of two units has a left inverse exactly when the compressed transition (1-P) u0^(-1) u1 (1-P) has one in its corner
distinct_from:
  two-piece-s0-lifts-telescope-to-a-corner: that fixes the partner built from the inverse units and asks when the product is a unit, through C'C over F_2; this asks for any left inverse, in any ring, and needs only the single compressed element P'hP' to be left invertible in the corner
artifacts:
  - research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md
---

**ESTABLISHED** (proof: artifact Section 2, route `two-piece-left-inverses-are-corner-left-inverses-proof`).
Re-derivation requested from `w4-vf-linear-b`.

Let `S` be a unital ring, `P` an idempotent, `P' = 1 - P`, `u0, u1` units, `h = u0^(-1) u1`, and
`a = u0 P + u1 P'`. Then `a` has a left inverse in `S` iff some `v in P'SP'` satisfies `v · P'hP' = P'`.
Explicitly:
- if `v h P' = P'` with `v in P'SP'`, then `c = (P + v - P h v) u0^(-1)` satisfies `c a = 1`;
- if `c a = 1`, then `v = P' c u0 P'` works.

**Use for lifts of s0** (artifact Corollary A.1). Take `S_- = eps_- F_3[L_(F_3)(1,2)^x]`, `P = P_(d0)` and
`P' = P_(d1)`, the honest idempotents of the involution `d1 = 1 + s1 t1`, and suppose `u0 s0 = s00` and
`u1 s1 = s01`.
- **The lift.** `pi(a) = s0`, and `a = -[u0] - [u0 d1] - [u1] + [u1 d1]` has four terms.
- **The reduction.** A left inverse of the single corner element `Y_h = P_(d1)[h]P_(d1)` makes `a` a
  one-sided unit that is not invertible, so `J_1(S_-) != 0` in
  `weakly-finite-reflection-ideal-detects-weakly-finite-images`.
- **Solving in the corner.** The corner is spanned by the `Y_g`, with `Y_g Y_k = Y_(g d1 k) - Y_(gk)`
  (artifact Proposition B). So the corner condition is one linear equation.

**Firewall** (artifact Proposition D). A left inverse of `Y_h` cannot use only group elements from a subgroup
`H` with `z, d1, h in H` and `F_3[H]` directly finite. For instance `H` locally residually finite, where a
direct proof is given, or `H` sofic.
