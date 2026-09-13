---
rg: 2
id: toeplitz-defect-ideal-almost-commuting-projection-axiom
kind: claim
title: Every unitary of 1 + J almost commutes, within norm 1, with a properly infinite full projection of J + T_2 with properly infinite full complement
---

Notation as in `toeplitz-defect-ideal-unitization-k1-injective`: `A_T = T_2 * T_2`, `e = iota_1(p_3)`,
`J = <e>`, `B_J = J + iota_1(T_2)`.

For every `u ∈ U(1 + J)` there is a projection `p ∈ B_J` such that `p` and `1 − p` are properly
infinite and full in `B_J`, and `||up − pu|| < 1`.

By route `toeplitz-defect-ideal-connected-via-almost-commuting-projection`, this implies that `U(J~)` is
connected. With the halving homotopy it implies STW Problem LXI. No converse is known: a null unitary
need not admit such a projection.

Constraints any witness must meet:
- `[u, p] ∈ J` always, because `u − 1 ∈ J`.
- For every unital quotient `π: B_J -> D` with `π(J) = D`, both `π(p)` and `1 − π(p)` are nonzero, by
  fullness. The O_3 quotient of `toeplitz-defect-ideal-absorbers-have-nonfull-complement` is one such π.

## Attempts

- **Absorbing projections: dead.** `toeplitz-defect-ideal-absorbers-have-nonfull-complement` kills
  route `toeplitz-defect-ideal-connected-via-absorbing-projections`. A `p` that contains the support of
  `u − 1` is pushed to 1 in the O_3 quotient, so `p` must genuinely cut the support.
  - Escape, not yet tried: first multiply `u` by a null lift of `π(u)^*`, then work in
    `1 + (J ∩ ker π)`. This has to be done for all unital quotients of `J` at once.
- **Projections from `iota_1(T_2)` alone: no uniform choice.**
  - Let `g ∈ iota_1(T_2)` be a projection other than 0 and 1, and `x = iota_2(s_1)e`. Represent `iota_1`
    on Fock space with vacuum Ω, and let `iota_2(s_1)` be an isometry with `iota_2(s_1)Ω = ξ` and
    infinite corank.
  - With `c = <gΩ, Ω>`, `[g, x]Ω = gξ − cξ`. Taking ξ in the range of `g`, or of `1 − g`, gives
    `||[g, x]|| ≥ max(c, 1 − c) ≥ 1/2` in `A_T`.
  - So a projection commuting approximately with the defect-generated elements needs `J`-components
    adapted to `u`. The `stw61-*` maximal-commutator theorems make the same point for explicit mixed
    families.
- **Unit axiom form.** By `defect-ideal-connected-iff-one-isometry-unit-axiom`, connectivity of `U(J~)`
  is exactly `u ~_h 1 + SxS^*` for `S = iota_1(s_2)`, with no halving hypothesis.
  - `C_S(u)` commutes exactly with `SS^*`, a properly infinite full projection whose complement is
    properly infinite and full.
  - So connectivity is equivalent to "every `u` is homotopic in `U(J~)` to a unitary that commutes with
    such a projection". This claim asks for `u` itself, up to a commutator of norm < 1.
- **Blocked, per lane ex2-k1-defect-ideal:** commutator criteria in explicit families, strict isometry
  paths (blocked by the O_3 quotient, where no norm path of isometries joins 1 to `r_2`), and
  stable-ideal shortcuts (`J` is not stable).
