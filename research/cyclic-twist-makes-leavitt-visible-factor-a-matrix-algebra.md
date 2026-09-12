---
rg: 2
id: cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
kind: claim
title: A diagonal unit twisting an m-cycle by a root of unity makes the Leavitt-visible factor an m by m matrix algebra over the cyclic corner
distinct_from:
  ternary-leavitt-swap-problem-splits-at-central-involution: that is the instance q = 3 and d = m = 2, with delta = s0 t0 - s1 t1 twisting the swap; this is the construction for every prime power q, arity d and cycle length m with m = 1 mod (d - 1), p not dividing m and m dividing q - 1, including characteristic two over F_4.
  leavitt-corner-idempotent-unital-surjection: that is the binary corner of the order-three unit uv, whose averaging idempotent evaluates to zero in R; this uses the permutation unit of an m-ary Leavitt family, whose averaging idempotent evaluates to a corner equivalent to 1.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Let `q = p^r`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`, and `A_iota` the Leavitt-visible factor of
`F_q[G]` (`leavitt-unit-group-algebras-split-over-scalar-characters`). Let `m = 1 + j(d-1)` with
`j >= 1` and `p` not dividing `m`, and let `s_i, t_i` be an `m`-ary Leavitt family in `L`.

1. **Image solution on every host.** `g = sum_i s_(i+1) t_i` is a unit of order `m`. With
   `e_H = eps_iota (1/m) sum_k [g^k]`, `b = sum_i s_i` and `c = (1/m) sum_i t_i`, the evaluation gives
   `c . pi(e_H) . b = 1` in `L`. Admissible `m` prime to `p` exist for every `(q, d)`.
2. **Matrix structure when `m` divides `q - 1`.** Let `zeta` in `F_q^x` have order `m`, and
   `delta = sum_i zeta^i s_i t_i`. Then `delta g delta^(-1) = zeta g`. Conjugation by `[delta]`
   permutes the `m` isotypic idempotents of `<g>` in `A_iota` cyclically, so
   `A_iota ~= M_m(T)` with `T = e_H A_iota e_H`. In particular `A_iota` has no unital homomorphism to a
   nonzero commutative ring.
3. **Cohn form.** `c' e_H b' = eps_iota` is solvable in `A_iota` iff `T` contains a unital `m`-pair
   Cohn family `gamma_i beta_j = delta_ij e_H`.

**Instances.**
- `(q, d, m) = (3, 2, 2)`: this is the ternary split, with `g = w` and `delta = s0 t0 - s1 t1`.
- `(4, 2, 3)`: the characteristic-two analogue on `L_(F_4)(1,2)^x`, which contains the binary unit group.

Over `F_2` itself there is no twist: there are no nontrivial scalars, and the augmentation is visible.

ESTABLISHED by `leavitt-cyclic-twist-matrix-structure-proof` (Sections 2 and 3 of the artifact).
