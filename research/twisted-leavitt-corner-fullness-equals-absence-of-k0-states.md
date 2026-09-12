---
rg: 2
id: twisted-leavitt-corner-fullness-equals-absence-of-k0-states
kind: claim
title: A twisted Leavitt-visible corner is full exactly when the factor fails the rank condition, exactly when its K_0 admits no state
distinct_from:
  ternary-anti-central-summand-has-cohn-family: that is the open request for a two-pair Cohn family in the ternary anti-central summand, with its equivalence to the swap corner; this is the established equivalence, on every twisted Leavitt-visible factor, between corner fullness, failure of the rank condition at any matrix size, nonpositivity of the unit class, and absence of states.
  anti-central-state-obstruction-equals-stable-finiteness: that proves on the ternary summand that a corner solution forbids states, and that states exist iff the unit class is not nonpositive; this adds the converse, that nonpositivity, and even failure of the rank condition at any size, gives back the corner, for every twisted host.
  cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra: that establishes the matrix structure and the Cohn form of the corner; this uses that structure, together with the diagonal endomorphism, to show that stabilization adds nothing.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

**ESTABLISHED.**

**Setting.**
- The host: `q = p^r`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`.
- The factor: `A = A_iota`, the Leavitt-visible factor of `F_q[G]`, with unit `eps_iota`.
- The twist: `m = 1 + j(d-1) >= 2` with `p` not dividing `m` and `m | q - 1`, with `g`, `e_H` and
  `T = e_H A e_H` as in `cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`.
- Put `u = [eps_iota]`.

The following are equivalent.

1. `c' e_H b' = eps_iota` is solvable in `A`.
2. `A^2` is isomorphic to a direct summand of `A`: a unital two-pair Cohn family in `A`.
3. `A` fails the rank condition: `A^(n+1)` is isomorphic to a direct summand of `A^n` for some `n >= 1`.
4. `u <= 0` in `K_0(A)`, equivalently `ku <= 0` for some `k >= 1`.
5. `(K_0(A), u)` admits no state.

When they hold, `G` is not surjunctive.

**Mechanism.**
- *Diagonal endomorphism.* Over the `m`-ary family, `D(h) = sum_i s_i h t_i` is an injective group
  endomorphism of `G` that fixes the scalars and commutes with `g`.
- *Halving map.* So `x -> e_H D(x)` is a unital ring homomorphism `A -> T`, and with `A ~= M_m(T)` it
  gives a unital homomorphism `M_m(A) -> A`.
- *Effect.* On projective modules this map divides the unit class by `m`, and it shrinks any failure of
  the rank condition down to size one.

**Instance.** At `(q, d, m) = (3, 2, 2)`, `A = S_-` and item 1 is
`ternary-anti-invariant-swap-corner-is-full`. So that claim is equivalent to
`ternary-anti-central-unit-class-is-nonpositive`, and to the absence of states on
`(K_0(S_-), [eps_-])`.

Proof: Theorem E of the artifact (Section 7).
