---
rg: 2
id: root-preserving-el3-isomorphisms-give-ring-isomorphisms-proof
kind: route
title: Coordinatization from the commutator relations, with direct finiteness supplying the units
target: root-preserving-el3-isomorphisms-give-ring-isomorphisms
requires: []
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
---

Since `e_ij(r+s) = e_ij(r)e_ij(s)`, the maps `φ_ij: R → S` defined by `α(e_ij(r)) = e_ij(φ_ij(r))` are additive
bijections. Applying `α` to `[e_ik(r), e_kj(s)] = e_ij(rs)`, for distinct `i, j, k`, gives

  (∗) `φ_ij(rs) = φ_ik(r) φ_kj(s)` for all `r, s ∈ R`.

Put `a = φ_12(1)` and `b = φ_23(1)`, and take `(i,j,k) = (1,3,2)` in (∗):
- with `s = 1`, `φ_13(r) = φ_12(r) b`, and `φ_13` is onto, so `S = Sb`;
- with `r = 1`, `φ_13(s) = a φ_23(s)`, and `φ_13` is onto, so `S = aS`.

So `b` has a left inverse and `a` has a right inverse. `S` is directly finite, so both are two-sided and
`a, b ∈ S^×`. Substituting `φ_23(s) = a^{-1}φ_13(s) = a^{-1}φ_12(s)b` back into (∗) for `(1,3,2)`,

  `φ_12(rs) b = φ_13(rs) = φ_12(r) φ_23(s) = φ_12(r) a^{-1} φ_12(s) b`,

and cancelling the unit `b` gives `φ_12(rs) = φ_12(r) a^{-1} φ_12(s)`. Put `ψ(r) = a^{-1}φ_12(r)`. Then `ψ` is
additive and bijective, `ψ(1) = a^{-1}a = 1`, and

  `ψ(rs) = a^{-1}φ_12(rs) = a^{-1}φ_12(r) a^{-1} φ_12(s) = ψ(r)ψ(s)`,

so `ψ` is a ring isomorphism and `α(e_12(r)) = e_12(aψ(r))`.

**The hexagon.** `A_ij` and `A_kl` commute iff `j ≠ k` and `l ≠ i`, so the commuting graph on the six root
subgroups is the hexagon `A_32 – A_12 – A_13 – A_23 – A_21 – A_31 – A_32`, whose automorphism group has order 12.
Conjugation by the permutation matrix `P_σ` sends `A_ij` to `A_{σ(i)σ(j)}`, and `S_3` acts simply transitively on
the six ordered pairs; the graph automorphism sends every `A_ij` to `A_ji`, which no relabelling does. So the two
together realize all 12 automorphisms, and an isomorphism carrying the set of root subgroups onto the set of root
subgroups can be corrected to one matching the labels.

**Model test.** For `R = S` a field and `α` the identity, `φ_ij = id`, `a = b = 1` and `ψ = id`. For `α`
conjugation by `diag(d_1,d_2,d_3)`, `φ_12(r) = d_1 r d_2^{-1}`, so `a = d_1d_2^{-1}` and `ψ(r) = d_2 r d_2^{-1}`, an
inner ring automorphism, as it must be. Direct finiteness is necessary for the step as written: over a ring where
`ab = 1 ≠ ba`, surjectivity of `φ_13` gives only one-sided inverses and `ψ` cannot be formed.
