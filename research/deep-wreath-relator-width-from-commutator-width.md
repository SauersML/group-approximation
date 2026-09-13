---
rg: 2
id: deep-wreath-relator-width-from-commutator-width
kind: route
title: Apply the tower relator-width theorem with the elementary commutator width bound for all transitive towers of bounded degree
target: simple-nonsofic-relator-width-over-iterated-wreath-products
requires: [relator-width-over-towers-of-bounded-commutator-width, transitive-wreath-towers-bounded-commutator-width]
---

Fix `m`. Let `𝒲_m` be the class of all iterated permutational wreath products of transitive groups
`T_i <= Sym(m_i)`, `m_i <= m`, of every depth. It contains the subtree towers of its members.

1. By `transitive-wreath-towers-bounded-commutator-width`, every element of `[H, H]` is a product of at most
   `c = 3(m! + m + 2)` commutators of `H`, for every `H in 𝒲_m`.
2. By `relator-width-over-towers-of-bounded-commutator-width`, applied to `𝒲_m` and this `c`, every finitely
   presented group `G = <X | R>` with no nontrivial finite quotient satisfies
   ```text
   w_W(a) <= sum_r |n_(x,r)| + 2|R| ( |Phi_m| + m - 1 + 6m (m! + m + 2) )
   ```
   for every `W in 𝒲_m` and every `a in W^X`.
3. An infinite finitely presented simple group has no nontrivial finite quotient. So the claim holds,
   with `K(G, m)` the right-hand side. Nonsoficity is not used.
