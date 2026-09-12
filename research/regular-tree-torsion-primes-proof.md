---
rg: 2
id: regular-tree-torsion-primes-proof
kind: route
title: Level actions land in iterated wreath products of S_d, whose orders have no prime factor above d
target: regular-tree-torsion-orders-have-primes-at-most-degree
requires: []
---

1. **Level quotients.** For `n >= 1` let `B_n` be the ball of radius `n` about
   the root of `T_d`. Restriction gives a homomorphism
   `rho_n : Aut(T_d) -> Aut(B_n)`. The group `Aut(B_n)` is the `n`-fold iterated
   wreath product of `S_d`, of order `(d!)^(1 + d + ... + d^(n-1))`. So every
   prime dividing `|Aut(B_n)|` divides `d!`, and is at most `d`.
2. **Orders stabilize.** Let `g` have finite order `m`, and put
   `m_n = ord(rho_n(g))`.
   - `m_n` divides `|Aut(B_n)|`, so its prime factors are at most `d`.
   - `rho_n` factors through `rho_(n+1)`, so `m_n` divides `m_(n+1)`.
   - Every `m_n` divides `m`.

   So the sequence `m_n` is eventually constant, equal to some `m_N`.
3. **Faithfulness.** An automorphism that fixes every ball `B_n` pointwise is
   the identity. Hence `g^k = 1` if and only if `rho_n(g)^k = 1` for every `n`,
   so `m = m_N`. Every prime factor of `m` is at most `d`. `∎`
4. **Consequences.** A faithful action of `G` on `T_d` embeds `G` in
   `Aut(T_d)`, and the embedding preserves the order of each element. So an
   element of prime order `p` forces `p <= d`. A self-similar group is by
   definition a subgroup of `Aut(T_d)` for some `d`.
