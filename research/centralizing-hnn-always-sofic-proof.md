---
rg: 2
id: centralizing-hnn-always-sofic-proof
kind: route
title: Reidemeister--Schreier along b exhibits a right-angled Artin kernel, then sofic-by-amenable
target: centralizing-hnn-over-conjugate-basis-is-always-sofic
requires: []
---

Let `chi : H_J -> Z` send `b` to `1` and `a, s` to `0`; it is well defined
since every relator is a commutator.  Its kernel `N_J` is the normal closure
of `{a, s}`.  Reidemeister--Schreier with the transversal `{b^k : k in Z}`
gives generators `a_i = b^i a b^-i` and `s_k = b^k s b^-k` (`i, k in Z`)
and, as relators, the conjugates of the defining relators:

```text
b^k [s, a_j] b^-k = [s_k, a_{j+k}],     j in J, k in Z,
```

i.e. `[s_k, a_i] = 1` iff `i - k in J`.  So `N_J` is the right-angled Artin
group `A(Gamma_J)` on the bipartite graph `Gamma_J` with those edges, and
`b` acts on it by the graph automorphism `a_i |-> a_{i+1}`, `s_k |-> s_{k+1}`:
`H_J = A(Gamma_J) x| Z`.

Right-angled Artin groups on countable graphs are residually finite: every
finitely generated subgroup lies in the parabolic subgroup on a finite full
subgraph, which is a retract of `A(Gamma_J)` and is a finitely generated
right-angled Artin group, hence residually finite (linear over `Z`); a
nontrivial element therefore survives in a finite quotient of the retract,
which is a finite quotient of `A(Gamma_J)`.  Residually finite groups are
sofic, and an extension of a sofic group by the amenable group `Z` is
sofic by Elek--Szabo's theorem.
