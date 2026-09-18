---
rg: 2
id: amenable-cd-two-groups-have-an-l2-rank-gap
kind: claim
title: In the integral group ring of a finitely generated amenable group of cd 2, the L2-ranks of nonzero elements are bounded away from zero
distinct_from:
  amenable-finite-cd-integral-group-rings-are-domains: that asks for no zero divisors, i.e. (for amenable groups) L2-rank exactly 1 for every nonzero element; this asks only for some positive lower bound
  elementary-amenable-torsion-free-strong-atiyah: that is integrality of all matrix L2-ranks for elementary amenable groups; this is a lower bound for 1x1 ranks for amenable cd-2 groups, with no integrality
  amenable-cd-two-l2-rank-gap-forces-baumslag-solitar: that proves this statement is equivalent to Kropholler's question in dimension 2; this is the open statement itself
---

**OPEN.** Let `G` be a finitely generated amenable group with `cd G = 2`. Then there is `c > 0`
such that `dim_U(U(G) a) >= c` for every nonzero `a ∈ Z[G]`. Equivalently,
`dim_NG ker(r_a : ℓ²G → ℓ²G) <= 1 − c`, where `r_a` is right multiplication by `a`.

By `amenable-cd-two-l2-rank-gap-forces-baumslag-solitar` (items 3–4), this is equivalent to
Kropholler's question for groups of cd at most 2, and it then holds with `c = 1`. It suffices to
have the bound for nonzero elements of the trace ideal of one second syzygy `P ≤ Z[G]^d`.

**Shape of a counterexample.** A counterexample has nonzero `a_n ∈ Z[G]` with
`dim_NG ker(r_{a_n}) → 1`. The `a_n` can be chosen in the trace ideal of `P`, each in the image
of a dual-basis functional. For amenable `G`, `dim_NG ker(r_a)` is the Følner limit of the
normalized kernel dimensions of `a` acting on finite Følner pieces (Elek; recalled). So a
counterexample needs integral group-ring elements whose finite kernel densities approach 1.
