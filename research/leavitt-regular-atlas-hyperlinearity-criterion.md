---
rg: 2
id: leavitt-regular-atlas-hyperlinearity-criterion
kind: claim
title: Hyperlinearity of the binary Leavitt unit group is one regular-A8 relative-unitary feasibility problem
distinct_from:
  atlas-steinberg-rank-five-translation: That constructs the finite Steinberg relator packet and central-sufficiency bridge; this is the canonical regular-A8 criterion for the unit group Q itself, with both finite factors frozen to the left regular representation and one relative unitary as the only unknown.
  leavitt-steinberg-hs-stability-fork: That is a stability dichotomy for a Steinberg cover; this is an exact iff characterization of hyperlinearity of Q.
artifacts:
  - notes/EXPLICIT_LEAVITT_ATLAS.md
---

Put

```text
Q = L_(F_2)(1,2)^x.
```

There are two explicit subgroups `K_1,K_2 <= Q`, each isomorphic to `A_8`, a
surjection

```text
bar_rho : bar_P = K_1 * K_2 -> Q,
```

and a fixed finite normal generating set `bar_S` for

```text
bar_N = [bar_P, ker(bar_rho)]
```

such that `bar_P/bar_N` is the universal central extension `U_Q`.

Let `lambda:A_8 -> U(20160)` be the left regular representation.  Then the
following are equivalent.

1. `Q` is hyperlinear.
2. There are integers `k_n>=1` and unitaries
   `U_n in U(20160 k_n)` such that the exact free-product representations

```text
pi_n(h) = lambda(h) tensor I_(k_n)                    (h in K_1),
pi_n(h) = U_n (lambda(h) tensor I_(k_n)) U_n^*        (h in K_2)
```

satisfy

```text
max_(s in bar_S) ||pi_n(s)-1||_2 -> 0.
```

Thus every analytic unknown in the hyperlinearity problem can be placed in
one relative chart unitary; the two finite-factor models are fixed regular
representations up to external multiplicity.
