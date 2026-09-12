---
rg: 2
id: jacobson-shift-gap-characterizes-mark-collapse
kind: claim
title: The shifted Jacobson matrix infimum exactly characterizes marked corona collapse
distinct_from:
  jacobson-boundary-amalgam-gap-characterizes-mark-collapse: that uses the smaller Xi presentation with two mixed relators; this uses the full boundary and six-coordinate packets with an additional stable letter enforcing recursion.
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
---

Use `Theta_shift`, `B,C,Z,F`, and its nontrivial mark `w=x_13,Q`
from `jacobson-stable-letter-closes-boundary-recursion`. Define
`alpha_F:F->tau(G) x delta(G)` by
`alpha_F(g_Q)=tau(g)` and `alpha_F(g_P)=delta(g)`.

Let `gamma_shift` be the infimum, over every positive dimension,
of

```text
max( ||(H rho_B(b))^3-I||,
     ||W-I||,
     ||T H T^*-H_1|| ),
```

where `rho_B,rho_C` are exact representations on that dimension,
agreeing on all of `Z`, `rho_B(w)!=I`, `H=rho_C(h)`,
`H_1=rho_C(h_1)`, and `T` is an exact unitary intertwiner

```text
T rho_B(f) T^*=rho_B(alpha_F(f))      for every f in F.
```

All occurrences of `H` in the two old relators use that same
operator. The domain is nonempty and `0<=gamma_shift<=2`.
Strict positivity is equivalent to every homomorphism from
`Theta_shift` to every norm matrix corona killing `w`.

Zero infimum is equivalent to existence of a corona homomorphism
retaining this mark; it is not asserted equivalent to MF of the
whole group. The sign of the infimum remains unsettled.

The new stable-letter equations on `F` can all be corrected exactly
on the original dimension. If their maximum error over `F` is
`epsilon<1`, the corrected unitary `T'` satisfies
`||T'-T||<=2epsilon`, and the remaining `h` error increases by
at most `4epsilon`. The two old mixed errors are unchanged by
this correction.

Only the six finite generators need to be tested. Let `d_F` be
their maximum intertwining error. Every element of each `GL_3`
factor has word length at most 167 in `Sigma`, so
`epsilon<=334 d_F`. For `334 d_F<1` this gives

```text
||T'-T||<=668 d_F,
remaining h error increases by at most 1336 d_F.
```

Let `eta_shift` be the infimum over exact `B,C` representations
glued on `Z`, with the mark retained and arbitrary unitary `T`,
of the maximum of the three mixed errors and the six generator
intertwining errors. Then

```text
eta_shift<=gamma_shift<=1337 eta_shift.
```

Thus the same positive-gap condition can be stated using exactly
nine finite word errors. This comparison does not prove positivity.

DERIVATION
jacobson-shift-relative-corona-lifting-proof
