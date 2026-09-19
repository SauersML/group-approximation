---
rg: 2
id: agent-projective-kernel-factor-face-is-playerwise-proof
kind: route
title: Split the factorial projective kernel and tensor CE traces
target: agent-projective-kernel-factor-face-is-playerwise
requires: []
---

Suppose `pi(a,b)` is scalar.  From `(APF1)`,

```text
L(u_a)=chi_pi(a,b) R(v_b)^*.
```

The left side belongs to `L(M)` and the right side belongs to `R(M)`.  Since
`M` is a factor,

```text
L(M) intersect R(M)=C I.
```

Therefore both player operators are scalar.  The converse is immediate,
which proves `K_pi=K_A x K_B`; multiplying their scalar values proves the
character formula in `(APF3)`.  The usual projective-kernel argument makes
`K_A,K_B` normal and `alpha,beta` conjugation invariant.

If a CE trace belongs to the full face on `G_A x G_B`, restrict it to the two
canonical player subgroups.  A von Neumann subalgebra of a Connes-embeddable
finite von Neumann algebra is Connes embeddable, and the face equations for
`(a,1)` and `(1,b)` give the two one-player scalar equations.  Both
one-player faces therefore contain CE traces.

Conversely, take CE traces `sigma_A,sigma_B` in the two one-player faces.
Their product trace is CE: matrix microstates for two finite sets can be
tensored, or equivalently their GNS algebras embed into a tracial matrix
ultraproduct after tensoring the representing matrices.  For
`(a,b) in K_A x K_B`,

```text
(sigma_A tensor sigma_B)
  (overline(alpha(a)beta(b)) (a,b))=1.
```

Hence the product trace belongs to the full face, proving `(APF4)`.

Finally `K<=K_pi` gives

```text
F_(K_pi,chi_pi)^tr subseteq F_(K,chi)^tr.
```

If the latter has no CE point, neither does the former, and `(APF4)` forces
one of the player faces to be CE-empty.  This proves `(APF5)`.

