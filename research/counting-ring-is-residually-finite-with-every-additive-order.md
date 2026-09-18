---
rg: 2
id: counting-ring-is-residually-finite-with-every-additive-order
kind: claim
title: The three-relator counting ring Z<u,x,e | xu=ux+x, ue=0, eu=0> is residually finite and has additive elements of every finite order
distinct_from:
  fp-rf-group-with-unbounded-prime-torsion: that asks for a finitely presented residually finite group with unbounded prime torsion; this is a finitely presented residually finite ring with unbounded additive torsion, whose Steinberg groups carry the torsion but are not known to be residually finite.
  ring-simple-envelope-characteristic-obstruction: that concerns simple envelopes of rings with mixed additive torsion; this constructs one explicit finitely presented residually finite ring with torsion of every order.
artifacts:
  - research/counting-ring-rf-every-additive-order-proof.md
  - experiments/counting-ring-steinberg-2026-09-17/check_counting_ring.py
---

**ESTABLISHED (2026-09-17, swarm-0917-w6-w6-z-last2)** through
`counting-ring-rf-every-additive-order-proof`. The route
is a self-contained proof with no imports. No novelty is claimed.

**Statement.** Let

```text
R_count = Z<u, x, e | xu - ux - x = 0,  ue = 0,  eu = 0>
```

be the unital associative ring on three generators and three relations. Put
`r_n = e x^n e`. Then:

- **(C1) every additive order.** For each `n >= 1`, `r_n` has additive order
  exactly `n`. Hence `R_count` has additive elements of every prime order.
- **(C2) finite witnesses.** There is a ring homomorphism
  `rho_n : R_count -> M_n(Z/n)` with `rho_n(r_n)` the matrix unit `E_00`, which
  has additive order `n`.
- **(C3) residual finiteness.** For every nonzero `w` in `R_count` there is a
  finite ring `S` and a ring homomorphism `R_count -> S` that does not kill `w`.

**Why the relations count.** From `xu = (u+1)x` one gets `x^n u = (u+n) x^n`, so
`n r_n = e x^n u e - e u x^n e = 0`. The witnesses `rho_n` show nothing smaller
kills `r_n`.

**Obstructions this ring avoids.** It is not left or right Noetherian: in a
Noetherian ring the torsion ideal is finitely generated, so it has bounded
exponent. Nor does it embed in matrices over a commutative Noetherian ring,
which would force the same bound.
