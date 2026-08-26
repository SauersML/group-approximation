---
rg: 2
id: leavitt-amalgam-microstates-have-unrepairable-kernel
kind: claim
title: Canonical amenable-amalgam microstates cannot be perturbatively repaired into models of the literal Leavitt join
distinct_from:
  leavitt-one-compressor-join-is-proper-amalgam-quotient: that proves only that the quotient kernel is nonzero; this gives the normalized-HS distance obstruction to repairing canonical amalgam models.
  reduced-amalgam-canonical-trace-is-mf: that asks for operator-norm MF trace selection on a different Kazhdan double; this uses only ordinary sofic/hyperlinear canonical microstates of an amenable-factor amalgam and proves a negative perturbation statement.
  hyperlinear-trace-not-mf-trace: that separates two trace approximation classes abstractly; this is the elementary fixed-word trace obstruction for one concrete quotient map.
---

Let `q:G=A *_C B -> J=<L,tau,c>` be `(PAQ1)`. For every nontrivial
`k in ker q`, canonical microstates `sigma_n` of the sofic group `G` satisfy

```text
||sigma_n(k)-1||_2 -> sqrt(2).                            (UKR1)
```

Consequently no generator tuples obtained from `sigma_n` by an `o(1)`
normalized-HS perturbation can make even this fixed quotient relation have
defect tending to zero. In particular, one cannot construct canonical
microstates of `J` by taking canonical amenable-amalgam models and adjusting
their edge identifications or a vanishing fraction of matrix coordinates.

For the base-face amalgam `A_0=L_0*_(C_0)P`, the obstruction is completely
explicit: take

```text
k=r=w x_02(s_0) w^(-1) x_12(s_0)^(-1).
```

Then `(UKR1)` holds by the reduced normal form in
`leavitt-first-mixed-amenable-face-relator`.

**Scope.** This does not decide hyperlinearity of `J`. A hypothetical model of
the quotient may be a fixed positive HS distance from every canonical free
amalgam model. The result rules out only the tempting perturbative gluing and
trace-approximable-quotient construction.
