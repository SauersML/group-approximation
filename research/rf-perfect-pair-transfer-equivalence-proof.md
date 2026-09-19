---
rg: 2
id: rf-perfect-pair-transfer-equivalence-proof
kind: route
title: Perfectness removes phases and residual-finite camouflage removes the trace profile
target: rf-perfect-pair-transfer-equals-regular-rcc
requires:
  - projective-transfer-linear-bound-equals-no-ultraproduct-leak
artifacts:
  - research/artifacts/rf-perfect-projective-rcc-audit-2026-08-30.md
---

First assume `(RPT1)`.  Let `pi:A->U(M)` have regular trace and let
`u in pi(C)' cap M` be unitary.  Lift `pi` and `u` to presentation tuples
`rho_n` and unitaries `u_n`.  Then `delta(rho_n)->0` and
`q(rho_n,u_n)->0`, so `(RPT1)` gives `e_h(rho_n,u_n)->0`.  In `M`, equality
in Cauchy--Schwarz says

```text
u pi(h) u^* pi(h)^* = z 1
```

for some `z in T`.  Since `u` commutes with `pi(C)` and `A=<C,h>`,
conjugation by `u` defines a character `chi:A->T`, trivial on `C`, with
`chi(h)=z`: every defining relation forces the corresponding scalar
relation.  Perfectness of `A` gives `chi=1`, hence `u` commutes with `pi(h)`
and therefore with `pi(A)`.  Unitaries span the finite von Neumann algebra
`pi(C)' cap M`, proving `(RPT2)`.

Conversely assume `(RPT2)`.  By
`projective-transfer-linear-bound-equals-no-ultraproduct-leak`, failure of
`(RPT1)` produces tuples and witnesses with

```text
delta(rho_n)->0,   q(rho_n,u_n)->0,
liminf e_h(rho_n,u_n)>0.                                (RPT3)
```

They define `pi:A->U(M)` and `u in U(M)`.  Projective centrality on `S`
gives scalars `chi(s)` with
`u pi(s) u^*=chi(s)pi(s)`.  The relations of `C` make `chi:C->T` a
character, so perfectness of `C` makes it trivial.  Thus
`u in pi(C)' cap M`.

Now remove the arbitrary trace profile.  Enumerate
`A\{1}={g_1,g_2,...}`.  Residual finiteness gives finite quotients
`q_n:A->Q_n` with `q_n(g_j)!=1` for `j<=n`; let `lambda_n` be the left
regular representation of `Q_n`.  Set

```text
rho_tilde_n(x)=rho_n(x) tensor lambda_n(q_n(x)),
u_tilde_n=u_n tensor I.
```

For every relator and every word `g`, normalized trace multiplicativity gives

```text
delta(rho_tilde_n)=delta(rho_n),
1-|tr([u_tilde_n,rho_tilde_n(g)])|^2
 =1-|tr([u_n,rho_n(g)])|^2.                            (RPT4)
```

For fixed `g_j!=1`, the second tensor factor has regular trace zero once
`n>=j`; hence `rho_tilde_n` induces a regular-trace representation
`pi_tilde:A->U(M)`.  Equation `(RPT4)` keeps `u_tilde` in
`pi_tilde(C)'`, while `(RPT2)` puts it in `pi_tilde(A)'`.  Its target energy
is therefore zero, contradicting `(RPT3)` and the exact preservation in
`(RPT4)`.  No unrestricted projective leak exists, and the cited
linearization theorem gives `(RPT1)`.