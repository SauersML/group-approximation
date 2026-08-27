---
rg: 2
id: finite-bass-serre-dyadic-cell-has-exact-countermodel
kind: claim
title: Every finite Bass--Serre compiler for the dyadic three-row cell has an exact marked countermodel
distinct_from:
  finite-bs-selectors-have-marked-fd-countermodels: That retains every named selector packet in one exact finite quotient; this evaluates arbitrary compressed group-word rows in that quotient and obtains an explicit normalized-HS floor from the strict dyadic target capacity.
  dyadic-pauli-payload-flags-supply-strict-target-capacity: That proves a faithful regular-trace obstruction to functorial row extraction; this shows that every finite construction by finite amalgams and finite-subgroup HNN edges has a finite-dimensional exact countermodel carrying that obstruction.
  two-affine-half-rows-pay-deleted-dyadic-atom: That gives a sharper deleted-atom identity when both rows normalize the flag algebra; this permits completely arbitrary Bass--Serre group words in the four compressed row slots.
  canonical-types-extend-every-finite-bass-serre-actor: That extends canonical ultraproduct types through a finite Bass--Serre actor; this produces a literal finite quotient and a quantitative lower bound for the specific three-row compiler.
---

**ESTABLISHED SHARP FIREWALL.**  Fix one BCS context with `k` visible
Boolean variables and keep its central-sign packet

```text
D=<J,x_1,...,x_k> ~= C_2^(k+1)                       (BDR1)
```

embedded.  Fix an assignment atom `C` in the `J=-1` sector and attach the
depth-`n` Pauli packet of
`dyadic-pauli-payload-flags-supply-strict-target-capacity`.  Thus

```text
E=C(1-Z_1)/2,
F=C-C product_(j=1)^n (1-Z_j)/2,
kappa=2^(1-n),                                         (BDR2)
```

are finite-group-algebra projections.

Starting from the shared-variable right-angled Coxeter base, enlarge the
presentation finitely many times only by

1. amalgamating finite packet groups over named finite subgroups;
2. adjoining HNN letters which identify named finite subgroups; or
3. forming a finite graph of such vertex and edge groups.

Call the resulting group `Gamma`.  For **arbitrary** words
`u_0,u_1,v_0,v_1 in Gamma`, there is an exact finite-dimensional unitary
representation `rho` of `Gamma` in which the whole packet in `(BDR1)--(BDR2)`
is injected and, for

```text
s_i=rho(F)rho(u_i)rho(E),
t_i=rho(E)rho(v_i)rho(F),
epsilon_i=||t_i s_i-rho(E)||_2,
eta=||t_0s_1||_2,                                      (BDR3)
```

one has

```text
max(epsilon_0,epsilon_1,eta)
 >= kappa sqrt(q)/16,
q=tr(rho(E))=2^(-(k+2)).                               (BDR4)
```

In particular,

```text
epsilon_0^2+epsilon_1^2+eta^2
 >= kappa^2 q/256
 =2^(-2n-k-8)>0.                                      (BDR5)
```

The lower bound depends only on the fixed context and Pauli depth, never on
the dimension of a competing representation.

Consequently no compiler in this finite Bass--Serre class can derive

```text
t_0s_0=E,             t_1s_1=E,             t_0s_1=0  (BDR6)
```

as group-algebra identities, nor can it bound the three defects in `(BDR3)`
by a modulus tending to zero with the defining-relator energy.  The
countermodel has defining-relator energy exactly zero while retaining both
the marked sign and the forbidden atom.

This remains true even if the perfect tracial BCS representation happens to
extend through the proposed packet and all its forbidden atoms vanish there.
Vacuity on that one representation cannot turn finite-subgroup covariance
into a matrix-only implication: the ordinary presentation also has the exact
finite quotient above.

## Exact scope

The theorem permits arbitrary reduced Bass--Serre words in the row slots;
they need not normalize the flag algebra and may cross the finite graph many
times.  What it excludes is deriving the row laws solely from the finite
vertex multiplication tables and finite-edge conjugacy/intertwiner
relations.

A surviving compiler must add at least one relation outside this class whose
finite-dimensional consequence couples the two inverse rows and the crossed
row to the **same** payload-conditioned pair `(E,F)`, while remaining
tracially satisfiable because `C=0` in the perfect model.  Such a relation is
precisely the payload-sensitive two-cell/nonstationary coefficient gate, not
a larger finite packet, another Reynolds subgroup, or another finite HNN
edge.

DERIVATION
finite-bass-serre-dyadic-three-row-countermodel-proof
