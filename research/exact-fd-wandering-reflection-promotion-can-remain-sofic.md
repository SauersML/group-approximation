---
rg: 2
id: exact-fd-wandering-reflection-promotion-can-remain-sofic
kind: claim
title: Exact finite-dimensional wandering reflection promotion can remain sofic
distinct_from:
  exact-fd-invisibility-has-no-general-hs-robustification: that gives a finite-order central word which exact finite-dimensional representations kill; this converts it into an infinite-order wandering word, attaches an arbitrary already-wordized corner reflection, and retains a finitely presented sofic countermodel to approximate promotion.
  fanizza-coherent-verifier-wandering-promotion: that requires vanishing compression error in every canonical matrix microstate; this proves that exact equality in every finite-dimensional representation, infinite-order normal form, and exact infinite completeness still do not imply that requirement.
---

**ESTABLISHED FIREWALL.**  Let `A` be any finitely presented sofic group,
let `0!=q=q^*=q^2 in C[A]`, and let `v in A` commute with `q` and satisfy

```text
v^m=1,                 (qv)^m=q                         (EWP1)
```

for some fixed `m`.  Thus `qv` is an already-wordized finite-order corner
unitary; the reflection case is `m=2`.

There is an explicit finitely presented sofic overgroup `Gamma` and an
ordinary infinite-order word `w` such that:

1. every exact finite-dimensional unitary representation of `Gamma`
   satisfies

   ```text
   q(w-v)q=0;                                             (EWP2)
   ```

2. `w` has infinite order and all its positive powers are distinct;
3. every exact representation of `A` extends after tensoring with an exact
   representation of the auxiliary factor; but
4. canonical matrix microstates of `Gamma` satisfy

   ```text
   ||q(w-v)q||_2^2 -> 2 tau_A(q)>0.                      (EWP3)
   ```

Consequently exact finite-dimensional invisibility of an actuator does not
promote an already-wordized Fanizza reflection.  This remains false even
after finite presentation, soficity, infinite-order normal form, and exact
infinite completeness have all been supplied.

## Construction

Take the finitely presented sofic Slofstra--Vidick group `K` and its
nontrivial central involution `c` from
`exact-fd-invisibility-has-no-general-hs-robustification`.  Every
finite-dimensional unitary representation of `K` sends `c` to one.  Put

```text
L=K * <t>,             h=[t,c],
Gamma=A times L,       w=v h.                           (EWP4)
```

Free and direct products preserve soficity, so `Gamma` is finitely
presented and sofic.  The reduced free-product word `h` is cyclically
reduced and nontrivial; every positive power remains reduced, so `h`, and
hence `w`, has infinite order.  On the other hand every finite-dimensional
representation kills `c`, hence kills `h`, proving `(EWP2)`.

In the canonical regular representation, the two direct factors commute and

```text
q(w-v)q=(qv) tensor (h-1).
```

Since `qv` is a corner unitary and `h!=1`,

```text
||q(w-v)q||_2^2
 =tau_A(q) ||h-1||_(2,L(L))^2
 =2 tau_A(q),                                            (EWP5)
```

which gives `(EWP3)` along canonical sofic microstates.

The auxiliary exact representation required for completeness can simply be
the left regular representation of `L`; tensoring it with the chosen exact
`A`-representation extends the direct product and keeps `h` nontrivial.

## Consequence for verifier two-cells

The construction grants the strongest purely exact version of the desired
promotion: the actuator disappears in **all** finite-dimensional
representations, not just in selected packet types.  Nevertheless its HS
error stays at the full regular value.  Therefore a successful
payload-sensitive non--Bass--Serre two-cell must prove an approximate,
dimension-independent estimate coupling the actuator to the verifier
carrier.  Exact representation classification, minimal almost periodicity,
or a direct-product sterile actor cannot supply that estimate.

