---
rg: 2
id: stable-laurent-k2-has-minimal-three-symbol-packet
kind: claim
title: Three explicit symbols are the minimal stable Laurent K2 relation packet
distinct_from:
  two-coordinate-relators-leave-stable-laurent-k2: that proves the two inverse-coordinate relations leave the whole Laurent K2 kernel; this identifies and kills a minimal generating packet for that kernel
  one-opposite-steinberg-relator-does-not-close-laurent-cycle: that separates the two ring inverse relations in a finite quotient; these are three central K2 relations after both inverse relations have been imposed
  opposite-transvections-are-first-nonore-relative-gate: that is the pinned group and RE/C gate; this gives an exact stable-range quotient and records the possible unstable and cone-presentation remainders
---

Let `k=F_q`, put `m=q-1`, and fix a generator `a` of the cyclic
group `k^*`.  For

```text
R=k[x_1^(+-1),x_2^(+-1),x_3,...,x_d],
```

write `c(u,v)` for the Steinberg symbol of two units.  One explicit
convention is

```text
W_ij(u)=x_ij(u)x_ji(-u^(-1))x_ij(u),
H_ij(u)=W_ij(u)W_ij(-1),
c(u,v)=[H_12(u),H_13(v)].                                  (MSP1)
```

Inside the stable Steinberg group, put

```text
c_0=c(x_1,x_2),       c_1=c(a,x_1),       c_2=c(a,x_2).     (MSP2)
```

The Bass boundary decomposition identifies

```text
K2(R)=<c_0> (+) <c_1> (+) <c_2>
     ~= Z (+) C_m (+) C_m.                                 (MSP3)
```

Consequently

```text
St(R)/<<c_0,c_1,c_2>> ~= E_inf(R).                          (MSP4)
```

If `q>2`, no packet of fewer than three central relators can do this.
If `q=2`, the torsion summands vanish and the single relation `c_0=1` is
minimal.

The same statement is exact at finite matrix rank in the classical stable
range.  For `r>=d+3`,

```text
St_r(R)/<<c_0,c_1,c_2>> ~= E_r(R).                          (MSP5)
```

Below that range the formula has a precise remainder, not a silent
extension of stability.  Put

```text
U_r=ker(St_r(R)->E_r(R)),
C_r=<<c_0,c_1,c_2>> in St_r(R).
```

Then

```text
ker(St_r(R)/C_r -> E_r(R))=U_r/C_r.                         (MSP6)
```

Stabilization sends `C_r` onto stable `K2(R)`, so `U_r/C_r` is a quotient
of the unstable kernel `ker(U_r->K2(R))`.  It vanishes in (MSP5), but its
vanishing is not known here in the pinned rank-three regime.

There is a second, independent qualification for the two-cone presentation.
Let `barPsi:Q_2->St(R)` be the surjection obtained after imposing the two
inverse-coordinate words, and quotient `Q_2` by any explicit lifts of the
three words in (MSP2).  The resulting group surjects onto `E_inf(R)`, but
the kernel is only known to be a quotient of `ker(barPsi)`.  Thus the
three-symbol packet kills exactly the detected stable `K2` layer; it does
not by itself prove that the cone quotient is the Laurent elementary group.

DERIVATION
bass-boundaries-and-unstable-remainder-proof
