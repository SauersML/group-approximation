---
rg: 2
id: sparse-relator-expanding-orbit-counterpacket-proof
kind: route
title: Cross-switch one redundant-generator edge between two congruence orbits
target: sparse-relator-defects-defeat-orbitwise-classicalization
requires:
  - orbitwise-relator-classicalization-separates-mihailova-kernel
---

Fix a finite presentation `Q_0=<S | R>` of `SL_3(Z)` and add a redundant
generator `z` with relator `r_0=z w(S)^(-1)`, where `w(S)` is any fixed word.
Let `F_p=SL_3(F_p)` for odd primes `p`, and let every `s in S` act by left
multiplication on each of two disjoint copies of `F_p`.

Denote left multiplication by the reduction of `w` by `P_w`.  Choose one
point in each copy and let `T_p` transpose those two points.  Define the free
generator `z` to act by

```text
P_z=T_p P_w.                                            (SRC1)
```

This is an exact action of the free group `E_0` by permutations.  The
`S`-edges are transitive inside each copy and the one cross-switch in
`P_z` joins the copies, so the full `E_0`-action on
`Omega_p=F_p times {0,1}` is transitive.  Every relator in `R` acts
identically.  With the convention in `(SRC1)`,

```text
P_(r_0)=P_z P_w^(-1)=T_p,                              (SRC2)
```

so `r_0` moves exactly two of `2|F_p|` points.  In particular all relator
defect densities tend to zero, but the unique nonempty invariant subset is
`Omega_p` itself and `r_0` is nontrivial there.

For a prescribed radius `k`, only a bounded number (depending on `k`, not
`p`) of starting points have a length-`k` path that encounters the switched
targets.  Residual finiteness of `SL_3(Z)` makes reduction modulo sufficiently
large `p` injective on its radius-`2k` ball.  Choose `o_p` outside the bounded
bad set.  Its rooted labelled `k`-ball is then exactly the `Q_0` ball: every
appearance of `z` follows `w`, and all original relators hold.

Finally put

```text
H_p=ell^2({-1,1}^(Omega_p)).                            (SRC3)
```

For `x in Omega_p`, let `A_x` be multiplication by the coordinate sign, and
let `U_g` be the Koopman permutation unitary of the exact `E_0`-action.  Haar
independence gives `(SRD2)` exactly, and

```text
U_g A_x U_g^*=A_(gx)                                   (SRC4)
```

exactly.  Thus neither higher lamp moments nor actor monomiality is missing.
Removing the two points moved by `r_0` does not help: its invariant saturation
is all of `Omega_p` by transitivity.  This proves every clause.

