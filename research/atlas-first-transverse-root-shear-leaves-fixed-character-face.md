---
rg: 2
id: atlas-first-transverse-root-shear-leaves-fixed-character-face
kind: claim
title: The first transverse Atlas rows shear character fibers in pairs and leave a fixed face
distinct_from:
  atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity: that identifies the two-qubit CK spin factor and its arbitrary eE/fF multiplicity split inside each negative first-root atom; this computes the first full-packet root direction which actually moves those atoms.
  pauli-two-child-transfer-packet: that supplies two partial isometries from one raw/comb Pauli source; this is an order-two permutation of additive-root character fibers and supplies no source-saturating partial isometry.
  orthogonal-steinberg-root-spectral-support-is-not-additive: that rules out recovering module support from individual additive-root cuts; this gives the exact transverse permutation of their joint character atoms.
---

**ESTABLISHED EXACT TRANSPORT AND LOCAL NO-GO.**  For every coefficient
letter `a in {1,e,f,E,F}`, put

```text
C_a=pi(x_12(a)),       D_a=pi(x_13(a)),
T=pi(x_23(1)).                                           (TRS1)
```

The five shortest transverse Steinberg rows are

```text
[C_a,T]=D_a.                                             (TRS2)
```

The `C_a` form a commuting involution family, the `D_a` form another, the
two families commute with each other, and `T` commutes with every `D_a`.
Consequently

```text
T C_a T = C_a D_a,       T D_a T=D_a.                   (TRS3)
```

Refine the old first-root atoms `Q_chi` by the joint spectral character
`eta` of the `D_a`.  On the joint atom `Q_(chi,eta)`, conjugation by `T`
has the exact affine action

```text
T Q_(chi,eta) T = Q_(chi*eta,eta),                      (TRS4)
```

where `*` is pointwise multiplication of signs.  Thus every nontrivial
`eta` pairs two equal-rank `chi` fibers, while `eta=(+,+,+,+,+)` fixes every
`chi` fiber.  This is the first literal packet family that couples distinct
`Q_chi`, but its orbits have length at most two.

The action on the CK partition branches is equally explicit.  Let

```text
p=eE, q=fF,
C_p=pi(x_12(p)), C_q=pi(x_12(q)),
D_p=pi(x_13(p)), D_q=pi(x_13(q)),
Z=C_p C_q=pi(x_12(1)),
W=D_p D_q=pi(x_13(1)).                                  (TRS5)
```

Spare-index independence and the ring relations extend `(TRS3)` to `p,q`.
On a joint sign sector, write `eta_p,eta_q` for the signs of `D_p,D_q`.

* If `W=+1` and `eta_p=eta_q=-1`, then `T` preserves the `Z=-1` carrier
  and exchanges its complementary `p` and `q` branches.  Their paired
  multiplicities are equal.
* If `W=+1` and `eta_p=eta_q=+1`, then `T` fixes both branches.  Their
  multiplicities remain arbitrary.
* If `W=-1`, then `T` exchanges the `Z=-1` and `Z=+1` carriers rather than
  balancing the two branches inside the marked carrier.

Hence the first nonlocal root direction forces balance only on the
`(W,eta_p)=(+1,-1)` summand.  It permits an arbitrary unbalanced summand on
the fixed face `(W,eta_p)=(+1,+1)` and an order-two marked/unmarked escape on
`W=-1`.  It produces no one-sided shift tower.

This limitation is exact.  For the local relations `(TRS2)--(TRS3)`, take
all `D_a=1` and `T=1`; then every first-root character fiber is fixed and
its multiplicity is arbitrary.  Tensoring this fixed shear model with the
two-qubit CK model preserves every split from
`atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity`.  This is a
countermodel to the transverse-shear subsystem, not to the whole Atlas
packet.

Therefore the next useful rows must either force positive mass away from the
fixed `D`-character face or combine at least two transverse directions whose
fixed faces intersect more rigidly.  Merely iterating `(TRS2)` cannot compare
the entire `M_p direct-sum M_q` multiplicity.

DERIVATION
atlas-first-transverse-root-shear-proof
