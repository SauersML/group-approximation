---
rg: 2
id: s3-packet-dressing-preserves-projective-microstate-gap
kind: claim
title: A fixed S3 packet neither creates nor removes an infinite-stabilizer projective HS gap
distinct_from:
  finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape: That treats a finite active holonomy by inverse-twisted regular absorption; this treats an arbitrary infinite active stabilizer and proves that the fixed finite packet is analytically neutral.
  deligne-sector-gap-is-exactly-nonhyperlinearity: That identifies the bare Maslov-sector gap with non-hyperlinearity of Deligne's triple cover; this proves that adjoining the complete S3 escape packet and inducing over its finite orbit does not make that gap any easier.
  minimal-s3-one-letter-actors-have-twisted-countermodels: That gives exact or hyperfinite countermodels for virtually free and amenable stabilizers; this reaches nonamenable property-T stabilizers and identifies the first finitely presented survivor.
---

**ESTABLISHED PACKET-NEUTRALITY THEOREM.**  Let `F=S_3` act transitively on
a fixed finite packet-type orbit `O`, let `sigma in O`, and write
`H=Stab_F(sigma)`.  Suppose the packet implementers on the `sigma` fibre have
finite multiplier `omega` on `H`.  Let `K` be any finitely presented group
and let `alpha` be a finite-valued multiplier on `K`.  Give

```text
Q=F x K                                                     (SPD1)
```

the outer packet action through `F`, so that `K` acts trivially on packet
types.  On the active stabilizer `H x K`, use the product multiplier

```text
beta((h,k),(h',k'))=omega(h,h') alpha(k,k').                (SPD2)
```

Then the following are equivalent:

1. the `alpha^(-1)` projective presentation of `K` has matrix microstates;
2. the `beta^(-1)` projective active stabilizer has matrix microstates;
3. the full `Q` packet cell has matrix microstates with `sigma`-density at
   least `1/|O|` times a fixed positive finite-packet constant.

The equivalence remains true with a uniform positive normalized-HS defect
gap in place of matrix microstates, up to constants depending only on the
fixed finite packet and the chosen finite presentations.  In particular, a
fixed complete irreducible `S_3` outer action can force its one genuine
finite-orbit escape, but it cannot amplify a projective gap on an infinite
active stabilizer.

There are two sharp property-`(T)` consequences.

* Attach the packet to Thom's exact LEF Kazhdan group from
  `thom-kazhdan-central-fibre-hyperlinear-nonamenable`.  Its nontrivial
  central-character projective microstates tensor with the inverse finite
  packet twist and induce to full-cell microstates of positive active
  density.  Thus nonamenability, property `(T)`, exact finite-dimensional
  central invisibility, and the complete `S_3` escape packet still admit
  regular-absorption countermodels.  Finite presentation is essential here:
  Thom's group is not finitely presented.

* The first concrete finitely presented property-`(T)` survivor is obtained
  from Deligne's triple cover

  ```text
  1 -> Z/3=<z> -> E_3 -> Sp_4(Z) -> 1.                    (SPD3)
  ```

  Equivalently take the ordinary actor `S_3 x E_3`, with `E_3` acting
  trivially on packet types, and cut to a nontrivial central character of
  `z`.  This actor is finitely presented and has property `(T)`; its exact
  tracial active sector is the finite packet amplification of the mod-three
  Maslov twisted regular algebra.  Every exact finite-dimensional
  representation kills `z`, but packet-neutrality shows that a reusable
  escape estimate for this actor is **exactly** the still-open Maslov
  projective HS gap, not a weaker consequence of its `S_3` geometry.

Quantitatively, assume the nontrivial Maslov sector has projective relator
energy at least `c^2>0` in every matrix dimension.  For an approximate full
packet representation of total squared presentation energy `E`, finite
packet correction and central spectral cutting give

```text
q_nontriv c^2 <= C_packet E,                               (SPD4)
```

where `q_nontriv` is the normalized matrix mass in the chosen nontrivial
central active sector.  Hence every selected projection under that sector
satisfies

```text
tau(A_selected)
  <= (C_packet/c^2) E + C'_packet sqrt(E).                 (SPD5)
```

This would be stronger than the required one-step escape payment.  Conversely,
if the Maslov gap fails, tensoring the surviving projective microstates with
an exact inverse-twisted finite packet module and inducing over `O` produces
positive-density full-cell countermodels.  Therefore the only sound robust
recurrence lemma exposed by this smallest nonamenable candidate is the
all-dimensional mod-three Maslov sector gap itself.

DERIVATION
s3-packet-projective-neutrality-proof
