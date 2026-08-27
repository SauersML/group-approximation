---
rg: 2
id: two-reynolds-edges-absorb-selector-holonomy-at-one-range
kind: claim
title: Two Reynolds edges absorb the selector holonomy while retaining one common range
distinct_from:
  same-range-dressed-reynolds-sections-expose-raw-source-unitary: that positively reads a prescribed source dressing from two partial sections; this gives an exact finite marked countermodel showing that the resulting raw phase need not cause range mismatch or escape.
  existential-cycle-gauge-absorbs-square-and-reynolds-readouts: that treats an arbitrary chord gauge in a marginal commutant; this realizes the gauge by the concrete one-bit selector and two explicit HNN edge words.
  two-orientation-hnn-packet-prepays-escape: that sends one coarse source to distinct rank-one/rank-three oriented targets; this keeps the same Reynolds target and shows that even a nontrivial odd holonomy does not separate the ranges.
---

**ESTABLISHED EXACT SAME-RANGE COUNTERMODEL.**  Let `H<C` be the finite
pair used by an index-two Reynolds edge, let `e_C` be its source Reynolds
projection, and let `U` implement the HNN injection.  Adjoin the one-bit
selector involutions `p_a,q_a`, require them to commute with `C` and with
`U`, and put

```text
d_a=p_aq_a,          r_a=d_a^2=[p_a,q_a]
                   =J^(1-a(v))x_v.                    (TRH1)
```

Define two distinct ordinary edge words

```text
U_0=U p_a,                  U_1=U q_a.                 (TRH2)
```

Because both selector letters centralize the finite edge groups, `U_0` and
`U_1` satisfy exactly the same HNN covariance rows as `U`.  Their relative
external-multiplicity holonomy is the desired raw selector word:

```text
U_0^*U_1=p_aq_a=d_a.                                  (TRH3)
```

It carries a nontrivial cycle phase even globally:

```text
d_a^2=r_a,              [U_0,d_a]=[p_a,d_a]=r_a.       (TRH4)
```

On the forbidden carrier `E_a=P_(c,a)Q_-`, `(TRH4)` reads

```text
E_ad_a^2=JE_a=-E_a,
E_a[U_0,d_a]=JE_a.                                    (TRH5)
```

Thus central-square and commutator holonomy tests both see the correct odd
payload phase.

Nevertheless the two Reynolds transports have **identical final support**.
Since `p_a,q_a` commute with `e_C`,

```text
U_0 e_C U_0^*=U e_C U^*=U_1 e_C U_1^*.               (TRH6)
```

The same holds after compression to `E_ae_C`.  Consequently every
cross-range mismatch, join growth, and overlap-loss quantity is zero, even
though the relative phase in `(TRH5)` is maximally nontrivial.

This is an exact finite marked countermodel, not only a formal algebra
calculation.  Take the finite uniform-assignment/context model with
`tau(E_a)>0`, the Pauli selector realization, and any finite packet model of
the Reynolds edge; amplify so the source/target subgroup restrictions agree.
Let the base HNN implementer act trivially on the selector factor.  Then
`(TRH1)--(TRH6)` hold exactly and the marked sign survives.  In the perfect
tracial BCS model use the same Pauli construction; `E_a=0`, so every
payload-corner condition is vacuous and completeness is preserved.

The obstruction persists after adjoining any finite list of relations in the
relative word `U_0^*U_1`, its powers, its commutators with selector letters,
or finite Reynolds averages **which is satisfied by this finite selector
packet model**.  Such readouts live entirely in the external selector
multiplicity algebra, while `(TRH6)` remains unchanged.  A readout not
satisfied there may of course exclude the countermodel, but then its
perfect-model consistency and payload sensitivity are the new load-bearing
assertions.  Fixed packet exactification gives the same conclusion with
`O(sqrt(E_pres))` errors in approximate models.

Therefore the next relation cannot merely prescribe an odd holonomy between
two Reynolds edges.  It must compare a **noncentral target-support
observable** not fixed by the common selector gauge, or force the two edges
to land in genuinely different target character atoms.  The latter returns
to the finite regular-packet compensation of
`two-orientation-hnn-packet-prepays-escape`; phase alone does not pay it.

DERIVATION
selector-dressed-two-hnn-same-range-proof
