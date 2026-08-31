---
rg: 2
id: opposite-transvections-are-first-nonore-relative-gate
kind: claim
title: Opposite transvections isolate the first non-Ore relative-embedding gate
distinct_from:
  heisenberg-kun-thom-slice-is-relatively-embeddable: that proves the adjacent-root noncommuting pair positive using an Ore nilpotent monoid; this treats the opposite-root pair whose positive monoid is free and non-Ore
  commuting-kun-thom-compressors-are-relatively-embeddable: that treats commuting pairs; this is the remaining standard elementary two-compressor type
  kt-q2-double-hyperlinear-iff-relative-embeddable: that states the full Kun--Thom equivalence; this proves the analogous exact equivalence and the finite-model firewalls for the smaller opposite-root slice
  kt-pair-group-double-is-nonsofic: that proves nonsoficity when the ambient vertex group is Kazhdan; the opposite-root vertex has an SL2(Z) quotient and is not Kazhdan, so that theorem does not decide it
---

Take `d>=3` and the opposite positive transvections

```text
A=I+E_12,       B=I+E_21,       P=<Gamma,(1,A),(1,B)>.
```

Put

```text
R_pm=k[x_1^(+-1),x_2^(+-1),x_3,...,x_d],
E_pm=EL_r(R_pm).
```

Then the following structural statements hold.

1. `<A,B>=SL_2(Z)` in the upper-left block, and

   ```text
   P=E_pm rtimes SL_2(Z).                                      (OTG1)
   ```

2. The positive monoid `<A,B>_+` is the free monoid on `A,B`.  In
   particular, `A` and `B` have no common left multiple, so the directed
   Ore-telescope proofs for commuting and Heisenberg slices cannot apply.

3. For every homomorphism `pi:P->F` to a finite group,

   ```text
   pi(Gamma) normal pi(P).                                     (OTG2)
   ```

   Hence every element of `E_pm` maps into `pi(Gamma)).  In particular
   `Gamma` is not separable in `P`, and literal finite-quotient Schreier
   models cannot approximate `P/Gamma` faithfully.

4. With `D=P *_Gamma P`,

   ```text
   D hyperlinear
   iff L(Gamma) subset L(P) is RE/C.                            (OTG3)
   ```

   If the coset action `P action P/Gamma` is sofic, then `D` is even
   sofic by the coset-difference embedding theorem.

Statements 1--4 do **not** decide whether the opposite-pair coset action is
sofic or whether (OTG3) holds.  They show exactly why neither neighboring
argument decides it: non-Ore destroys the common-level construction;
finite-image models collapse the Laurent kernel; and Kun--Thom's nonsofic
double theorem requires the ambient vertex group to have property (T), while
`P` surjects onto `SL_2(Z)`.

For the standard elementary positive compressors in rank three, this is the
only unresolved two-generator type.  Disjoint/root-commuting pairs are covered
by the commuting theorem, and adjacent-root pairs by the Heisenberg theorem.
On the other side, the three-cycle

```text
I+E_12,       I+E_23,       I+E_31
```

generates `SL_3(Z)`; for `d=3` its slice is the full Kun--Thom vertex
group.  Its coset action and group double are nonsofic, while its `RE/C`
status remains the original hyperlinearity problem.  Thus the standard
elementary-compressor atlas is bracketed sharply:

```text
one direction: positive;
two directions: positive except the opposite-root gate above;
three cyclic directions: already the full nonsofic action/double.
```

DERIVATION
opposite-sl2-cone-and-three-cycle-boundary-proof
