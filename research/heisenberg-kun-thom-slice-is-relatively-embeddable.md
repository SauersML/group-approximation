---
rg: 2
id: heisenberg-kun-thom-slice-is-relatively-embeddable
kind: claim
title: The minimal noncommuting Kun--Thom compressor slice is relatively embeddable
distinct_from:
  commuting-kun-thom-compressors-are-relatively-embeddable: that treats directed N^m telescopes for commuting external matrices; this treats the first noncommuting pair and uses an Ore Heisenberg monoid
  one-kun-thom-compressor-is-relatively-embeddable: that treats one ascending-HNN direction; this includes two stable directions and their nontrivial central commutator relation
  sofic-coset-action-makes-amalgam-double-sofic: that is conditional on a sofic coset action; this proves the hypothesis for the concrete minimal nonabelian compressor subgroup
  coordinate-action-not-sofic: that concerns the full Kun--Thom action; this shows its failure is not visible in the standard two-generator Heisenberg slice
---

Use the regular finite-field Kun--Thom group with `d>=3`, and set

```text
A=I+E_12,       B=I+E_23,       C=[A,B]=I+E_13,
P=<Gamma,(1,A),(1,B)>.
```

Then:

1. the coset action `P action P/Gamma` is sofic;
2. the double `P *_Gamma P` is sofic;
3. `L(Gamma) subset L(P)` is relatively embeddable over the scalars.

Thus the first noncommuting positive compressor pair is still on the positive
side of the Kun--Thom relative-embeddability gate.

The external group `Q=<A,B>` is the integral Heisenberg group.  Its positive
compressor monoid becomes left Ore after including the already generated
central commutator:

```text
S=<A,B,C>_+
 ={C^r B^q A^p:p,q,r in N}.                                  (HKS1)
```

Any finite collection of levels `s^(-1) Gamma s`, and any finite collection
of external denominators, has one common level because elements of `S` have
common left multiples.  At that level, every site stabilizer is conjugate to

```text
s Gamma s^(-1)=EL_r(k[s N^d])
```

for some `s in S`, a subgroup separable in `Gamma` by finite monomial
truncation.  This makes the telescope-kernel action sofic.

Finally use the Heisenberg central series

```text
{1} < <C> < <C,A> < Q,
```

whose successive quotients are infinite cyclic.  Cyclic-extension permanence
for sofic actions adjoins `C`, then `A`, then `B`.  The general
coset-difference embedding then makes the double sofic and Gao's criterion
gives `RE/C`.

This does not treat arbitrary noncommuting positive matrices.  The exact
feature used here is the Ore property of the positive Heisenberg monoid.
Consequently the surviving finite-slice gate is pushed beyond both abelian
compressor families and this first nilpotent nonabelian family, toward
non-Ore or non-solvable compressor coherence.

DERIVATION
ore-heisenberg-telescope-coset-action-proof
