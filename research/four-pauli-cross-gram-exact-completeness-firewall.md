---
rg: 2
id: four-pauli-cross-gram-exact-completeness-firewall
kind: claim
title: A positive cross-Gram contraction cannot exactly intertwine one qubit with two transverse qubits
distinct_from:
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that compares two four-tuples which are already placed on one common carrier; this gives the direct residual floor for an arbitrary positive-mass contraction between them.
  compulsory-pauli-cross-gram-is-four-word-intertwiner: that asks the local packet to manufacture the four intertwiners; this proves that exact manufacture is incompatible with the packet's positive overlap.
  atlas-kernel-relators-couple-cross-gram-to-four-pauli: that retains a finite-matrix-only extraction target; this rules out interpreting that target as an ordinary quotient-algebra or relator-ideal consequence.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial von Neumann algebra and
let `T in M` be a contraction.  Let `C_1,...,C_4` be contractions contained
in one degree-two factor `M_2 tensor I`, and let `D_1,...,D_4` be unitaries.
Suppose, for a unitary `W`,

```text
||s4(D_1,D_2,D_3,D_4)-8W||_2 <= epsilon.              (PCF1)
```

Then

```text
sum_(j=1)^4 ||D_j T-T C_j||_2
 >= (8||T||_2-epsilon)/24.                            (PCF2)
```

In particular, for the exact transverse Pauli tuple

```text
D=(X tensor 1,Z tensor 1,1 tensor X,1 tensor Z),
```

one has `epsilon=0`.  If the compulsory Atlas orientation satisfies

```text
||T||_2^2 >= 5/64,
```

then

```text
sum_j ||D_jT-TC_j||_2 >= sqrt(5)/24,                  (PCF3)
sum_j ||D_jT-TC_j||_2^2 >= 5/2304.                   (PCF4)
```

Thus no positive compulsory cross-Gram contraction can exactly carry all
four occurrences from one literal degree-two factor to the transverse
two-qubit packet.  This is independent of external multiplicity.

The consequence for the regular Atlas is an exact-completeness firewall.
The canonical quotient representation satisfies every kernel relation and
retains the fixed raw/comb cross-Gram moments.  Therefore no fixed
group-algebra identity, coefficient-ideal certificate, or van Kampen
telescoping argument can make the four residuals vanish from kernel defect
alone while also supplying the degree-two source and transverse target on
that overlap.  Such an identity would hold in the exact quotient model and
contradict `(PCF3)`.

This does not refute a genuinely finite-matrix-only extraction.  A proof may
use finite coordinate rank, multiplicity balance, or matrix-integrality to
choose a source factor/carrier which has no counterpart in the exact regular
von Neumann model.  The firewall says that this finite-only operation is
load-bearing; it cannot be replaced by an algebraic consequence of the
kernel relators.
