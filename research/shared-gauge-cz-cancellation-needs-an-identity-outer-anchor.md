---
rg: 2
id: shared-gauge-cz-cancellation-needs-an-identity-outer-anchor
kind: claim
title: A shared gauge cancels CZ exactly only through an identity-outer anchor
distinct_from:
  packet-dressed-shared-implementer-requires-one-outer-class: that classifies which packet-dressed gates can share one implementer; this specializes the classification to the fine-prefix CZ, proves the occurrence-parity obstruction for every bounded product/cycle/commutator, and gives the exact HS support-row endpoint if an identity-outer anchor is supplied by another mechanism.
  second-layer-lookup-cancellation-no-go: that is a universal free-product obstruction for arbitrary lookup words; this uses the Pauli outer-automorphism quotient and gives an explicit balanced multiplicity-involution countermodel for CZ support and oriented-trace proposals.
  controlled-pauli-corner-has-clifford-groupification: that produces `CZ tensor V`; this determines exactly what additional shared-gauge word would remove `V` and why the existing covariance packet cannot produce it.
  unitary-offdiagonal-block-gram-is-support-leakage: that turns a literal fine reflection into the terminal trace estimate; this audits whether several twisted Clifford occurrences can manufacture that reflection.
---

**ESTABLISHED.**  Let `P` be the two-qubit extraspecial Pauli group and let
`alpha` be the non-inner involutive automorphism induced by the fine-atom
controlled-Z `C`.  On a marked spin isotypic component every covariance
implementer has the form

```text
T=C tensor V,                                             (SGC1)
```

with an arbitrary multiplicity involution `V`.

There is a bounded positive cancellation if one has an additional
**identity-outer anchor with the same gauge**:

```text
A=I tensor V.                                             (SGC2)
```

Then exactly

```text
T A=C tensor I.                                           (SGC3)
```

Robustly, if exactification gives

```text
||T-C tensor V||_2<=eta_T,
||A-I tensor V||_2<=eta_A,                               (SGC4)
```

then

```text
||TA-C tensor I||_2<=eta_T+eta_A.                        (SGC5)
```

Consequently, writing `C=R_f` for the fine carrier reflection, the ordinary
word

```text
D=T A J_x R_e J_x^*                                     (SGC6)
```

satisfies the dimension-free endpoint

```text
tr(P_carrier)
 <=(||D-1||_2+eta_T+eta_A)^2.                           (SGC7)
```

This follows immediately from
`unitary-offdiagonal-block-gram-is-support-leakage`.  Thus a same-gauge
identity-outer anchor would solve the first coarse-to-fine support row with
one fixed product word.

## Why repeated existing Clifford occurrences cannot supply the anchor

Let `u` be the stable letter implementing `alpha`.  Every occurrence which
is forced to carry the same multiplicity gauge by packet dressing has form

```text
u_i=h_i u k_i,                  h_i,k_i in P.            (SGC8)
```

For a word `W` in `P` and these occurrences, let `nu(W) in Z/2` be its total
stable-letter occurrence parity.  On the spin component,

```text
rho(W)=C_W tensor V^(nu(W)),
[Ad(C_W)]=[alpha]^(nu(W)) in Out(P).                    (SGC9)
```

The two desired cancellations are therefore inseparable:

- if `nu(W)=0`, the multiplicity gauge cancels, but the outer class is
  trivial, so `C_W` is a packet-inner operator and cannot be `C`;
- if `nu(W)=1`, the label operator lies in the CZ outer class, but the
  arbitrary factor `V` remains.

In particular every product with an even number of shared-gauge CZ
occurrences, every commutator, and every closed balanced cycle erases both
`V` and the CZ outer action.  An odd product retains both.  Packet dressing
cannot give `(SGC2)`, because it never changes the outer class of `u`.

The obstruction is visible in normalized HS norm, not only algebraically.
Take

```text
V=diag(I_m,-I_m).                                        (SGC10)
```

Every odd-occurrence word has a balanced multiplicity twist and remains at
squared normalized distance `2` from the same label operator tensored with
the identity.  Its trace is zero whenever tested through the multiplicity
factor.  Even-occurrence words have no twist, but their conjugation action
on `P/Z(P)` is trivial, whereas CZ acts by the nontrivial symplectic
transvection `alpha`.  Hence products, commutators, and finite oriented-trace
combinations of the existing shared-gauge occurrences admit exact
countermodels.

## Surviving construction target

The positive word `(SGC6)` shows exactly what a new two-cell must do: couple
one CZ-outer implementer and one identity-outer implementer to the **same**
multiplicity involution.  Ordinary packet dressing cannot relate different
outer classes, and a finite covariance graph permits independent gauges.
Thus authenticating `(SGC2)` is not a further word-balancing exercise; it is
the genuine multiplicity holonomy/same-reservoir relation.

