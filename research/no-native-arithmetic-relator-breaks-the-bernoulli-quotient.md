---
rg: 2
id: no-native-arithmetic-relator-breaks-the-bernoulli-quotient
kind: claim
title: No native arithmetic relator can break the coset Bernoulli quotient
distinct_from:
  native-sl3-group-is-hecke-graph-wreath-product: that identifies the native group as a graph wreath product; this takes its complete-lamp quotient and proves a universal obstruction to relator-only Cartan/PVM extraction.
  p3-denominator-steinberg-word-is-multiplicity-blind: that checks one denominator-conjugated Chevalley triangle on one oscillator packet; this simultaneously covers every genuine native mixed-root, section, and conductor word because they all survive one exact quotient.
  global-schreier-pvm-is-stronger-than-action-soficity: that gives an exact Bernoulli PVM firewall once the crossed product is present; this proves that the Bernoulli model is an algebraic quotient of the actual native graph-wreath presentation and isolates the first canonical-trace datum which does not survive it.
  native-forty-two-shell-has-a-noncommuting-pair: that exhibits one nonedge pair and rules out a Boolean Fourier decoder in the native regular model; this identifies its commutator as an anti-relation rather than a missing presentation relator.
---

ESTABLISHED. Put

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),       X=A/C,
G_cc=(graph_product_(x in X) C_2) rtimes A,             (NBR1)
```

where the graph is the native Hecke orbital graph. There is a canonical
surjection, identical on the actor,

```text
q:G_cc -> W_ab=(direct_sum_(x in X) C_2) rtimes A,      (NBR2)
```

obtained by imposing the missing lamp commutators. Consequently **every**
genuine group-word relation of the native arithmetic presentation holds in
`W_ab`. This includes all actor Steinberg/root relations, all fixed coset
section identities `a_i=b_i d_i`, every conductor word in the actor, the
native stabilizer and Hecke-edge lamp relations, and every consequence made
by mixing these relations.

The group von Neumann algebra of `W_ab` is the exact coset Bernoulli crossed
product

```text
L(W_ab)=L^infinity({+-1}^X) rtimes A.                   (NBR3)
```

Thus no additional native mixed-root or conductor **relator** absent from
the Bernoulli model exists. In particular there cannot be a finite-tracial
inequality of the form

```text
site-PVM covariance energy
 <=K(native presentation + mixed-root + conductor defect), (NBR4)
```

for a complete finite Bernoulli-lamp site decoder: the right side is zero
in `(NBR3)`, while
`finite-bernoulli-site-decoder-has-schreier-error-floor` makes the left side
at least `2 gamma`.

The first datum that distinguishes the canonical regular packet from this
quotient is not a relation but a regular-character **anti-relation**. Let

```text
kappa=[c_(hC),c_(h^(-1)C)]
      =[h c_C h^(-1),h^(-1)c_C h].                    (NBR5)
```

The two vertices are a nonedge, so `kappa!=1` in `G_cc`, whereas
`q(kappa)=1`. Hence

```text
tau_(G_cc)(kappa)=0,             tau_(W_ab)(q(kappa))=1, (NBR6)
```

and canonical regular microstates require

```text
||rho(kappa)-I||_2^2 ->2.                              (NBR7)
```

This is the minimal fixed shell seam that excludes the Bernoulli quotient.
It is a prescribed large separation, not a small word defect, and therefore
cannot be inserted into the old defect ledger under the name of a new
mixed-root relation.

Nor does the scalar condition `(NBR6)` alone imply the atomwise section
leakage `(EDA11)`. The independent-refinement construction in
`independent-chart-refinement-forces-eda-leakage` tensors every raw
conductor/root operator by the identity and puts the chart labels on an
independent factor. This preserves the trace of `kappa` (and of any fixed
finite list of raw words) while keeping the `41/42` EDA leakage floor.
Therefore the surviving positive target is sharper: use the nonedge
regular-character separation to construct the chart atoms **functorially
from the same raw packet**, or prove a matrix-only exclusion of the
Bernoulli crossed product. Adding more relators or scalar word moments to
the marginal EDA ledger does not provide that coupling.

Scope: `(NBR3)` is an exact finite-tracial countermodel. Its Connes
embeddability for this nonamenable-stabilizer action is open. Accordingly
the claim rules out tracial/SOS and relator-only proofs; a genuinely
finite-matrix inequality could evade it only by proving the corresponding
Bernoulli crossed product non-Connes-embeddable, which is already a terminal
nonhyperlinearity-strength result rather than a routine extraction lemma.
