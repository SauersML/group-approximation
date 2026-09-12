---
rg: 2
id: leavitt-balanced-corners-separated-modulo-four
kind: claim
title: The trace-balanced Leavitt corners are separated by their modulo-four lifts
distinct_from:
  group-algebra-coefficient-trace-separates-leavitt-corners: that separates the earlier pair already over F_2; this separates the newer pair whose entire F_2 cocenter vanishes.
  leavitt-trace-balanced-nested-idempotents: that correctly computes the characteristic-two traces; this recovers a lost invariant after lifting the coefficient ring.
  lifted-trace-detects-finite-subgroup-projectives: that treats all finite-subgroup projectives and all primes; this gives explicit modulo-four lifts and refutes the designated Leavitt module-equivalence target.
---

Let S=F_2[Q] and let e=[g]+[g^(-1)], c=[h]+[h^(-1)], f=ec be the
pair of `leavitt-trace-balanced-nested-idempotents`. Then

    eS is not isomorphic to fS.

Indeed their classes differ in K_0(S), with lifted trace difference
2/9 in Z_2. Thus no common projective stabilization repairs the
equivalence.

There is already an elementary obstruction over (Z/4)[Q]. With
g,h independent commuting elements of order three, put

    E=2[1]+[g]+[g^2],
    C=2[1]+[h]+[h^2],
    F=EC.

These are idempotent lifts of e,c,f, and their identity coefficients
satisfy T(E)=2, T(F)=0 modulo four. Any equivalence of e and f would
lift through the square-zero ideal 2(Z/4)[Q], contradicting cyclicity
of T. The obstruction allows arbitrary ambient support for the proposed
intertwiners.

Consequently the implication through
`nested-idempotent-padding-refutes-direct-finiteness` has a false
prerequisite. Neither direct finiteness of S nor surjunctivity of Q is
settled by this refutation.
