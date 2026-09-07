---
rg: 2
id: finite-subgroup-corners-have-invariant-basis-number
kind: claim
title: Every nonzero finite-subgroup projective corner has invariant basis number in the ambient modular group algebra
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that constructs a lifted trace and detects finite-subgroup projective classes; this applies their infinite additive order to all rectangular inverse relations and refutes the proposed full Leavitt-family lift.
  augmentation-blocks-unital-leavitt-family: that uses a scalar augmentation or a map to a domain; this also applies to finite-subgroup corners of augmentation zero.
  leavitt-balanced-corners-separated-modulo-four: that compares two designated nested projectives; this excludes unequal finite numbers of copies of a single finite-subgroup projective, with arbitrary ambient intertwiners.
---

Let p be prime, H <= G finite, and 0 != e in M_k(F_p[H]) idempotent.
Put S=F_p[G] and T=e M_k(S) e, with identity e. Then T has invariant
basis number:

    T^m ~= T^n as right T-modules  => m=n.               (FIB1)

Equivalently, no rectangular matrices X in M_(m,n)(T) and
Y in M_(n,m)(T) can satisfy XY=I_m, YX=I_n when m!=n.
In particular, no unital Leavitt algebra L_(F_p)(m,n), m!=n,
maps to T. This holds at every matrix size and permits arbitrary
G-support for all entries of X,Y.

For the designated order-three corner e=[g]+[g^2] in
F_2[L_(F_2)(1,2)^x], the lifted trace is 2/3. Hence there are no
S_0,S_1,T_0,T_1 in eSe satisfying

    T_i S_j=delta_ij e,       S_0 T_0+S_1 T_1=e.

Thus `binary-leavitt-family-lifts-into-unit-corner` is false even
without its extra conditions on the evaluation images, and the unital
corner evaluation onto the binary Leavitt algebra has no ring section.

This does not assert that T is directly finite. A single one-sided
inverse has a zero-class defect and need not identify unequal numbers
of copies of eS^k. That weaker construction remains open here.
