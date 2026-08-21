---
rg: 2
id: canonical-iwahori-projection-commutant-transfer
kind: claim
title: Canonical Iwahori microstates transfer positive-density projection centralizers between the two vertices
distinct_from:
  iwahori-unitary-commutant-transfer: that asks for a modulus over every pair of exact finite-dimensional vertex representations and every unitary; this only asks for projection transfer along sequences whose induced amalgam character is the regular character, exactly the case supplied by canonical microstates of the HNN witness.
  iwahori-local-global-defect-question: that repairs arbitrary almost-compatible vertex representations to a compatible representation; this neither repairs the representations nor treats noncanonical characters.
---

OPEN.  Put

```text
A=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-,
C_+=C_-=SL_2(Z),
```

with the index-three Iwahori edge isomorphism `sigma`.  Let
`pi_(n,+),pi_(n,-):C -> U(d_n)` be exact representations whose edge defects
tend to zero.  Evaluate fixed amalgam normal forms using these two
representations, obtaining asymptotic homomorphisms `Phi_n:A->U(d_n)`, and
assume the canonical trace condition

```text
tr_(d_n)(Phi_n(g)) -> delta_(g,1)       for every g in A.             (CIP1)
```

Prove that every sequence of projections `p_n in M_(d_n)` satisfying

```text
max_(c in S_C)||[p_n,pi_(n,+)(c)]||_2 ->0                            (CIP2)
```

also satisfies

```text
max_(c in S_C)||[p_n,pi_(n,-)(c)]||_2 ->0.                           (CIP3)
```

It is enough to prove this when
`min(tr(p_n),1-tr(p_n))` is bounded below:
`iwahori-transfer-failure-reduces-to-two-block-projection` replaces every
unitary failure by a projection failure after harmless doubling, and
`iwahori-transfer-failure-has-two-positive-density-blocks` proves that both
blocks then have uniformly positive normalized rank.

In a tracial matrix ultraproduct, `(CIP1)` says that the induced homomorphism
extends to a trace-preserving embedding `L(A)->M_omega`.  The endpoint is the
lift-conditioned relative-commutant assertion

```text
rho(C_+)' intersect M_omega = rho(A)' intersect M_omega              (CIP4)
```

tested only on projections and only for embeddings whose two vertex
restrictions lift to exact matrix representations.  This is strictly weaker
than arbitrary Iwahori repair and strictly weaker than
`iwahori-unitary-commutant-transfer`.

## Exact remaining carrier

A counterexample must now exhibit projections of positive normalized rank
and corank which are asymptotically reducing for the first exact vertex but
are mixed by the second vertex by a fixed amount, while the two Iwahori edge
representations agree asymptotically and the amalgam character remains
regular.  Vanishing-rank outliers, scalar multiplicity unitaries, and
noncanonical finite-dimensional characters cannot refute this endpoint.
