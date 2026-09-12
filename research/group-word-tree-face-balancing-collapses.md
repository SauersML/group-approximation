---
rg: 2
id: group-word-tree-face-balancing-collapses
kind: claim
title: Group-word multiplicative balancing of both tree faces collapses to one kernel conjugation
artifacts:
  - research/artifacts/caprace-muehlherr-maximal-bounded-ucp-audit-2026-08-25.md
distinct_from:
  kernel-inner-tree-face-balancing-collapses: that starts by assuming the two tree-face embeddings are kernel conjugates and verifies the collapse in one explicit A2-A2 triangle; this gives a Bass-Serre criterion forcing every group-word-valued multiplicative lift of either tree face to have that form before applying the same collapse.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that rules out a small correction of the canonical tree-face values for arbitrary ucp maps; this permits arbitrarily large group-word motion and rules it out by classifying the finite subgroup lifts.
  triangle-relator-extension-admits-local-ucp-sections: that permits genuinely nonmultiplicative ucp restrictions and remains open; this eliminates the larger class in which both finite tree-face restrictions are star homomorphisms whose canonical group unitaries remain group unitaries.
---

**ESTABLISHED (and unconditional at the `(3,3,4)` instance).**  Use the
triangle notation

```text
G_0=P_12 *_(P_2) P_23,       K=ker(G_0 ->> Lambda),
A_0=C^*(G_0),                S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13).
```

Assume the following finite-subgroup rigidity conditions:

```text
(GW1) P_12 and P_23 are nonconjugate maximal finite subgroups of Lambda;
(GW2) N_Lambda(P_12)=P_12 and N_Lambda(P_23)=P_23;
(GW3) K intersect C_(G_0)(P_2)={1}.                         (GW)
```

Then there is no ucp map `Phi:S_Delta->A_0` such that, for
`ij in {12,23}`,

```text
Phi|_(C^*(P_ij)) is a unital star homomorphism and
Phi(u_g) is a group unitary of G_0 for every g in P_ij.     (GW4)
```

Here `Phi` is also required to be a lift on the two tree faces, as every
candidate local section is:

```text
q_* Phi(u_g)=u_g,                 g in P_12 union P_23.     (GW5)
```

Indeed `(GW4)` gives group homomorphisms
`alpha_ij:P_ij->G_0` with `q alpha_ij=id`.  Bass--Serre finite-subgroup
rigidity, maximality, nonconjugacy and self-normalization force

```text
alpha_ij=Ad(k_ij)|_(P_ij)       for some k_ij in K.         (GW6)
```

Agreement of the two restrictions on `C^*(P_2)` implies
`k_23^(-1)k_12 in K intersect C_(G_0)(P_2)`, so `(GW3)` gives one common
`k`.  Conjugating `Phi` globally by `u_k^*` makes both tree faces canonical,
contradicting `three-face-ucp-balancing-needs-macroscopic-tree-motion`.

Proof: `group-word-tree-face-lift-classification-proof`.

The hypotheses are not merely formal.  They hold for the explicit
`(3,3,4)` Kac--Moody triangle in
`kernel-inner-tree-face-balancing-collapses`.  Caprace--Muehlherr's
classification of maximal bounded subgroups, together with their theorem
that bounded equals finite over a finite field, makes each maximal spherical
rank-two Levi a maximal finite subgroup.  Its unique stabilized pair of
opposite maximal spherical residues makes it self-normalizing, and distinct
residue types make `P_12` and `P_23` nonconjugate.  These properties pass to
the centre-free quotient.  Finally `(IK5)` of the cited node gives `(GW3)`.
Thus the no-go applies to that concrete simple Kazhdan lattice, with no
unverified group-theoretic hypothesis left there.

**What remains.**  This strictly enlarges the inner-gauge no-go: the
conjugators are not part of the hypothesis but are forced from the apparently
more flexible group-word-valued face homomorphisms.  It still does not decide
local ucp splitting.  A successful balance may send finite-face generators
to non-group unitaries, or may leave the multiplicative domain altogether.
Thus the surviving correction in
`finite-relator-reservoir-repairs-every-fd-packet` must be genuinely operator
algebraic on at least one tree face; changing group-word lifts, even by long
kernel words chosen separately on the two sides, cannot work whenever
`(GW1)--(GW3)` hold.

DERIVATION
group-word-tree-face-lift-classification-proof
