---
rg: 2
id: titz-witzel-regular-packets-collapse-mark
kind: claim
title: Regular nonabelian fibre packets cannot tile a positive Titz--Witzel model
distinct_from:
  titz-witzel-central-square-lifts-collapse-mark: That excludes abelian and central-square voltage lifts; this allows arbitrary finite nonabelian packet groups and proves that regularity itself quantizes the relator defects too strongly.
  titz-witzel-sparse-defect-needs-dense-generator-surgery: That rules out small edge edits from a union of arbitrary exact finite actions; this directly treats unions of inexact regular voltage packets and charges every marked packet to a failed relator component.
---

**THEOREM.**  In the C2-block system `(TWC1)--(TWC6)`, suppose that

```text
X=disjoint_union_(j in J) F_j
```

for finite groups `F_j`, and that `P,Q` preserve every `F_j` and restrict
there to left translations by elements `p_j,q_j in F_j`.  Let
`delta_c,delta_0,delta_P,delta_J` be the normalized Hamming defects on
`Omega=X times C2` of the four relators in `(TWC5)`, and put
`mu=d_Omega(u^8,1)`.  Then

```text
mu <= 2(delta_c+delta_0+delta_P+delta_J).                 (TWR1)
```

The same conclusion holds whenever each packet carries a free action of a
finite group and `P,Q` are supplied by elements of that group.

Consequently no sequence of disjoint regular nonabelian group packets can
have all four defects tend to zero while retaining a positive marked
limsup.  A positive nonabelian-fibre construction must instead use nonfree
fibre actions, in which nonidentity voltages can have small support, or use
seams which cut through the proposed packets.  Passing from abelian to
nonabelian regular fibres alone does not escape the gate.

---

### Proof

titz-witzel-regular-packets-collapse-mark-proof
