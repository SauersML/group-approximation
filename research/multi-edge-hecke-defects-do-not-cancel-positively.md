---
rg: 2
id: multi-edge-hecke-defects-do-not-cancel-positively
kind: claim
title: Multi-edge Hecke defects do not cancel positively, and exact compressed cycles force every edge to reduce
artifacts:
  - research/multi-edge-hecke-balance-and-cycle-rigidity-proof.md
distinct_from:
  single-nonreducing-hecke-transport-cannot-carry-a-complete-context: that treats one transported PVM; this proves the multi-edge convex, outcome-gated, and cyclic balance laws.
  finite-sheet-transport-networks-are-exactly-matricial: that treats permutation sheets globally; this derives the local finite-trace identities and exhibits the smallest S4 and dihedral absorbers.
  five-clifford-odd-orbit-cancels-phase-not-payload: that concerns a product before corner compression; this rules out repairing leakage by a product of compressed edges.
---

Let Q be a projection in a finite tracial von Neumann algebra.

For edge i, let U_i be unitary and let P_(i,v) be a PVM summing to Q.
The compressed transported context has positive deficit
```text
sum_v Q U_i P_(i,v) U_i^*Q
 =Q-D_i,
D_i=Q U_i(1-Q)U_i^*Q>=0.                               (MHB1)
```
Hence a positive convex combination of complete transported contexts can
equal Q only when every D_i=0, equivalently every U_i reduces Q.
Positive off-corner mass never cancels across edges.

Outcome-dependent routing is possible, but has a sharper balance.  If
P_1+...+P_k=Q and
```text
sum_i Q U_i P_i U_i^*Q=Q,
```
then
```text
||(1-Q)U_iP_i||_2=0                   for every i.        (MHB2)
```
Thus each selected slice lands wholly inside Q.  Different edges may
leak on unused slices, but no used leakage is compensated.

Nor can a sequential cycle hide the defect.  If
```text
(QU_1Q)(QU_2Q)...(QU_kQ)
```
is unitary in QMQ, then every QU_iQ is unitary, and therefore every U_i
reduces Q.  This follows from the elementary fact that a product of
contractions can be unitary in a finite von Neumann algebra only when
every factor is unitary.

The boundary is exact and finite:

- In S_4, two nonnormal edges have complementary full defects P_+ and
  P_-, while outcome gating routes P_+ and P_- with zero slice leakage
  and gives a complete Q-corner PVM.  This is a finite controlled router.

- Coherent amplitude interference can cancel before positivity is formed.
  In the faithful two-dimensional block of the dihedral group of order
  16,
  ```text
  Q=(I+Z)/2,
  U_1=H, U_2=ZH,
  2^(-1/2)(U_1+U_2)Q=Q,
  ```
  even though both individual off-corner blocks are nonzero.  This is an
  additive finite-matrix identity, not a compressed group-word cycle.

Therefore multiple nonnormal edges do not provide a positive-defect or
cycle loophole.  The only escapes are zero-leak outcome gating and
coherent group-algebra interference, both already finite-dimensional.
A viable compiler must couple such an absorber to a separate
infinite-only trace obstruction; the Hecke network itself cannot supply
one.
