---
rg: 2
id: controlled-pauli-commutator-robustly-measures-projection-overlap
kind: claim
title: A gauge-free controlled Pauli commutator robustly measures projection overlap
artifacts:
  - research/controlled-pauli-overlap-identity-and-gauge-lock-proof.md
distinct_from:
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that gives the commuting-projection AND identity and exposes the external commutator; this gives the exact normalized-Hilbert--Schmidt formula for arbitrary projections and a dimension-free overlap decoder.
  controlled-pauli-corner-has-clifford-groupification: that groupifies one covariance but leaves an arbitrary multiplicity involution; this states precisely what a successful shared gauge lock would buy for the full SynchBCS compiler.
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that rules out a fixed finite selector overgroup; this cell is a conditional infinite/shared-payload interface and does not claim that the controlled form is forced by a finite group.
---

**ESTABLISHED ROBUST CELL; MULTIPLICITY LOCK OPEN.**

Let \((M,\tau)\) be a finite tracial von Neumann algebra and let \(p,q\)
be arbitrary projections. On \(M_2(M)\), with normalized tensor trace, put

\[
 U_p=I_2\otimes(1-p)+X\otimes p,\qquad
 V_q=I_2\otimes(1-q)+Z\otimes q,                        \tag{CPO1}
\]

where \(X,Z\) are the Pauli reflections. Write
\([U,V]_g=UVU^{-1}V^{-1}\) for the group commutator and
\([p,q]=pq-qp\) for the additive commutator. Then

\[
 \|[U_p,V_q]_g-I\|_2^2
   =4\|pq\|_2^2+2\|[p,q]\|_2^2.                         \tag{CPO2}
\]

Consequently

\[
 [U_p,V_q]_g=I
 \quad\Longleftrightarrow\quad pq=qp=0,                 \tag{CPO3}
\]

and, quantitatively,

\[
 \|pq\|_2\leq\frac12\|[U_p,V_q]_g-I\|_2.                \tag{CPO4}
\]

The estimate is stable under approximate controlled-form rounding. If
reflections \(U,V\) satisfy

\[
 \|U-U_p\|_2\leq\alpha,\qquad
 \|V-V_q\|_2\leq\beta,\qquad
 \|[U,V]_g-I\|_2\leq\eta,
\]

then

\[
 \|pq\|_2\leq\frac12(\eta+2\alpha+2\beta).              \tag{CPO5}
\]

Thus a gauge-free controlled-form theorem would compile every forbidden
overlap of the perfect independent-set SynchBCS by one ordinary group
commutator, with a dimension-independent reverse estimate. Pairwise use
inside one question, together with the group-word parity equation for the
decoded reflections \(1-2p_{i,v}\), would also recover the exact PVM
partition.

The word **gauge-free** is load-bearing. Finite packet covariance forces
only

\[
 U_p=C_X(p)A,\qquad V_q=C_Z(q)B
\]

with arbitrary multiplicity unitaries \(A,B\). Their commutator contains
the external factor \([A,B]\), which can cancel the Pauli overlap phase at
zero defect. Fixed finite Clifford couplings cannot remove all such
sectors. Therefore (CPO2) solves the analytic NAND decoder after controlled
rounding, but not the shared multiplicity lock needed to make that rounding
universal.

A surviving source-dependent cyclic compiler may use (CPO2) only if its
cross-context relations force the relevant multiplicity gauges to commute,
or otherwise make their commutator independently observable, on every
marked approximate representation. No such lock and no nonhyperlinear
group is claimed here.

DERIVATION
controlled-pauli-overlap-identity-and-gauge-lock-proof
