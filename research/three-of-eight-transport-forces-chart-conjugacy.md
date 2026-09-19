---
rg: 2
id: three-of-eight-transport-forces-chart-conjugacy
kind: claim
title: Literal transport of a three-of-eight projection conjugates the whole Boolean chart
artifacts:
  - research/artifacts/three-of-eight-heisenberg-transport-audit-2026-08-21.md
distinct_from:
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that induces a forbidden selector character through a finite or residually finite overgroup; this assumes the desired coarse projection is transported exactly and proves, without finiteness or residual finiteness of the ambient group, that one literal transporter must conjugate the entire context subgroup.
  heisenberg-subgroup-cuts-are-affine-stabilizer-flats: that classifies a coarse projection which is itself one subgroup-character cut; this treats the genuinely non-affine sum of three atoms and classifies a group word which transports it.
  britton-support-traps-dense-free-phase-chord: that uses HNN normal form to trap the support of a dense element in an associated subgroup; this uses only linear independence of the ambient group basis and applies to every group and every literal conjugator.
  finite-sheet-transport-networks-are-exactly-matricial: that constructs finite monomial models for a network already given by atom bijections; this proves that a literal three-of-eight transport necessarily supplies exactly such an affine atom bijection.
---

Let `Gamma` contain a central involution `J` and two elementary abelian
subgroups

```text
A_i=<J,z_(i,1),z_(i,2),z_(i,3)> isomorphic to (C_2)^4,
X_i={chi in A_i^ : chi(J)=-1}.                         (TET1)
```

Thus each `X_i` is an affine three-dimensional Boolean space.  For
`chi in X_i`, let

```text
e_(i,chi)=|A_i|^(-1) sum_(a in A_i) chi(a) a,
P_(i,S)=sum_(chi in S) e_(i,chi).                       (TET2)
```

These are the atom and coarse projections in the `J=-1` corner of the
corresponding rank-three Heisenberg spin chart.

If `S subset X_1` and `T subset X_2` both have three elements and a literal
group word `g in Gamma` satisfies

```text
g P_(1,S) g^(-1)=P_(2,T)                               (TET3)
```

in `C[Gamma]` (equivalently in its faithful canonical group von Neumann
algebra), then

```text
g A_1 g^(-1)=A_2.                                      (TET4)
```

Conjugation therefore induces an affine bijection

```text
g_*:X_1 -> X_2
```

and coefficient comparison in `(TET3)` gives

```text
T=g_*(S),
g e_(1,chi) g^(-1)=e_(2,g_*(chi))   for every chi.      (TET5)
```

The result is sharp.  Any two three-element subsets of an affine
three-cube are affinely equivalent, so relations conjugating the three
context generators according to such an affine map do transport the desired
three-of-eight projection.  But they transport all eight atoms at once.

Consequently the smallest non-affine Boolean sum does not provide a
selective group-word escape from the Heisenberg affine-flat fence.  A literal
transporter can identify it only by aligning the complete Boolean charts,
returning exactly to affine sheet transport.  This conclusion holds even
when `Gamma` is infinite and non-residually-finite.  It does not rule out a
genuinely additive corner unitary with several group-basis terms, whose
Fourier cancellations can move equal-rank projections without normalizing
either context subgroup; that is the remaining piecewise signed-Hecke
transport problem.
