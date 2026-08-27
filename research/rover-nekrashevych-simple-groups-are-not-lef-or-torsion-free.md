---
rg: 2
id: rover-nekrashevych-simple-groups-are-not-lef-or-torsion-free
kind: claim
title: Simple Rover--Nekrashevych commutators contain a non-LEF torsion Higman--Thompson subgroup
distinct_from:
  simple-alternating-limit-excludes-standard-self-similar-shifts: That rules out a faithful rooted-tree action by the desired simple kernel itself; this rules out passing from a self-similar input to the larger simple Rover--Nekrashevych commutator.
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: That excludes a topological-full-group source using torsion and a property-T fence; this excludes the current Thompson-like simple groups already at torsion-freeness and LEF.
---

Let `H<=Aut(T_d)` be any self-similar group, let `V_d(H)` be its
Rover--Nekrashevych group, and set

```text
S=[V_d(H),V_d(H)].
```

Then `S` contains the infinite finitely presented Higman--Thompson simple
group `V_d'=[V_d,V_d]`.  Consequently

```text
S is not LEF,                   S has nontrivial torsion.       (RNS1)
```

In particular the infinitely presented simple groups of Llosa Isenrich--
Schesler--Wu, *Infinitely presented simple groups separated by homological
finiteness properties*, arXiv:2510.01952 (2025), cannot serve as the simple
LEF/sofic torsion-free Kazhdan kernel, including their simple
`FP_infinity` example.  Their unusually strong finiteness properties do not
provide the finite automorphic presentation sought here, and their
Thompson-like ambient structure already violates two mandatory kernel
properties.

DERIVATION
rover-nekrashevych-simple-non-lef-proof
