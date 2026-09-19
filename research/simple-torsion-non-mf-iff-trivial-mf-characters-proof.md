---
rg: 2
id: simple-torsion-non-mf-iff-trivial-mf-characters-proof
kind: route
title: Take trace limits of the macroscopic model and use simplicity for the converse
target: simple-torsion-non-mf-iff-trivial-mf-characters
requires:
  - simple-torsion-groups-have-a-macroscopic-mf-dichotomy
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

An operator-norm asymptotic representation whose normalized traces converge
pointwise has a character as its limit.  Normalization is immediate;
positive definiteness follows by replacing
`tr(sigma_n(g^(-1)h))` with `tr(sigma_n(g)^*sigma_n(h))`; and asymptotic
multiplicativity plus trace cyclicity gives conjugation invariance.  For a
countable group, a diagonal subsequence makes all traces converge.

If an MF character `chi` of a simple group is nontrivial, its character
kernel `{g:chi(g)=1}` is a proper normal subgroup and hence trivial.  Thus
`chi` is faithful.  For every `g!=1`,

```text
||sigma_n(g)-1||_2^2 -> 2-2 Re chi(g)>0.
```

The associated norm-corona homomorphism is therefore injective, so the MF
radical is not all of `G`.  Contrapositively, full radical forces every MF
character to be trivial.

Conversely, if the radical is not all of `G`, simplicity and the macroscopic
dichotomy give an operator-norm asymptotic representation with

```text
liminf_n ||sigma_n(g)-1||_2>0
```

for every `g!=1`.  Pass to a trace-convergent subsequence.  The preceding
identity shows that the limiting MF character is faithful.  This proves all
three equivalences.
