---
rg: 2
id: agent-mf-hyperlinear-shadow-refutes-corner-route-proof
kind: route
title: Apply Kazhdan compression transport to the integer lamp commutator
target: agent-mf-hyperlinear-shadow-refutes-corner-route
requires:
  - infinite-cyclic-compression-lamp-mf
  - mf-vs-tracial-radical-strict-gap
---

The target claim contains the complete argument.  The first prerequisite
gives a faithful weak norm-corona model of the integer compression-lamp
group.  The second puts the displayed nontrivial commutator in its
operator-to-Hilbert--Schmidt shadow residual.  The elementary identity

```text
1-Re tr(U)=(1/2)||U-I||_2^2
```

then forces the trace gap of that word to vanish in every operator-norm
almost representation.  This contradicts the uniform gap equivalent to
`mf-invariant-corner-visibility`, but it leaves open the possibility of a
genuinely Hilbert--Schmidt-only model and therefore does not decide
`mf-implies-hyperlinear`.

