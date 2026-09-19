---
rg: 2
id: finite-clifford-forbidden-atom-induction-proof
kind: route
title: Induce the forbidden selector character through the coupled finite group
target: finite-clifford-couplings-cannot-prune-a-forbidden-atom
requires:
  - finite-selector-gadget-induction-barrier
  - balanced-fourier-routers-retain-every-assignment-sector
---

Realize `(FCC2)` as `C[G] tensor_(C[D]) C_(chi_a)`.  The vector
`1 tensor 1` is nonzero and has `D`-character `chi_a`, so the Fourier
idempotent `(FCC1)` fixes it.  This proves `(FCC4)`.  Since `J` is central,
for every coset vector `g tensor 1`,

```text
J(g tensor 1)=gJ tensor 1=g tensor chi_a(J)=-g tensor 1,
```

proving `(FCC3)`.  Decomposing the finite-dimensional induced module into
irreducibles leaves at least one constituent on which `P_a` is nonzero.

The router-fiber statement follows by cutting that constituent with the
central scalar value of `S` and applying the exact `C directSum M_2`
classification.  For the quotient alternative, characters of `D/K` are
exactly the characters of `D` trivial on `K`; under
`D isomorphic to (C_2)^n` these form a linear annihilator, up to a fixed mark
coset.  Finally, if `G` is residually finite and `D` embeds, intersect the
finitely many finite-index kernels separating every nonidentity element of
`D`; the resulting finite quotient is injective on `D`, where the same
induction argument applies.

