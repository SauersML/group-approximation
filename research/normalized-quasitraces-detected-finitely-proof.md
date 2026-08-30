---
rg: 2
id: normalized-quasitraces-detected-finitely-proof
kind: route
title: Take an ultralimit over finite subsets and pass every quasitrace axiom locally
target: normalized-quasitraces-detected-finitely
requires: []
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Restriction proves `(1)=>(2)`.  For the converse, direct the finite subsets
of `B` by inclusion.  For each finite `F subset B`, put

```text
B_F=C*(1,F)
```

and choose a normalized 2-quasitrace `tau_F` on `B_F`.  Choose an ultrafilter
`U` on the directed set which contains every tail `{G:F subset G}`.

For `x in B`, the set of `F` for which `x in B_F` belongs to `U`.  Define

```text
tau(x)=lim_U tau_F(x),
```

assigning any bounded value at the irrelevant indices where `x` is not in
`B_F`.  Do the same with the matrix extensions
`tau_F^(2):M_2(B_F)->C` to define `tau^(2)` on `M_2(B)`.  Normalized
quasitraces are uniformly bounded on each fixed norm ball, so these scalar
ultralimits exist.

Every axiom involves only finitely many algebra elements.  On a tail, all of
those elements lie in the same `B_F`, where the axiom holds exactly.
Taking the scalar ultralimit therefore gives

```text
tau(xx*)=tau(x*x)>=0,
tau|_D is linear for every abelian C-star subalgebra D subset B,
tau(a+ib)=tau(a)+i tau(b) for self-adjoint a,b,
tau^(2)(x tensor e_11)=tau(x),
tau(1)=1.
```

Thus `tau` is a normalized 2-quasitrace on `B`, proving `(2)=>(1)`.
Contraposition supplies a finite `F` for which `B_F` is quasitraceless.
Finally, a normalized quasitrace on an intermediate unital algebra would
restrict to one on `B_F`, so no intermediate algebra has one.

The only set-theoretic input is the ultrafilter lemma.  No exactness,
separability, continuity theorem for quasitrace spaces, or quasitrace
linearity is used.
