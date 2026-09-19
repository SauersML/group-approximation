---
rg: 2
id: finitary-alternating-lamp-no-global-rounding-proof
kind: route
title: Remove every finite character orbit, then use locally finite microstates
target: finitary-alternating-augmentation-lamp-global-rounding-no-go
requires: []
---

Every finite subset of `Gamma` is contained in

```text
M_Y rtimes Alt(Y)
```

for some finite `Y subset X`, so `Gamma` is locally finite.  This proves item
2 and supplies exact finite models for every fixed word window.

The compact dual of the even-parity module is

```text
hat M = F_2^X / <constant-one coloring>.                       (1)
```

Suppose a character class `[c]` has finite `A`-orbit.  The resulting action
of the infinite simple group `A` on that finite orbit is trivial, because
`A` has no nontrivial finite quotient.  Hence `[c]` is fixed.  For every
`g in A`, write

```text
g c-c=kappa(g) 1,                 kappa(g) in F_2.             (2)
```

The cocycle identity makes `kappa:A->F_2` a homomorphism.  Simplicity (or
perfectness) gives `kappa=0`; transitivity then makes `c` constant.  Thus
`[c]=0`.  The trivial character is the only finite character orbit.

Now let `rho:Gamma->U(d)` be exact.  Since `M` is elementary abelian,
`rho|M` has a finite spectral support in `hat M`.  Conjugation covariance
makes that support `A`-invariant, so the preceding paragraph makes it
trivial.  Therefore `rho(M)=1`, proving item 3.

If a uniform global semidirect decoder preserved a fixed `1!=m in M`, apply
it to the exact finite-window models coming from local finiteness.  Their
relator defect tends to zero and their canonical traces separate `m`; the
decoded exact representations all kill `m`, a contradiction.

