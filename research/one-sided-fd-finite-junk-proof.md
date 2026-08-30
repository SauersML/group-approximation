---
rg: 2
id: one-sided-fd-finite-junk-proof
kind: route
title: Add a converging evaluation representation on a rank-one corner
target: one-sided-fd-models-allow-finite-junk-corners
requires: []
---

## Proof

Let `H` be infinite dimensional, `B=B(H)`, `A=C([0,1])`, and let

```text
phi(f)=f(0)1_B.
```

This map factors through `C`, so it has nuclear dimension zero.  Its only
nonzero positive range elements are positive scalar multiples of `1_B`,
hence are properly infinite.

Choose a rank-one projection `p`.  Given finite `F subset C([0,1])` and
`epsilon>0`, uniform continuity gives `t>0` such that

```text
|f(t)-f(0)|<epsilon                       (f in F).
```

Set `D=Cp+C(1-p)` and define

```text
theta_t(f)=f(t)p+f(0)(1-p).
```

This is a unital homomorphism, and

```text
||theta_t(f)-phi(f)||=|f(t)-f(0)|<epsilon  (f in F).
```

Because `t!=0`, a continuous function separates `0` and `t`, so the two
spectral projections of `theta_t(A)` are `p` and `1-p`; hence
`D=C*(theta_t(A))`.  Nevertheless `p` is a finite minimal projection.

There is still a better scalar model obtained by setting `t=0`, so this is
not a counterexample to the zero-dimensional case.  It is a concrete local
packet proving that an argument must merge representations which become
indistinguishable on the growing test sets; merely deleting algebraically
unused summands does not remove the obstruction.
