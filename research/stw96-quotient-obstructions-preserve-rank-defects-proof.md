---
rg: 2
id: stw96-quotient-obstructions-preserve-rank-defects-proof
kind: route
title: Push dense invertibles, finite-spectrum approximants, and generators to the quotient
target: stw96-quotient-obstructions-preserve-rank-defects
requires: []
---

Pass first to the induced unital surjection between minimal unitizations

```text
q_tilde:E_tilde -> Q_tilde.
```

Topological stable rank and real rank for a nonunital C*-algebra are defined
using its minimal unitization, so it suffices to work with `q_tilde`.  Assume
that `E` has stable rank one.  Given `b in Q_tilde`, choose a lift
`a in E_tilde`.  Approximate `a` by an invertible `u in E_tilde`.  Then
`q_tilde(u)` is invertible and approximates `b`, so invertibles are dense in
`Q_tilde`.

If `E` has real rank zero and `b=b* in Q_tilde`, replace any lift `c` by the
self-adjoint lift `(c+c*)/2`.  Approximate it by an invertible self-adjoint
element `h in E_tilde`.  Its image `q_tilde(h)` is again invertible and
self-adjoint, proving real rank zero of `Q`.

Nowhere scatteredness passes to quotients by Thiel--Vilalta,
[*Nowhere scattered C*-algebras*, Proposition
4.1](https://doi.org/10.4171/JNCG/526).  Finally, if `E=C*(g)`, then

```text
Q = q(E) = C*(q(g)).
```

These four observations prove the reduction statement.

Elliott--Li--Niu, [Proposition
3.3](https://arxiv.org/abs/2608.13707), prove `tsr(A)>=2` and `rr(A)>=2`.
If `A` were a quotient of an algebra of stable rank one or real rank zero, the
first or second paragraph would contradict that computation.  Evaluation
`C(X) tensor A -> A` is such a quotient.  More generally, if a unital
C*-algebra `D` has a character `chi`, then `id_A tensor chi:A tensor D -> A`
is a quotient, so tensoring by a character-bearing algebra cannot remove either
rank defect while retaining this obstruction.
