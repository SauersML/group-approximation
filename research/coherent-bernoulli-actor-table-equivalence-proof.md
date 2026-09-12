---
rg: 2
id: coherent-bernoulli-actor-table-equivalence-proof
kind: route
title: Identify simultaneous finite completions with invariant diagonal normalizers
target: coherent-bernoulli-actor-tables-are-cartan-soficity
requires:
  - diagonal-normalizer-rigidity
---

For `(1)=>(2)`, take the ultraproduct of the full diagonal algebras of
functions on the finite table carriers.  Cylinder convergence puts
`Theta(A)` in this diagonal ultraproduct.  The permutations, together with
the allowed diagonal phases, normalize it; Hamming multiplicativity makes
their ultraproduct classes a representation and gives `(CAT1)`.

For `(2)=>(1)`, apply `diagonal-normalizer-rigidity` to factor every actor
normalizer uniquely as a permutation ultraproduct times a diagonal unitary.
Uniqueness passes multiplication to the permutation factors, while the
diagonal factors commute with `Theta(A)` and therefore do not affect cylinder
transport.  Choosing representatives and diagonalizing finitely many
cylinder projections gives the required finite tables on every prescribed
finite window.  The normalized matrix trace gives their empirical cylinder
laws.  A diagonal rank refinement (or amplification by a common denominator)
turns weighted atoms into uniform finite carriers without changing any
ultraproduct class.

This is also the usual finite-model definition of a sofic pmp action: finite
diagonal probability algebras, asymptotically multiplicative permutations,
asymptotically equivariant images of observables, and convergence of their
traces.  Retaining labelled site evaluations gives exactly the orbit-chart
definition of a sofic set action.  Conversely either kind of sofic chart
gives these diagonal algebras and permutations by its Koopman action.  This
proves the stated dictionaries.

For the finite completion assertion, set

```text
D_g={x in F:g x in F},       R_g=gD_g.
```

The map `x |-> g x` is a bijection `D_g->R_g`; since the two complements in
`F` have equal size, extend it to a permutation of `F`.  Permuting cube
coordinates gives `pi_g` satisfying `(CAT2)`.  Formula `(CAT4)` preserves
uniform measure, has no fixed point for nonidentity named labels, and does
not alter the completed coordinate transport.  Its trace assertions follow
because the diagonal of a permutation matrix is the indicator of its fixed
points.  The two copy-coordinate shifts in `(CAT5)` are distinct everywhere,
so the Hamming defect is one; for permutation matrices `P,Q`,

```text
||P-Q||_2^2=2-2 |{y:Py=Qy}|/|Y|,
```

which gives the squared Hilbert--Schmidt defect `2`.

Finally, on a forest, recursively transporting a chosen root basis gauges
every edge map to the identity matching of bases.  The recursion is
well-defined exactly because there is a unique root path.  On adding an edge,
the obstruction is the product around the resulting cycle, proving the
tree/groupoid description.  Once those cycles arise from an exact finite
group action, the atomwise character calculation of
`finite-cylinder-mixed-traces-kill-normalizer-holonomy` regularizes all
stabilizer representations.  Before joint extraction, `(CAT4)-(CAT5)` shows
that its hypothesis is absent even though every individual trace and
covariance conclusion holds exactly.
