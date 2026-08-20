---
rg: 2
id: finite-subgroup-type-exclusion-is-already-nonhyperlinearity
kind: claim
title: Robust exclusion of one finite-subgroup type already proves the ambient group nonhyperlinear
distinct_from:
  finite-selector-gadget-induction-barrier: that proves every selector character occurs in a representation of a finite overgroup; this concerns asymptotic matrix models of an arbitrary infinite ambient group and uses its canonical regular trace.
  finite-overgroups-cannot-kill-schur-character-density-gap: that constructs a counterrepresentation when the overgroup is finite; this shows why asking an infinite overgroup to exclude one child type is circular rather than a simplification.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives a stationary vector for a graph of finite groups; this uses the positive Plancherel weight forced by the canonical trace of the final group.
---

Let `H` be a countable group containing a finite subgroup `C`, and let `sigma`
be any irreducible representation of `C`.  Write `e_sigma` for its primitive
central idempotent in `C[C]`.  The canonical trace of `L(H)` restricts to the
canonical trace of `C[C]`, so

```text
tau_H(e_sigma)=dim(sigma)^2/|C|>0.                    (FTE1)
```

Suppose there is a finite presentation of `H` and a dimension-independent
matrix theorem saying that every sequence of unitary tuples with defining
relator defect tending to zero satisfies

```text
||rho_n(e_sigma)||_(2,tr) -> 0.                       (FTE2)
```

Then `H` is nonhyperlinear.  Indeed, hyperlinearity supplies matrix
microstates converging in trace on every fixed group-algebra word to the
canonical trace.  Since `e_sigma` is a projection,

```text
||rho_n(e_sigma)||_2^2 -> tau_H(e_sigma)>0,            (FTE3)
```

contradicting `(FTE2)`.

The same conclusion holds if `(FTE2)` is stated after flexible
exactification of the fixed finite subgroup.  The character formula for
`e_sigma` is a fixed finite sum of `C` words, so the exactified type mass and
the original microstate evaluation differ by `o(1)`.

Consequently the Schur child cannot be groupified by attaching an auxiliary
overgroup which simply permits the good child type and robustly forbids the
bad one.  Producing such an overgroup is already a solution of the original
nonhyperlinearity problem, before the BCS or Schur packet is attached.

A noncircular matrix-valued return must retain the complete regular type
vector at each individual finite interface and obstruct only a **joint
contextual correlation** among several interfaces.  Equivalently, its local
extension cones must each contain the Plancherel point; the contradiction may
appear only in their fiber product over the shared BCS/multiplicity
coordinates.

