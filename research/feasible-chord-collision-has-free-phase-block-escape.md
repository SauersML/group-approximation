---
rg: 2
id: feasible-chord-collision-has-free-phase-block-escape
kind: claim
title: A feasible first chord with a residual assignment collision has an exact free-phase block escape
distinct_from:
  one-binary-marginal-block-escape: that preserves one prescribed binary marginal before any cyclic constraints are frozen; this starts from the full first-chord relative-commutant solution and preserves every previously installed separator together with the new common chord sign.
  finite-relative-commutant-chord-is-bounded-integer-feasibility: that decides whether the endpoint chord orbits meet inside a finite packet; this adds a genuinely multi-piece finite-support group-ring unitary which moves a real assignment atom outside that packet.
  free-relative-placement-closes-one-balanced-chord: that freely chooses joint capacities and remains entirely matricial; this keeps the already frozen separator placements and gives the exact additional collision hypothesis under which block escape is possible.
---

**ESTABLISHED MINIMAL CONSTRUCTION.**  Work in a simple finite packet corner

```text
q C[K]q=M_D(C).
```

Let `A_0,A_1` be the frozen endpoint separator algebras and let `X_0,X_1`
be the chord signs.  Assume the bounded integer system `(WIF3)` of
`finite-relative-commutant-chord-is-bounded-integer-feasibility` is feasible.
Then there are endpoint regauges `U_i in A_i'` and one common involution `Z`
such that

```text
U_0 X_0 U_0^*=Z=U_1 X_1 U_1^*.                         (FCC1)
```

Consider one regauged endpoint context partition `(P_a)_(a in R)`.  Suppose
there are distinct supported assignments `a!=b` and nonzero coordinate
subprojections `e_r<=P_a`, `e_s<=P_b` which have the same joint character
under every already frozen binary marginal and under `Z`.  After a harmless
common coordinate refinement, take `e_r,e_s` rank one.

Then in

```text
Gamma=K times F_D
```

there is an explicit finite-support corner unitary `V` commuting with every
frozen marginal of the chosen endpoint and with `Z`, such that
`(V P_a V*)_a` is still a context partition, every old overlap and the new
chord equality `(FCC1)` remain exact, and both `V P_a V*` and `V P_b V*` lie
outside `q C[K]q`.

Thus the smallest first chord has a nonliteral, nonpermutation,
finite-support block-escaping solution whenever two independent conditions
hold:

1. the finite relative-commutant rank table is feasible; and
2. the frozen signs plus the chord do not separate the endpoint assignments.

The second condition is sharp for conjugation-based escape.  If the frozen
marginals together with `Z` separate all supported assignments, their joint
spectral projections are exactly the context atoms, and every unitary
preserving them fixes the context algebra.  A collision-free chord therefore
requires a genuinely higher additive operation which is not one common
endpoint conjugation.

This construction deliberately does not solve the full no-CE atlas.  Its
host is a direct product with a free group and the cell remains hyperlinear.
It removes the isolated feasible-collision chord from the frontier and
localizes the load-bearing cycle to infeasible conditional tables,
collision-free frozen endpoints, or incompatibility among several such
cells attached to one context.

