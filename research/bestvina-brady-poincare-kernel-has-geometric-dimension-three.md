---
rg: 2
id: bestvina-brady-poincare-kernel-has-geometric-dimension-three
kind: claim
title: The Bestvina--Brady kernel of a Poincaré-sphere spine has cohomological dimension 2 and geometric dimension 3
distinct_from:
  bestvina-brady-poincare-kernel-has-geometric-dimension-two: that is the complementary alternative, geometric dimension 2, which yields a Whitehead counterexample; this is geometric dimension 3, which refutes Eilenberg--Ganea.
  eilenberg-ganea-or-whitehead-is-false: that is the established dichotomy; this decides one side of it.
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**OPEN.** Let `L` be a flag triangulation of a spine of the Poincaré homology
sphere and `H_L` the Bestvina--Brady kernel. `H_L` has cohomological dimension
2 (`eilenberg-ganea-or-whitehead-bestvina-brady-citation`) and geometric
dimension 3. If established, it refutes `eilenberg-ganea-conjecture`.

## Attempts

1. **Bestvina--Brady's closing remark (p. 470), verbatim.** "Fix a metric on L.
   We conjecture that there is ε > 0 such that if g : L → K is a surjective
   PL ε-map, then K is homotopy equivalent to L with 1- and 2-cells attached.
   This conjecture implies that the geometric dimension of H_L is 3."
   - The source gives no proof of either sentence.
   - The ε-map statement is not recorded here as a claim, because the
     implication is unproved in the source.
2. **What any proof must rule out (2026-09-13).** Suppose a contractible
   2-complex `Y` carries a free `H_L`-action.
   - `Y` has infinitely many `H_L`-orbits of cells: a free cocompact action on a
     simply connected complex would make `H_L` finitely presented, which
     contradicts Example (3).
   - Case 3 of `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`
     then gives a finite subcomplex `K` of `Y` with `pi_1(L)` as a retract of
     `pi_1(K)`. `pi_1(L)` is the binary icosahedral group, so `pi_1(K)` has
     torsion.
   - A contradiction therefore has to come from the global structure of `Y`,
     not from `K` alone. Gersten's criterion (arXiv:1501.06875, abstract, via a
     web tool, not verified verbatim) says a finite connected subcomplex of an
     aspherical 2-complex is aspherical iff its fundamental group has
     cohomological dimension 2. For `K` that criterion is consistent with
     non-asphericity, so it gives no contradiction.
