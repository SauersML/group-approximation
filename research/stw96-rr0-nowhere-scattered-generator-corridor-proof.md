---
rg: 2
id: stw96-rr0-nowhere-scattered-generator-corridor-proof
kind: route
title: Pass from zero-dimensional Glimm halving through Z-stability to generator rank one
target: stw96-rr0-nowhere-scattered-generator-corridor
requires: []
---

Real rank zero implies the ideal property, and the ideal property implies
topological dimension zero.  Ng--Thiel--Vilalta, [Theorem
2.3](https://doi.org/10.1112/blms.70343), prove that a C*-algebra of
topological dimension zero has the Global Glimm Property exactly when it is
nowhere scattered.  This proves the first assertion.

For the generator assertion, suppose in addition that `A` has finite nuclear
dimension and no nonzero purely infinite simple subquotient.  By
Thiel--Vilalta, Theorem 3.1, nowhere scatteredness says in particular that `A`
has no nonzero elementary subquotient.  Real rank zero gives the ideal property,
and hence `Prim(A)` has a basis of compact open sets.  Therefore all hypotheses
of Robert--Tikuisis, [Corollary
7.11](https://arxiv.org/abs/1308.2941), hold, and `A` is `Z`-stable.

Hannes Thiel, [Theorem
5.3](https://arxiv.org/abs/2006.08404), proves that every separable,
`Z`-stable C*-algebra of real rank zero has generator rank one (indeed, the
generators are a dense `G_delta`).  This gives the second assertion.  The same
paper's Corollary 5.5 proves directly that every nuclear, purely infinite
C*-algebra of real rank zero has generator rank one, giving the third
assertion.

Finally, Robert--Tikuisis explicitly note after Corollary 7.11 that finite
decomposition rank together with the ideal property supplies both the absence
of purely infinite simple subquotients and the required compact-open basis.
Real rank zero supplies the ideal property, so the stated finite-decomposition-
rank corollary follows.
