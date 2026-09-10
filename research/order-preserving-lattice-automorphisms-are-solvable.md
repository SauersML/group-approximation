---
rg: 2
id: order-preserving-lattice-automorphisms-are-solvable
kind: claim
title: An order-preserving subgroup of GL_n(Z) is solvable, so relative-(T) semidirect products are never bi-orderable
---

Let `Z^n` carry a bi-invariant total order and let `Gamma <= GL_n(Z)` preserve
it.  Then `Gamma` is real-triangularizable with positive diagonal, hence
solvable.

Consequence.  If `G = Z^n semidirect Gamma` is bi-orderable then the image of
`Gamma` in `GL_n(Z)` is solvable.  The standard sources of relative property (T)
for the pair `(Z^n semidirect Gamma, Z^n)` require that image to be large — non-
amenable, in the usual constructions Zariski-dense — so **no group built that
way is bi-orderable**.  In particular `Z^2 semidirect F_2` with the relative-(T)
action is not bi-orderable, although it is locally indicable.

This is the reason the cell "bi-orderable and not Haagerup" in the group
property atlas resists the obvious attack.  The cheapest non-Haagerup groups
that are not already Kazhdan are exactly the relative-(T) semidirect products,
and this rules all of them out at once.  It also composes with the elementary
fact that a nontrivial finitely generated locally indicable group surjects onto
`Z`, while a Kazhdan group has finite abelianization: bi-orderable Kazhdan
groups do not exist either, so the whole (T)-flavoured supply is closed off and
a witness would have to fail Haagerup for some other reason.
