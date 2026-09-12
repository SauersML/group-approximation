---
rg: 2
id: finite-hyperbolic-residual-iff-persistent-class-proof
kind: route
title: Identify the finite-residual case with the persistent prime extension case
target: finite-hyperbolic-residual-iff-persistent-class
requires:
  - finite-kernel-nonrf-has-central-prime-reduction
  - finite-central-extension-rf-iff-virtually-splits
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

For (1) implies (2), use `G->G/R(G)`. The quotient is residually finite
by the definition of the residual: every nonidentity coset is detected
by a finite homomorphism descending from `G`. Its hyperbolicity follows
because the kernel is finite. The first prerequisite gives (2) implies
(3). A group as in (3) is hyperbolic by its finite-kernel map to its
hyperbolic base, so it also gives (1).

For (3) implies (4), let `alpha` classify the central extension
`1->C_p->J->H->1`. A section over a finite-index subgroup `U<=H` would
produce `S<=J` with `[J:S]=p[H:U]` and `S intersect C_p=1`. This
contradicts `R(J)=C_p`, since every finite-index subgroup contains the
finite residual. Thus the extension class persists.

For (4) implies (3), form the central extension classified by `alpha`.
The second prerequisite makes its total group `J` non-residually finite.
Residual finiteness of the base gives `R(J)<=C_p`, since finite
homomorphisms pulled back from the base detect every element outside
the kernel. Therefore `1<R(J)<=C_p`, and primality gives `R(J)=C_p`.

These prove both directions of the equivalence without assuming either
existence assertion. The artifact supplies the complete proofs and the
separate explanation that an arbitrary infinite residual is untreated.
