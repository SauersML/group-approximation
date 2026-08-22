---
rg: 2
id: titz-witzel-simple-kazhdan-cat0-lattices-exist
kind: claim
title: Torsion-free simple Kazhdan CAT(0) lattices on exotic C2-tilde buildings exist, with explicit finite presentations
distinct_from:
  simple-kazhdan-kac-moody-lattices-exist: those are the Caprace--Remy twin building lattices, NON-uniform, with torsion root subgroups and no cocompact CAT(0) model (km-lattices-admit-no-cocompact-npc-model); these are UNIFORM lattices on single exotic C2-tilde buildings, torsion-free, acting freely cocompactly — the cocompactness that unlocks every Brown-type cohomological shortcut the Kac--Moody family provably lacks.
  km-lattices-admit-no-cocompact-npc-model: that fence shows Kac--Moody lattices never admit cocompact CAT(0) models; this records the literature family that DOES: the first simple CAT(0) groups with property (T).
---

**Literature fact (Titz Mite--Witzel, *Non-residually finite
C2-tilde-lattices*, arXiv:2509.05054v2, August 2026; introduction read
from the PDF on 2026-08-22).**  Theorem A (verbatim content): there are
five finite triangle complexes `Y_i^q` (`q = 2, 3`) whose universal
covers `X_i^q` are exotic buildings of type `C~_2` (thickness `q + 1`)
and whose fundamental groups `Gamma_i^q = pi_1(Y_i^q)` are NOT residually
finite; the finite residual `Gamma^_i^q = (Gamma_i^q)^(infinity)` has
FINITE INDEX; the buildings are pairwise non-isomorphic and the groups
pairwise not quasi-isometric; "Since the `Gamma_i^q` are uniform building
lattices they are CAT(0)-groups and have Kazhdan's property (T)."
Corollary B (verbatim content): the five groups `Gamma^_i^q` are "simple
CAT(0) groups that have property (T) and are not quasi-isometric to a
proper direct product" — the first known.  Explicit presentations: 15
generators / 24 relations of lengths 2 and 4 at `q = 2` (their Prop.
4.3); 40 generators / 64 relations at `q = 3` (their Appendix A).  The
construction wraps a non-residually-finite lattice on a product of two
trees (Wise; Burger--Mozes) inside an irreducible exotic building.

**Derived facts used downstream (proofs in the citation route).**  Each
`Gamma_i^q` acts FREELY and cocompactly on the contractible (CAT(0),
Cartan--Hadamard) 2-dimensional locally finite complex `X_i^q`, hence is
torsion-free of type `F` with `H^2(Gamma, Z Gamma) = H^2_c(X_i^q)`; the
same holds for the finite-index simple subgroups `Gamma^`.  So these are
finitely presented, torsion-free, simple, Kazhdan, non-residually-finite
CAT(0) groups — members of the class of
`non-rf-kazhdan-group-with-llp-full-c-star-algebra` with every
cohomological handle available, unlike the Kac--Moody candidates.  The
fence-exclusion theorem `twin-lattices-exclude-known-llp-fences` applies
verbatim (single locally finite polyhedral complex, proper cocompact
cellular action), and torsion-freeness closes even its char-p residual
risk: no infinite torsion module can embed at all.
