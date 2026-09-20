---
rg: 2
id: non-linear-kazhdan-hyperbolic-tree-hosts-are-open
kind: claim
title: No hyperbolic Kazhdan group outside the linear ones is known to pass both gates of the tree route to F_∞ simple hosts (residual finiteness and a faithful Baumslag–Solitar-class member)
distinct_from:
  arithmetic-lattices-embed-in-f-infinity-simple-groups: that runs the tree route for linear arithmetic lattices, where Llosa Isenrich–Schesler–Wu already give the conclusion; this asks for an input beyond them, a non-linear hyperbolic Kazhdan group, and records that none is known.
  commensurator-rigid-groups-have-no-faithful-bs-members: that is the second gate as an obstruction; this combines it with residual finiteness to state what a new input must have.
  bbmz-hosts-with-higher-dimensional-boundary-are-unbounded: that concerns the rational-similarity route for Kazhdan groups; this concerns the tree route.
---

**OPEN.** Is there a hyperbolic group `Γ` with property (T), not known to be linear, that meets both
conditions below?
1. `Γ` is residually finite.
2. Some member of `BS_Γ` acts faithfully on its Bass–Serre tree.

## What a positive answer gives

`Γ` is of type `F_∞`, being hyperbolic. So Steps 3–4 of
`arithmetic-lattices-embed-in-f-infinity-simple-groups-proof`, that is Bux–Llosa Isenrich–Wu
Theorem 11.1 for every `n` with one envelope, embed `Γ` in a simple group of type `F_∞`. For a
non-linear `Γ` this would go beyond Llosa Isenrich–Schesler–Wu, arXiv:2510.01952, Theorem 1.4,
which needs `ℚ̄`-linearity.

## The two gates

- **Residual finiteness** is forced: `finite-index-edge-hnn-embeds-in-fp-simple-group`, L1 and L4.
- **A non-rigid commensurator** is forced by `commensurator-rigid-groups-have-no-faithful-bs-members`
  (fb1c469c2). If `Γ → Comm(Γ)` is injective with finite-index image, no member of `BS_Γ` acts
  faithfully. So `Γ` must have infinite index in its abstract commensurator.
  - For `Γ` acting geometrically on a CAT(0) complex `X`, a natural source would be a non-discrete
    `Aut(X)` in which `Γ` has dense commensurator, as for uniform tree lattices.

## Known status of explicit candidates (searched 2026-09-19)

- **Caprace–Conder–Kaluba–Witzel groups**, including `𝓗_31` (arXiv:2011.09276, Theorem 1.2).
  - The paper, read via a summarizing fetch of the arXiv HTML, does not claim residual finiteness
    or linearity for them. It frames residual finiteness of hyperbolic groups as Gromov's open
    question.
  - Its Theorems 1.3–1.4 give some of these groups finite simple quotients of arbitrarily large rank,
    which does not imply residual finiteness.
  - Whether the automorphism groups of their triangle complexes are non-discrete was not checked.
- **Random groups at density `(1/3, 1/2)`**: residual finiteness is unknown (Gromov's question).
- **Groups from the Żuk / Ballmann–Świątkowski criterion**: not checked at source.
- **Quotients from the Belegradek–Osin Rips construction with property (T)** (math/0605553): no
  residual finiteness result known on main.

So the tree route currently reaches exactly the Kazhdan hyperbolic groups LISW already cover.
