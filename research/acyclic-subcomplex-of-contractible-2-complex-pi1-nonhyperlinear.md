---
rg: 2
id: acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear
kind: claim
title: A finite acyclic subcomplex of a contractible 2-complex is simply connected or has a non-hyperlinear fundamental group
distinct_from:
  whitehead-asphericity-conjecture: that asserts asphericity of every subcomplex of an aspherical 2-complex; this constrains only the fundamental group of finite acyclic subcomplexes of contractible 2-complexes, and holds whether or not that conjecture does.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that is the existence of a non-aspherical subcomplex; this says that any finite acyclic non-simply-connected subcomplex, aspherical or not, has a non-hyperlinear fundamental group.
  non-hyperlinear-group: that asks for some non-hyperlinear group; a finite acyclic non-simply-connected subcomplex of a contractible 2-complex would supply one through this claim.
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

**ESTABLISHED** through `acyclic-subcomplex-pi1-nonhyperlinear-proof`. Unreviewed. No
novelty is claimed: this is Nitsche--Thom Theorem 1.2 (attributed there to
Gerstenhaber--Rothaus and Pestov) applied to a finite stage of a null-homotopy.

Let `Y` be a contractible 2-dimensional CW complex and `K` a finite connected subcomplex
with `H_1(K; Z) = 0`. Since `H_2(K) ⊆ H_2(Y) = 0`, `K` is acyclic. Then `π_1(K)` is
trivial or not hyperlinear (not Connes-embeddable).

## Consequences

1. **Finite fundamental groups.** A finite acyclic 2-complex with finite nontrivial
   fundamental group is not a subcomplex of any contractible 2-complex, finite or infinite.
   Finite groups embed in unitary groups, so they are hyperlinear. This covers every flag
   triangulation of a spine of the Poincaré homology sphere.
2. **Bridge to non-hyperlinear groups.** Exhibiting a contractible 2-complex with a finite
   acyclic non-simply-connected subcomplex, aspherical or not, gives a non-hyperlinear group.
3. **Scope in the Bestvina--Brady alternative.** The Whitehead alternative of
   `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead` produces a finite subcomplex
   `K = φ_v(S_(v,L))` of a contractible `Y` that retracts onto `L` up to homotopy. That `K`
   need not be acyclic. The argument below then breaks: the kernel of the exponent-sum matrix
   injects into `H_1(K)`, which can be nonzero, and the extra relators may kill `π_1(L)`
   directly. So this claim does not decide `bestvina-brady-poincare-kernel-has-geometric-dimension-three`.
   It is the input for `epsilon-map-conjecture-gives-poincare-kernel-gd-three`.
