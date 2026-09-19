---
rg: 2
id: strong-t-orbits-never-inject-into-subexp-times-tree
kind: claim
title: No infinite transitive set of a group with Lafforgue's strong property (T) has a Lipschitz uniformly finite-to-one map into Cay(A)×T with A of subexponential growth and T a bounded-degree tree, so SL_3(Z) and every higher-rank lattice is excluded from the Z^2×F_d boundary-product full groups
distinct_from:
  kazhdan-orbits-never-inject-boundedly-into-z2-times-free: that is the same NO answer for every Kazhdan group and stays OPEN; this proves it for groups with strong (T), which include SL_3(Z), SL_n(Z) for n ≥ 3 and cocompact lattices of SL_3(Q_p), but not hyperbolic Kazhdan groups, which lack strong (T).
  tree-times-zk-images-have-polynomial-ball-separators: that kills orbits whose stabilizers meet Z^4 or F₂×F₂ finitely, by ball separators; SL_3(Z) contains neither Z^4 nor, as far as is known here, F₂×F₂, so it is untouched there. This uses no separation at all, only weighted walls and strong (T).
  kazhdan-schreier-graphs-have-superquadratic-ball-separation: that is the OPEN separation lower bound for all Kazhdan Schreier graphs; this bypasses it for strong-(T) groups and says nothing about separation.
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that kills virtually free scaffolds by commensurated tree walls (item 5); here the walls over Cay(A)×T have infinite boundary and are not commensurated, and they are made square-summable by a small exponential weight on the A-coordinate that only a non-unitary strong-(T) argument can absorb.
---

**ESTABLISHED** by `strong-t-orbits-never-inject-into-subexp-times-tree-proof`
(lane proof, swarm-0917-w15-w15-bh-break; elementary modulo two cited theorems; not reviewed).
Recalled rather than re-read at source:
- Lafforgue's definition of Hilbert strong property (T) (Duke Math. J. 143, 2008, Définition 0.1)
  and his theorem that `SL_3` over a non-archimedean local field and its cocompact lattices have it;
- de la Salle's theorem (Acta Math. 223, 2019) that every lattice in a higher-rank simple Lie or
  algebraic group, uniform or not, has strong property (T), in particular `SL_3(Z)`.

## Setting

- `K = ⟨S⟩` is finitely generated, with word length `|·|`.
- `K` has **Hilbert strong (T)**: there is `s > 0` such that for every `C ≥ 1` there are finitely
  supported probability measures `m_n` on `K` for which, for every representation `π` of `K` on a
  Hilbert space with `‖π(k)‖ ≤ C e^{s|k|}`, the operators `π(m_n) = Σ_k m_n(k) π(k)` converge in
  norm to a projection `P_π` onto the `π`-invariant vectors.
- `A = ⟨S_A⟩` is finitely generated of subexponential growth. `T` is a tree of bounded degree.
  `Y = Cay(A) × T` is the Cartesian product.
- `O` is an infinite transitive `K`-set, and `f : O → Y` is `L`-Lipschitz for the Schreier graph
  `Sch(K, O, S)` and has fibres of size at most `m`.

## Theorem

No such `f` exists.

## Consequences

1. **Need d2d6a0cb for strong-(T) groups.** No group with strong (T) acts transitively on an infinite
   set `Z` with an injective bounded-left-displacement map `Z → Z^2 × F_d`. The map is Lipschitz by
   item 2 of `tree-times-zk-images-have-polynomial-ball-separators`, and `Cay(Z^2×F_d) = Cay(Z^2)×T_{2d}`.
   The same holds with `Z^2` replaced by any group of subexponential growth.
2. **Host kill.** Every strong-(T) subgroup of `[[(Z^2×F_d) ⋉ (Ω×∂F_d)]]`, `Ω` a free `Z^2`-subshift,
   is finite. It has no infinite orbit through a free point, by item 1 and the orbit map of the
   corollary of `dense-finite-free-orbits-force-finite-kazhdan-subgroups`, and that corollary then
   makes it finite. So `SL_3(Z)`, which is finitely presented with solvable word problem, does not
   embed in this full group. Nor does any group containing it, such as `Z^3 ⋊ SL_3(Z)` or `SL_n(Z)`.
   The full-group mechanism of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` therefore
   cannot give a Boone–Higman-universal host.
3. **Invariant and failing step.** Over `Cay(A) × T`, the pulled-back half-tree walls have boundaries
   of subexponential size in the `A`-direction. A weight `e^{-2ε|a|}` makes them square-summable while
   `K` acts with norm growth `e^{εL|k|}`. Strong (T) turns every such wall cocycle into a coboundary.
   An approach that embeds strong-(T) groups permutationally dies exactly where the scaffold is
   (subexponential) × (tree). It needs **two independent exponential directions**, as `F₂×F₂` has and
   as the Robertson–Steger host `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan` has.
4. **What is left of the need.** Kazhdan groups without strong (T). Lafforgue showed that infinite
   hyperbolic groups never have it, so this means hyperbolic Kazhdan groups (lattices of `Sp(n,1)`,
   random groups at density `> 1/3`) and groups such as the simple Kazhdan hosts of
   `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, where strong (T) is not known. For a BH
   host kill these do not matter, since `SL_3(Z)` already has to embed.

## Attempts

1. **Pulled-back walls with unitary ℓ²** (w11, recorded in
   `kazhdan-schreier-graphs-have-superquadratic-ball-separation`). This dies because the wall boundary
   is infinite. Here the weighted, non-unitary space removes exactly that obstruction.
2. **Uniformly bounded weights** (heuristic, not a theorem). A weight `w` on `O` gives a uniformly
   bounded representation only if `w(kx)/w(x)` is bounded in `k` and `x`. For an unbounded `A`-orbit
   direction this keeps `w` from being summable along `A`, which the walls need. So the plain-(T)
   version stalls at the step "b is a coboundary" (proof, Step 2). That is why strong (T) is used.
