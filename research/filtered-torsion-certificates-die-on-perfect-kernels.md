---
rg: 2
id: filtered-torsion-certificates-die-on-perfect-kernels
kind: claim
title: Finitely generated perfect groups and idempotent rngs map trivially into ultraproducts of filtered groups and radicals, so no congruence, unipotent or radical model certifies torsion-freeness of the quotientless kernel
distinct_from:
  steinberg-images-die-in-torsion-free-groups: that kills elementary-sourced kernels through the Weyl word of order dividing 8 and names the surviving gate EL_3(I) with I=I^2; this kills the other half of the problem, the standard ways of certifying that a candidate (including EL_3(I)) is torsion-free, via the depth of a separated commutator filtration or the Jacobson radical.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the construction problem for a torsion-free sofic quotientless Kazhdan kernel; this is an obstruction to one class of torsion-freeness certificates for any such kernel, and the construction stays open.
  exact-kazhdan-radical-kernel-cannot-be-lef: that uses Ozawa--Thom to forbid LEF approximations by finite groups; this forbids nontrivial maps into ultraproducts of infinite torsion-free filtered groups such as level-p congruence groups of unbounded rank, where no finite-quotient argument applies.
  mapping-torus-mf-radical-lies-in-finite-residual: that forces the kernel to have no finite quotient; this uses that consequence (hence perfectness) as input and derives that the kernel is invisible to every separated-filtration target, even in ultraproducts.
artifacts:
  - research/filtered-torsion-certificates-die-on-perfect-kernels-proof.md
  - experiments/pronilpotent-torsion-certificates-2026-09-17/filtration_depth_check.py
---

**ESTABLISHED.** Conventions: `[a,b] = a b a^-1 b^-1`. `prod_omega` is the
algebraic ultraproduct over a nonprincipal ultrafilter `omega` on `N`, and an
identity holds in it exactly when it holds in `omega`-most coordinates.

A *separated filtration* on a group `G` is a chain of subgroups
`G = F^1 >= F^2 >= ...` with

```text
[F^a, F^b] <= F^(a+b)  for all a,b >= 1,        intersection_m F^m = 1.
```

Examples:
- the lower central series of any residually nilpotent group, which covers free
  groups, right-angled Artin groups, torsion-free nilpotent groups and residually
  torsion-free nilpotent groups;
- `F^m = Gamma(q^m)` on the principal congruence subgroup `Gamma(q) <= GL_N(Z)`,
  `q >= 2`, since `(1+q^a X)(1+q^b Y) - (1+q^b Y)(1+q^a X) = q^(a+b)(XY - YX)`;
- `F^m = 1 + J^m` on `1 + J`, for an ideal `J` of a unital ring with
  `J <= Jac(S)` and `intersection_m J^m = 0`. This covers `1 + t M_N(A[[t]])`,
  `1 + p M_N(Z_p)` and unipotent groups `UT_N(A)` with the superdiagonal
  filtration (`J` nilpotent).

**(PN1) Perfect groups are invisible to filtered ultraproducts.** Let `K` be a
finitely generated perfect group, and let each `G_n` carry a separated
filtration `F_n^*`. Then every homomorphism `K -> prod_omega G_n` is trivial. In
particular every homomorphism from `K` to one filtered group is trivial.

**(PN2) Idempotent rngs are invisible to radicals.** Let `I` be a finitely
generated associative rng with `I = I^2`, and let `S_n` be unital rings. A rng
map `phi: I -> prod_omega S_n` is zero if either of the following holds:
1. (radical) lifts of the generators can be chosen in `J_n`, for ideals `J_n`
   with `J_n <= Jac(S_n)` or with `intersection_m J_n^m = 0`. This covers
   `p M_N(Z)`, `p M_N(Z_p)`, nil ideals and `t A[[t]]`;
2. (perturbative) the `S_n` are Banach algebras, and the lifts of the
   generators have norms at most `delta(I, x)` in `omega`-most coordinates,
   where `delta > 0` depends only on a chosen presentation of the relation
   `x = A x` below.

The same conclusion holds for a rng map `I -> B` into a single Banach algebra
whose generator norms are at most `delta`.

**(PN3) Bounded-index version.** Let `K` be finitely generated with no
nontrivial finite quotient. Let `N_n <= G_n` be normal of index at most `B`,
where `N_n` carries a separated filtration. Then every homomorphism
`K -> prod_omega G_n` is trivial.

## Consequences for the root

`torsion-free-sofic-exact-mf-radical-over-z` forces the kernel `K` to be
finitely generated and Kazhdan with no nontrivial finite quotient
(`mapping-torus-mf-radical-lies-in-finite-residual`). Hence `K` is perfect.
Since `G = K semidirectProduct Z` is torsion-free exactly when `K` is, the
torsion-freeness of the witness must be certified on `K`. Consider the class of
*filtered torsion certificates*: prove `K` torsion-free by mapping it, injectively
or with a torsion-detecting family of maps, into
- a torsion-free level-`q` congruence group, or an ultraproduct
  `prod_omega Gamma_(N_n)(q)` of unbounded ranks (torsion-free coordinatewise by
  Minkowski when `q >= 3`);
- a unipotent, pro-unipotent or `1 + radical` group, or an ultraproduct of them;
- a residually torsion-free nilpotent or bi-orderable group, or an ultraproduct
  of them;
- a virtually filtered group of uniformly bounded index (PN3).

Every member of this class dies at one step. The finitely many perfect
relations `s_i = prod_j [u_ij, v_ij]` hold exactly in `omega`-most coordinates,
and there the depth of the generators doubles. The invariant is the minimal
filtration depth of the generator images. Every nontrivial `K` of the root,
whether intrinsic (DI) or extrinsic (DX), therefore has only trivial filtered
certificates.

At the rng level, (PN2) with `I = I^2` from `steinberg-images-die-in-torsion-free-groups`
(STF3) kills the classical certificate for relative elementary groups. There one
places `I` inside `p M_N(Z)` or any radical, so that `EL_3(I) <= Gamma_(3N)(p)`,
possibly in an ultraproduct. The STF3 survivor `EL_3(I)` cannot be proved
torsion-free that way, and neither can its image in any perturbative Banach model
near the identity.

Bi-orderability and local indicability are excluded more directly. Finitely
generated bi-orderable groups are locally indicable, a nontrivial finitely
generated perfect group has no `Z` quotient, and an ultraproduct of bi-ordered
groups is bi-ordered.

**What survives.** Torsion-freeness mechanisms that do not route through a
separated filtration:
- geometric ones (proper cocompact actions on CAT(0) complexes, as for
  Titz--Witzel lattices);
- small cancellation and hyperbolic Dehn filling without proper powers;
- extension-type mechanisms, such as `K <= V semidirectProduct Q` with a torsion-free
  module `V` and the torsion handled by (RLT) in
  `relation-cover-rational-lifting-over-quotientless-kazhdan`;
- left-orderability, which does not force indicable quotients;
- maps into ultraproducts of `GL_N(Z)` whose images avoid every fixed congruence
  level. Their torsion-freeness then needs a non-congruence argument.

Derivation: `filtered-torsion-certificates-die-on-perfect-kernels-proof`.
