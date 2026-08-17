---
rg: 2
id: degree-kernel-abelianization-is-infinite-cyclic
kind: claim
title: The degree-m kernel of a perfect coefficient group has infinite cyclic abelianization
invalidates: [simple-kl-via-abelianized-relation-module, leavitt-kl-violation-via-fox-calculus]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Let `G` be any group, `m >= 1`, and `N_m = ker(G * <t> -> C_m)` as in
`kl-simple-failure-leaves-only-the-cyclic-quotient`.  Then

    N_m  =  ( *_{i=0}^{m-1} t^i G t^{-i} )  *  <t^m> ,

a free product of `m` conjugate copies of `G` with an infinite cyclic factor.

If `G` is **perfect** then

    N_m^ab  =  Z ,      induced by  x |-> deg_t(x)/m ,

the residual `C_m`-action on it is trivial, and **every** `w in N_m` with
`deg_t(w) = m` has `[w] = ±1`, a generator.

## The consequence, which is the point

If `N_m = <<w>>_{G*<t>}` then `[w]` generates `N_m^ab` as a `Z[C_m]`-module —
inner automorphisms of `N_m` act trivially on `N_m^ab` and `G <= N_m`, so
only the quotient action survives.  That necessary condition is satisfied
automatically, by every candidate word, for every perfect `G`.

So the first-homology test on the degree-`m` kernel is **vacuous** exactly
where the reduction chain lands: `kl-counterexample-can-be-two-generator-simple`
sends every counterexample into a simple, hence perfect, group, and
`leavitt-gl-equals-el-and-perfect-unit-group` puts the binary Leavitt unit
group in the same class.  A first-Fox-derivative or Alexander-module
computation there selects nothing and excludes nothing.  Two routes are
invalidated by this, one on each side of the problem.

## Terminology, stated precisely because the literature is loose here

The object computed is `N_m^ab`, not the relation module
`<<w>>/[<<w>>, <<w>>]` of a presentation.  The condition killed is exactly
"`[w]` generates `N_m^ab` over `Z[C_m]`".  The external audit calls `N_m^ab`
the relation module; the conclusion is unaffected and this node states the
condition in the form that is actually tested.

## Where an obstruction can still live

Anything that sees more than `H_1` of the kernel: a Peiffer quotient or
crossed module, identities among relations, a second relation module or an
explicit `pi_2` class, or — most concretely — a finite **nonabelian**
quotient of `N_m`, compatible with the ambient conjugation action, in which
the image of `w` has proper normal closure.  That is the open target
`uniform-normal-rank-certificate-for-degree-kernels`.
