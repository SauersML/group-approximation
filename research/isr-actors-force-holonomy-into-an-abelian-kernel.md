---
rg: 2
id: isr-actors-force-holonomy-into-an-abelian-kernel
kind: claim
title: Invariant-subalgebra-rigid actors can recover relation rectangles only through an abelian action kernel
distinct_from:
  normalizer-kernel-generation-forces-haar-action: that reconstructs a Haar algebraic action once the phase kernel generates the Cartan; this proves that kernel generation is forced by native-base recovery for actors with invariant subalgebra rigidity.
  normalizer-kernel-generation-is-not-automatic: that gives an amenable wreath-product counterexample without invariant subalgebra rigidity; this identifies an actor class where the counterexample mechanism is impossible.
  regular-isotropy-cocycle-over-hyperlinear-actor-is-ce: that blocks non-CE payload retention for hyperlinear actors; this blocks recovery of the native diffuse rectangle algebra even without using Connes embeddability.
---

Say that a countable group `Gamma` has invariant subalgebra rigidity
`(ISR)` if every von Neumann subalgebra `B<=L(Gamma)` normalized by all
canonical group unitaries has the form

```text
B=L(Sigma)  for a normal subgroup Sigma normal Gamma.   (ISR1)
```

Let `Gamma` act pmp on a diffuse probability space `(X,mu)`, let `R`
be its orbit relation, fix `n>=1`, and let
`b in Z^1(Gamma curvearrowright X,U(n))`. Put

```text
v_g=b_g(u_g tensor 1_n),
N_b=W*(v_g:g in Gamma).
```

Assume that the `v_g` have the regular character and recover the native
rectangle base:

```text
(tr_n tensor tau_R)(v_g)=1_(g=e),
L^infinity(X) tensor 1_n <= N_b.                        (ISR2)
```

If `Gamma` has `(ISR)`, then there is an infinite abelian normal subgroup
`Sigma normal Gamma` such that

```text
Sigma <= ker(Gamma curvearrowright X),
W*(v_s:s in Sigma)=L^infinity(X) tensor 1_n.            (ISR3)
```

Consequently an ISR actor with no infinite abelian normal subgroup cannot
recover the native rectangle algebra by any regular finite-rank
transformation cocycle. This applies in particular to every ICC
acylindrically hyperbolic actor, including nonabelian free groups:
Chifan--Das--Sun prove `(ISR1)` for this class and prove that it has no
nontrivial normal amenable subgroup.

In the scalar case `n=1`, if `N_b=L(R)`, equation `(ISR3)` is exactly
the kernel-generation hypothesis of
`normalizer-kernel-generation-forces-haar-action`. Thus the only ISR
survivor is already the compact-abelian Haar action lane; isotropy holonomy
supplies no separate compiler.
