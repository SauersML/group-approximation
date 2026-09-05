---
rg: 2
id: stw99-lxxvi-pure-coefficients-kill-scalar-unstable-homotopy
kind: claim
title: Simple pure coefficients kill every stably trivial scalar unitary class before Z-stabilization
artifacts:
  - research/artifacts/stw99-lxxvi-scalar-unstable-homotopy-audit-2026-09-05.md
distinct_from:
  stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes: that assumes a unital copy of Z; this uses almost divisibility and stable rank one to obtain finite prime dimension-drop maps, with no compatible inductive system or Z embedding.
  stw99-lxxvi-dimension-drop-subalgebra-kills-s6-class: that assumes one finite block and treats one degree; this derives all needed block maps from purity and treats every scalar unstable degree.
---

Let `A` be a unital stable-rank-one C*-algebra with almost divisible
`Cu(A)`. For all `r>=1`, `k>=1`, and

```text
alpha in ker(pi_k(U(r)) -> pi_k(U(infinity))),
```

the scalar-extension image of `alpha` in `pi_k(U(M_r(A)))` is zero.

Consequently the same statement holds for every unital separable simple
pure C*-algebra `A`: the finite case has stable rank one by Lin, and
the purely infinite case is K-stable. In particular there is no simple
pure coefficient preserving the scalar rank-two `S^6` clutching class.

For spheres of every dimension at least two, stably isomorphic complex
vector bundles of the same rank therefore become isomorphic as
`A`-module bundles after scalar extension to such a coefficient.
They cannot first become isomorphic after tensoring that coefficient
with `Z`.

The key imported theorem is Rørdam--Winter's divisibility criterion:
the compact-unit inequalities `n x <= [1_A] <= (n+1)x` in `W(A)` yield
a unital *-homomorphism `Z_(n,n+1) -> A`. Injectivity of that homomorphism
is unnecessary. Choosing `n` sufficiently large makes the endpoint
unitary groups stable in two consecutive homotopy degrees; coprimality
then removes the remaining homotopy-pullback obstruction.

This concerns scalar classes coming from `U(r)`. It does not prove that
the full stabilization map on `pi_k(U(p(A tensor K)p))` is injective for
an arbitrary projection corner and a coefficient-dependent homotopy class.

ROUTES

stw99-lxxvi-pure-dimension-drop-scalar-kernel-proof
