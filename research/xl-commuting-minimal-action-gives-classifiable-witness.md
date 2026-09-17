---
rg: 2
id: xl-commuting-minimal-action-gives-classifiable-witness
kind: claim
title: A commuting free minimal amenable-group action on an amenable G-space yields an XL witness
distinct_from:
  stw40-unital-nuclear-no-trace-iff-exact: that produces the nonsimple commutative model C(X); here a second, commuting, amenable group Gamma acting freely and minimally on X turns C(X) into the simple stably finite classifiable algebra C(X) x Gamma while keeping the G-action amenable.
  stw40-trace-simplex-boundary-is-topologically-amenable: that is a necessary condition on any witness; this is a sufficient condition producing witnesses.
---

Let `G` be a countable group and let `Gamma` be a countable amenable group.
Let `X` be a compact metrizable space carrying commuting continuous actions of
`G` and `Gamma` (equivalently an action of `G x Gamma`) such that

1. `G` acts topologically amenably on `X`;
2. `Gamma` acts freely and minimally on `X`, and `X` is infinite;
3. `C(X) x Gamma` has finite nuclear dimension (for instance `dim X < infinity`
   and `Gamma` has finite dynamic asymptotic dimension, e.g. `Gamma = Z^d`
   or `Gamma` locally finite).

Put `A = C(X) x Gamma` and `alpha_g(f u_gamma) = (f o g^-1) u_gamma`.
Then `A` is unital, separable, simple, nuclear, `Z`-stable, satisfies the UCT
and has a trace (hence is stably finite), i.e. `A` is a unital stably finite
classifiable C-star algebra, and `alpha` is an amenable action of `G`.
Its trace simplex is `M_Gamma(X)` and `A x_alpha G = C(X) x (G x Gamma)`.

Consequently **Problem XL holds for `G` as soon as `G` admits such a space**:
a compact metrizable finite-dimensional amenable `G`-space with a commuting
free minimal `Z`-action (or locally finite group action).  The key step is a
Følner averaging of the Reiter witnesses over `Gamma`, which makes them
approximately central for the unitaries `u_gamma` while leaving them exactly
central for `C(X)` and approximately `G`-equivariant.

The companion obstruction
`xl-commuting-minimal-action-forbids-proximal-factors` shows that such an `X`
can never factor onto a nontrivial proximal `G`-flow (in particular not onto a
boundary), which kills every shift-over-a-boundary or skew-product-over-a-
boundary construction of `X`.
