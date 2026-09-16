---
rg: 2
id: effaceable-cohomology-makes-inflation-an-isomorphism-proof
kind: route
title: Induct on the degree, killing an effaced class in the coinduced module and chasing the inflation ladder
target: effaceable-cohomology-makes-inflation-an-isomorphism
requires: []
artifacts:
  - research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md
---

The complete argument is Section 1 of the artifact, with the standard facts (F1)-(F3)
of its Section 0. What follows is that argument.

**Standard inputs.** For a finite `G`-module `M`, write `N(G;M)` for the finite-index
normal subgroups of `G` acting trivially on `M`.

- (F1) `H^q(G_hat;M) = colim_{U in N(G;M)} H^q(G/U;M)`, and `inf` is the colimit of the
  inflations `H^q(G/U;M) -> H^q(G;M)` (Serre, *Galois Cohomology* I.2.2, Prop. 8). This
  is the description used in `good-no-persistent-cohomology-proof`.
- (F2) A short exact sequence of finite `G/U`-modules gives long exact sequences for `G`
  and, as a directed colimit of exact sequences, for `G_hat`. Inflation is a map of long
  exact sequences, connecting maps included, because it comes from a map of cochain
  complexes natural in the module.
- (F3) Shapiro. Let `U` be normal of finite index in a group `Γ` and act trivially on `M`.
  Put `M* = Map(Γ/U,M)` with `(g f)(x) = g f(g^{-1}x)`. Let `η: M -> M*` be the constant
  functions and `ε(f) = f(U)`. Then `σ = ε_* ∘ res^Γ_U : H^q(Γ;M*) -> H^q(U;M)` is an
  isomorphism, and `σ ∘ η_* = res^Γ_U` (Brown, *Cohomology of Groups* III.5-6).

**Proof.** We induct on `n`.

*Base case `n = 0`.* By (F1), `H^0(G_hat;M) = colim M^{G/U} = M^G`, and `inf_0` is the
identity. So `(A_0)` holds for every group.

*Inductive step.* Let `n >= 1` and assume `(E_n)`. By induction `(A_{n-1})` holds. Fix a
finite `M`. For `U in N(G;M)` put `M* = Map(G/U,M)` and `M'' = M*/η(M)`. These are finite
`G`-modules on which `U` acts trivially. (F2) gives a commutative ladder with exact rows:

```text
H^{n-1}(G_hat;M*) -> H^{n-1}(G_hat;M'') -δ^-> H^n(G_hat;M) -η^-> H^n(G_hat;M*)
      | a                  | b                  | c = inf_n        |
H^{n-1}(G;M*)     -> H^{n-1}(G;M'')     -δ->  H^n(G;M)    -η->  H^n(G;M*)
```

Here `a` and `b` are isomorphisms by `(A_{n-1})`.

*`c` is onto.* Take `x in H^n(G;M)`. By `(E_n)` some finite-index `W <= G` has
`res^G_W x = 0`. Let `U` be the normal core of `W` intersected with the kernel of the
action on `M`; then `U in N(G;M)` and `res^G_U x = res^W_U res^G_W x = 0`. Use the ladder
for this `U`. Then `σ(η_* x) = res^G_U x = 0` and `σ` is
injective, so `η_* x = 0`. Hence `x = δ(w)`. Write `w = b(ŵ)`. Then `c(δ^ ŵ) = x`.

*`c` is one-to-one.* Take `y` with `c(y) = 0`. By (F1), `y` is the image of some
`z in H^n(G/U;M)` with `U in N(G;M)`; use the ladder for this `U`. As a `G/U`-module, `M*`
is coinduced from the trivial subgroup ((F3) with `Γ = G/U`). So
`H^n(G/U;M*) ≅ H^n(1;M) = 0`, which gives `η_* z = 0` and `η^ y = 0`. Therefore `y = δ^ v`.
Then `δ(b v) = c(y) = 0`, so `b v` is the image of some `w in H^{n-1}(G;M*)`. Write
`w = a(ŵ)`. Let `v'` be the image of `ŵ` in `H^{n-1}(G_hat;M'')`. Then `b(v') = b(v)`, and
`b` is injective, so `v = v'` lies in the image of the top-left map. Hence `y = δ^ v = 0`.

So `inf_n` is bijective for every finite `M`, and `(A_n)` follows. `QED`

The converse is `good-no-persistent-cohomology-proof`, read degree by degree.
