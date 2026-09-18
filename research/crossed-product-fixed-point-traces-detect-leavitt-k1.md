---
rg: 2
id: crossed-product-fixed-point-traces-detect-leavitt-k1
kind: claim
title: In characteristic p, a p-element of the acting group whose fixed-point set carries a centralizer-invariant functional nonzero on 1 makes K_1 of the Leavitt tensor of the crossed product nonzero
distinct_from:
  leavitt-tensor-k1-sees-traces-of-nilpotent-matrices: that is the detector K_1(B ⊗ L) -> k for an arbitrary algebra B with a given trace; this builds the traces on a crossed product LC(X, k) ⋊ Λ from fixed points of p-elements (a fixed-point "measure" on Fix(g) invariant under the centralizer), so that the detector fires for actions that are minimal and topologically free.
  farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts: that proves K(B ⊗ L) = 0 when every finite subgroup acts freely; this proves K_1(B ⊗ L) != 0 as soon as one p-element has a fixed point with this invariant functional, with no hypothesis on the acting group.
  free-action-leavitt-tensor-hosts-have-trivial-k1-k2: that is the open vanishing statement for free actions, whose necessity section uses a trivial (non-effective) Z/2 action; this shows the same failure for effective, even minimal topologically free, actions, where the crossed product is central simple.
---

**ESTABLISHED (elementary, from established claims; unreviewed).** Route:
`crossed-product-fixed-point-traces-detect-leavitt-k1-proof`.

Let `k` be a field of characteristic `p > 0` and `L = L_k(1,2)`. Let a group `Λ`
act by homeomorphisms on a compact Hausdorff zero-dimensional space `X`, and let
`B = LC(X, k) ⋊ Λ`, with `u_γ f u_γ^(-1) = f ∘ γ^(-1)`.

**Theorem.** Suppose one of the following holds.

- **(F) Fixed-point functional.** Some `g ∈ Λ`, `g ≠ e`, `g^(p^j) = e`, has a
  `k`-linear `ν : LC(Fix(g), k) -> k` with `ν(1) ≠ 0` and `ν(f ∘ c) = ν(f)` for
  every `c` in the centralizer `C_Λ(g)`.
- **(M) Invariant mass.** `Λ` has a nontrivial element `g` of `p`-power order, and
  there is a `Λ`-invariant `k`-linear `μ : LC(X, k) -> k` with `μ(1) ≠ 0`.

Then `x = 1 - u_g` is nilpotent, and `[1 + x ⊗ e_1] ≠ 0` in `K_1(B ⊗ L)`. In
particular `K_1(B ⊗ L) ≠ 0`.

**Easiest instance of (F).** `g` of order `p` (or `p^j`) fixes a point `ξ_0`
that its whole centralizer fixes, or more generally `Fix(g)` contains a finite
`C_Λ(g)`-invariant set of size prime to `p` (take `ν` = counting mod `p`).

**Dictionary (the entropy-measure transplant).** Traces of `B` vanishing on
`[B, B]` are built from `k`-valued finitely additive invariant "measures":
- identity component: `Λ`-invariant measures on `X` (case (M));
- the component of a conjugacy class `[g]`: `C_Λ(g)`-invariant measures on
  `Fix(g)` (case (F)).
A `p`-element contributes the nilpotent `1 - u_g`, and the detector
`leavitt-tensor-k1-sees-traces-of-nilpotent-matrices` reads its trace. So
`K_1(B ⊗ L) = 0` forces every such measure to vanish on `1`, for every
`p`-element: a mass condition on fixed-point sets of torsion.

**What it kills.** Every proof of `K_1(B ⊗ L) = 0` for crossed products that
uses only effectiveness, minimality, topological freeness, finite presentation,
central simplicity, or the Farrell–Jones conjecture for `Λ` dies: the
finitely presented central simple example
`fp-central-simple-host-with-nonzero-leavitt-k1` (over the virtually free, hence
hyperbolic, group `F_2 ⋊ Z/2` acting on `∂F_2`) has all of these and satisfies
(F). The step where such a proof dies is the passage from free finite subgroups
(`farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`) to finite
subgroups acting with fixed points: the invariant is `ν(1)` on `Fix(g)`.

**Scope.** Only a sufficient condition for `K_1 ≠ 0` is claimed. Whether odd
(prime-to-`p`) torsion may have fixed points without harming vanishing is not
claimed here; a heuristic (locally the ring is ultramatricial when point
stabilizers have order prime to `p`) suggests it can, see the route's remark.
