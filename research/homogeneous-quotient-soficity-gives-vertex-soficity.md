---
rg: 2
id: homogeneous-quotient-soficity-gives-vertex-soficity
kind: claim
title: Topological microstates of a dense action on compact lattice quotients make the vertex coset action sofic
distinct_from:
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that asks whether the crossed product of the same compact system embeds in R^omega, allowing non-Cartan microstates; this turns permutation microstates of the compact system into GKP orbit approximations of the countable vertex action.
  finite-equidistributed-orbits-give-sofic-action: that builds models of one p.m.p. action from honest finite invariant sets; this transfers microstates of a compact system to a different countable set action, which carries no invariant measure, through an exactly equivariant separating label.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes exact finite common-level models of the K-orbit label; this uses the label only pointwise, so defective approximate models are allowed.
---

**ESTABLISHED (unreviewed).** Let `L` be a totally disconnected locally compact second countable
group, `K <= L` compact open, `A <= L` a countable subgroup and `C = A ∩ K`. Let `Λ_1 <= L` be a
cocompact lattice and `Λ_1 >= Λ_2 >= ...` finite-index normal subgroups of `Λ_1` with
`∩_N Λ_N = {1}`. Let `A` act on the compact metrizable space `X_N = L/Λ_N` by left translation.

1. Suppose that for every `N`, every finite `F ⊆ A` containing `1` and every `ε > 0` there are a
   finite set `V` and maps `σ : F → Sym(V)`, `y : V → X_N` with

   ```text
   |{v : σ(s)σ(t)v != σ(st)v}| <= ε|V|        (s, t, st ∈ F),
   |{v : d(y(σ(s)v), s·y(v)) >= ε}| <= ε|V|    (s ∈ F).                  (HV1)
   ```

   Then the coset action `A ↷ A/C` is sofic in the sense of Gao--Kunnawalkam Elayavalli--Patchell,
   Definition 2.1(5).
2. In particular it suffices that every p.m.p. action `A ↷ (X_N, Haar)` is sofic (Păunescu
   Definition 1.4), by item 1 of `uniquely-ergodic-action-sofic-iff-topological-microstates`
   (`A` is assumed sofic there; every residually finite `A` is).

**The mechanism.** For `x ∈ L/K` the label

```text
f_x(gΛ_N) = Λ_N g^(-1) x   ∈   Λ_N \ L / K   (a finite set)                 (HV2)
```

is exactly equivariant, `f_(hx)(h·y) = f_x(y)`, and locally constant. Once `Λ_N` avoids all
conjugates of finitely many double cosets `KwK`, it separates a given finite window of
`A/C ⊆ L/K` at **every** point of `X_N`. Microstates only have to be metrically almost equivariant.
The separating label, which is the hard part of any direct finite model of `A ↷ A/C`, comes for
free and exactly.

**Instances.**
* **Dyadic.** `L = PSL_2(Q_2)`, `K` the image of `SL_2(Z_2)`, `A = PSL_2(Z[1/2])`,
  `C = PSL_2(Z)`. `X_N` is the frame space of the finite `3`-regular graph `Λ_N\T`. The label
  `(HV2)` sends a tree vertex to its image under the covering `T → Λ_N\T` determined by the frame.
  Separation is the girth of `Λ_N\T`. Here `A` is dense in `L`, so `A ↷ X_N` is uniquely ergodic.
  Microstates are then equivalent to soficity of the p.m.p. action
  (`dyadic-homogeneous-quotient-admits-topological-microstates`). The conclusion is
  `dyadic-bruhat-tits-vertex-action-is-sofic` (route
  `dyadic-vertex-action-sofic-from-homogeneous-microstates`).
* The same statement applies verbatim to `SL_3(Z[1/2]) < SL_3(Q_2)`, to function-field pairs, and to
  every S-arithmetic pair with a compact open `K`.

**What it does not say.** The converse is unknown. A sofic vertex action need not come with marks
in `L/Λ_N`: a label configuration is a proper colouring of the tree, not a covering map onto a fixed
finite graph. Nothing is claimed about the crossed-product question
`sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`, except the standard remark (not
recorded as an edge) that p.m.p. soficity of `A ↷ X_N` gives Cartan microstates of that crossed
product.

**Credit.** The equivariant label `(HV2)` is the classical covering-map dictionary between frames
and lattice quotients of buildings. The observation that it converts topological microstates into
GKP orbit approximations was not found in the sources this graph carries. The literature check was
bounded to the GKP paper and the graph's own sofic-action nodes.

Proof in `homogeneous-quotient-soficity-gives-vertex-soficity-proof`.
