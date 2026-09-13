---
rg: 2
id: homogeneous-quotient-soficity-gives-vertex-soficity-proof
kind: route
title: An exactly equivariant locally constant covering label turns metric microstates into orbit charts
target: homogeneous-quotient-soficity-gives-vertex-soficity
requires:
  - uniquely-ergodic-action-sofic-iff-topological-microstates
---

The notation is that of the target. GKP Definition 2.1 (v3, p. 3; transcribed in
`research/artifacts/fz-gkp-q42-review-2026-09-13.md`) is used verbatim. A map
`φ : A → Sym(V)` is *unital* if `φ(1) = 1`. It is `(F,ε)`-*multiplicative* if
`d(φ(gh), φ(g)φ(h)) < ε` for `g, h ∈ F`, where `d` is the normalized Hamming distance. It is an
`(F,E,ε)`-*orbit approximation* if there are a finite set `B`, a set `S ⊆ V` with
`|S| > (1−ε)|V|`, and injections `π_s : E ↪ B` for `s ∈ S`, such that
`π_(φ(g)s)(x) = π_s(g^(-1)x)` whenever `s ∈ S`, `g ∈ F`, `x ∈ E`, `φ(g)s ∈ S` and `g^(-1)x ∈ E`.

**Step 0 (labels).** `L/K` is discrete and `Λ_N` is cocompact, so `B_N = Λ_N\L/K` is finite.
Because `A ∩ K = C`, the map `aC ↦ aK` identifies `A/C` with the orbit `A·K ⊆ L/K`. Define
`f_x` by `(HV2)`. It is well defined, since `gλ` gives `Λ_N λ^(-1) g^(-1) x = Λ_N g^(-1) x`. It is
exactly equivariant:

```text
f_(hx)(hgΛ_N) = Λ_N g^(-1) h^(-1) h x = f_x(gΛ_N)       (h ∈ L).          (P1)
```

It is locally constant: if `x = aK`, then `f_x` is constant on the open neighbourhood
`(aKa^(-1))·y` of any `y`, because `aKa^(-1)` fixes `x`.

**Step 1 (separation).** Let `x = a_1K != x' = a_2K`. If `f_x(gΛ_N) = f_(x')(gΛ_N)`, then
`g^(-1)a_2K = λ g^(-1)a_1K` for some `λ ∈ Λ_N`. Hence

```text
λ ∈ h (KwK) h^(-1),     h = g^(-1)a_1,   w = a_1^(-1)a_2 ∉ K.               (P2)
```

*Lemma S.* For finite `W ⊆ L \ K` there is `N_0` such that, for `N >= N_0`, `Λ_N` meets no
`h(KwK)h^(-1)` with `h ∈ L`, `w ∈ W`.

*Proof.* `Λ_1\L` is compact, so `L = Λ_1 Ω` for a compact `Ω`. Put `Q = Ω K W K Ω^(-1)`, which
is compact. Then `Λ_1 ∩ Q` is finite, since `Λ_1` is discrete. It does not contain `1`, because
`1 ∈ ωKwKω^(-1)` would force `w ∈ K`. The `Λ_N` decrease and intersect in `{1}`, so some `Λ_(N_0)`
misses the finite set `Λ_1 ∩ Q`. Suppose `λ ∈ Λ_N ∩ h(KwK)h^(-1)` with `N >= N_0`, and write
`h = μω` with `μ ∈ Λ_1`, `ω ∈ Ω`. Then `μ^(-1)λμ ∈ Q`, and `μ^(-1)λμ ∈ Λ_N` by normality. This
contradicts the choice of `N_0`. ∎

Applying Lemma S to `W = {a_1^(-1)a_2 : a_1C != a_2C ∈ E}`, with fixed representatives, makes
`x ↦ f_x(y)` injective on `E` for **every** `y ∈ X_N`.

**Step 2 (orbit approximation).** Fix finite `F ⊆ A`, finite `E ⊆ A/C` and `ε > 0`. Choose `N`
by Step 1. The finitely many locally constant maps `f_x : X_N → B_N` (`x ∈ E`) on the compact metric
space `X_N` admit `δ > 0` with

```text
d(y, y') < δ   ⇒   f_x(y) = f_x(y')   for all x ∈ E.                        (P3)
```

Put `F' = F ∪ FF ∪ {1}` and `η = min(δ, ε/(2|F|+2))`, and take `(V, σ, y)` satisfying `(HV1)` for
`(F', η)`. Taking `s = t = 1` in `(HV1)` gives `σ(1)v = v` outside `η|V|` points. Define
`φ(1) = 1`, `φ(s) = σ(s)` for `s ∈ F' \ {1}`, and `φ(s) = 1` elsewhere.

* *Unital*: by definition.
* *Multiplicative*: for `g, h ∈ F` with `g, h, gh != 1`, `(HV1)` gives defect at most `η`. If
  `gh = 1`, compare with `σ(1)` and then with `1`, which gives defect at most `2η`. If `g = 1` or
  `h = 1` the identity is exact. So `d(φ(gh), φ(g)φ(h)) <= 2η < ε`.
* *Orbit approximation*: take `B = B_N`, `π_v(x) = f_x(y(v))`, and
  `S = {v : d(y(σ(g)v), g·y(v)) < η for all g ∈ F \ {1}}`. Every `π_v` is injective by Step 1, and
  `|V \ S| <= |F| η |V| < ε|V|`. For `v ∈ S`, `g ∈ F \ {1}`, `x ∈ E` with `g^(-1)x ∈ E`:

  ```text
  π_(φ(g)v)(x) = f_x(y(σ(g)v)) = f_x(g·y(v)) = f_(g^(-1)x)(y(v)) = π_v(g^(-1)x),
  ```

  by `(P3)` and then `(P1)`. For `g = 1` the identity is trivial. This holds without assuming
  `φ(g)v ∈ S`.

So `A ↷ A/C` is sofic. This proves item 1. ∎

**Item 2.** Item 1 of `uniquely-ergodic-action-sofic-iff-topological-microstates` says that a
sofic p.m.p. action of a countable sofic group by homeomorphisms of a compact metric space admits
microstates `(HV1)` for all `F` and `ε`. Its microstate definition is literally `(HV1)`. ∎

**Dyadic instance (checks used by the instances paragraph).**
* `SL_2(Z[1/2]) ∩ SL_2(Z_2) = SL_2(Z)` and `−1` lies in both, so `A ∩ K = C` in `PSL_2`.
* Torsion-free cocompact lattices exist in `SL_2(Q_2)`: unit groups of definite quaternion orders
  split at `2` (Borel--Harder in general), followed by Selberg's lemma. A torsion-free lattice
  avoids `−1` and maps isomorphically onto a cocompact lattice of `PSL_2(Q_2)`. It is finitely
  generated linear and hence residually finite (Mal'cev). The intersections of all subgroups of
  index at most `N` form the required normal tower.
* *Density and unique ergodicity.* The closure of `A` contains `K`, since `PSL_2(Z)` is dense in
  `K` (strong approximation), and it contains `d = diag(2,1/2)`. By the Cartan decomposition
  `L = ∪_n K d^n K`, the closure is `L`. The stabilizer of a Borel probability measure under the
  jointly continuous `L`-action on `X_N` is closed. So an `A`-invariant measure is `L`-invariant,
  and hence it is the Haar probability measure.
