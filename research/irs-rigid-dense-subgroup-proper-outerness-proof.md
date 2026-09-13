---
rg: 2
id: irs-rigid-dense-subgroup-proper-outerness-proof
kind: route
title: Kill the central case with the stabilizer IRS and a closed stabilizer, and the factor case with mixing along the escaping element
target: irs-rigid-simple-dense-subgroups-act-properly-outer
requires:
  - creutz-peterson-factor-representation-rigidity-steps
---

Notation as in the claim.

**Step 0: the action is faithful and mixing off the constants.**
- `ker α = {g : α_g = id}` is a closed normal subgroup of `G`. If it were `G`, all of `M_0`
  would be invariant and ergodicity would force `M_0 = C`. So `ker α = {e}`.
- The Koopman representation `g -> α_g` on `L^2(M_0, τ)` is strongly continuous. Let `P` be
  the projection onto its invariant vectors. For `x in M_0`, `P x` is the element of minimal
  norm in the `||·||_2`-closed convex hull of `{α_g(x)}` (Alaoglu--Birkhoff). That hull lies
  in the operator-norm ball of radius `||x||`, which is `||·||_2`-closed in `L^2(M_0)`. So
  `P x in M_0` is invariant, hence scalar. `M_0` is dense in `L^2(M_0)`, so `P` is the
  projection onto `C1`.
- By the Howe--Moore property, `<α_g ξ, η> -> 0` as `g -> infinity` for all `ξ, η` in
  `L^2(M_0) ⊖ C1`.

**Step 1: the reduction.** This is imported: item (CP-f) of
`creutz-peterson-factor-representation-rigidity-steps`, the opening of the proof of their
Proposition 4.1. Suppose `λ in Λ \ {e}` and `0 ≠ v in M_0` satisfy `α_λ(x) v = v x` for all
`x`. After polar decomposition, `v` may be taken to be a partial isometry. Then
`p = v*v = vv*` is a nonzero central projection with `α_λ(p) = p`, and `α_λ(q) = q` for every
central projection `q <= p`, so `α_λ` is the identity on `Z(M_0)p`. If `M_0` is a factor then
`p = 1`, `v` is unitary and `α_λ = Ad(v)`.

**Step 2: `M_0` is a factor.** Suppose not.
- Write `Z(M_0) = L^∞(Y, ν)` for a standard probability space, with `ν` induced by `τ`
  (separable predual). `Z(M_0)^G ⊂ M_0^G = C`, so `G` acts ergodically on `Z(M_0)`.
- `Λ` is countable, so by Mackey's point realization its action comes from a Borel
  measure-preserving action on `(Y, ν)`.
- Let `E` be the support of `p`, so `ν(E) = τ(p) > 0`. `λ` is the identity on `L^∞(E)`.
  Take countably many Borel sets `A_k` separating the points of `Y`. For each `k`,
  `λ(A_k ∩ E) = A_k ∩ E` modulo null sets. So for almost every `y in E`, `y` and `λy` lie in
  the same `A_k` for all `k`, that is `λy = y`.
- `y -> Stab_Λ(y)` is Borel with `Stab_Λ(μy) = μ Stab_Λ(y) μ^(-1)`, so its law `θ` is an
  invariant random subgroup of `Λ`. By (PO2), `θ = t δ_e + (1-t) δ_Λ`. Since `λ ≠ e` and
  `θ({H : λ in H}) >= ν(E) > 0`, we get `1 - t >= ν(E) > 0`.
- So `F = {y : Stab_Λ(y) = Λ}` is `Λ`-invariant with `ν(F) = 1-t > 0`. The subgroup
  `{g in G : α_g(1_F) = 1_F}` is closed, by continuity, and contains the dense `Λ`, so it is
  `G`. By ergodicity `1_F = 1`, so almost every point is fixed by all of `Λ`.
- Hence every element of `Λ` is the identity on `Z(M_0)`. The subgroup
  `{g : α_g(z) = z for all z in Z(M_0)}` is closed and contains `Λ`, so it is `G`, and
  ergodicity gives `Z(M_0) = C`. Contradiction.

**Step 3: the factor case.** By Step 1, `α_λ = Ad(v)` for a unitary `v`.
- `H = {h in G : α_h in Inn(M_0)}` is a subgroup, and it is normal because
  `α_g ∘ Ad(u) ∘ α_g^(-1) = Ad(α_g(u))`. So `H ∩ Λ` is a normal subgroup of `Λ` containing
  `λ ≠ e`, and by (PO1) it is all of `Λ`. In particular `α_{γ_0} = Ad(u)` for a unitary `u`.
- `u` is not a scalar. Otherwise `α_{γ_0} = id`, so `γ_0 in ker α = {e}` by Step 0, which is
  impossible since `γ_0^n -> infinity`.
- `α_{γ_0}(u) = u u u* = u`, so `α_{γ_0^n}(u) = u` for all `n`. The vector
  `w = u - τ(u)1` is nonzero and lies in `L^2(M_0) ⊖ C1`, and `<α_{γ_0^n} w, w> = ||w||_2^2`
  for all `n`. By Step 0 and (PO3) this tends to 0. Contradiction.

So no `λ ≠ e` is implemented by a nonzero intertwiner, and the restriction of `α` to `Λ` is
properly outer.
