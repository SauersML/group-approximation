---
rg: 2
id: fpbs-price-one-forests-have-infinitely-many-components-proof
kind: route
title: The coset lift of a k-component invariant forest, with hairs to the marked tree, is a treeing of cost 1+(E deg/2-1)/k
target: fpbs-price-one-forests-have-infinitely-many-components
requires:
  - gaboriau-treeable-free-action-realizes-min-cost
  - fpbs-non-fixed-price-one-has-nonuniqueness
---

The only imports are items 1–3 of `gaboriau-treeable-free-action-realizes-min-cost` (Gaboriau's
lecture notes, Theorem 2.24 and Corollary 2.26, quoted verbatim in its citation node). Part 3 also uses
`fpbs-non-fixed-price-one-has-nonuniqueness` to name the open class. Notation: `Ω` is the space of
spanning subgraphs of `G`. `Γ` acts on `Ω` by `(γω) = {{γg,γh} : {g,h}∈ω}`, which preserves `G`
because edges are `{g,gs}`. `ν` is the invariant law of `ω`.

**Step 0 (a free action carrying the forest).** Let `X = Ω×[0,1]^Γ` with `μ = ν⊗Leb^{⊗Γ}`. Let `Γ`
act diagonally by `γ(ω,u) = (γω, u(γ^{-1}·))`. This action is p.m.p. The Bernoulli factor is
essentially free: almost surely the values `u(g)` are pairwise distinct, and `γu=u` with `γ≠e` would
force `u(γ^{-1})=u(e)`. So the diagonal action is essentially free. Discard the null set of points with
nontrivial stabiliser (it is invariant) and write `ω(x)` for the first coordinate. Equivariance
`ω(γx)=γω(x)` holds by construction.

**Step 1 (reduction to exactly k components).** Let `K(x)∈{1,2,…,∞}` be the number of components of
`ω(x)`. Left translation maps components of `ω(x)` bijectively to components of `γω(x)`, so `K` is
`Γ`-invariant. If `P(K<∞)>0` then `μ(K=k)>0` for some finite `k`. Restricting `μ` to `X_k={K=k}` and
normalising gives a free p.m.p. action on which `ω` has exactly `k` components everywhere. Moreover
`E deg` computed under the restriction is the conditional mean degree. Part 1 assumes `K=k` a.s., so
there `X_k=X`. For part 2 it suffices to derive a contradiction on `X_k`. From now on assume `K≡k`
on `X`.

**Step 2 (the coset lift).** Enumerate `Γ={γ_1=e,γ_2,…}`. For a component `C` of `ω(x)` call
`lead(C)` the element of `C` of least index. Let

`X̃ = {(x,j) : x∈X, γ_j = lead(C) for some component C of ω(x)}`,

a Borel subset of `X×N`. Identify `(x,j)` with the pair `(x,C)`. Each fibre has exactly `k` points.
Put `μ̃ = (1/k)(μ⊗counting)` restricted to `X̃`, a probability measure. Define

`γ·(x,C) = (γx, γC)`.

This is well defined because `γC` is a component of `γω(x)=ω(γx)`. It is a Borel action: the label
of `γC` is a Borel function of `(γ,x,j)`, since components are determined by finitely many
coordinates up to each finite radius. It preserves `μ̃`, because `μ` is invariant and `C↦γC` is a
bijection between fibres, so `μ⊗counting` is invariant. It is free, because `γ·(x,C)=(x,C)` forces
`γx=x` and hence `γ=e`.

**Step 3 (the orbit picture).** Fix `(x,C)∈X̃` and identify its orbit with `Γ` via
`g ↦ g^{-1}·(x,C) = (g^{-1}x, g^{-1}C)`. This is a bijection by freeness. Call the point `g` *marked*
if `e ∈ g^{-1}C`, that is, if `g∈C`. Note `ω(g^{-1}x) = g^{-1}ω(x)`, so
`{e,s}∈ω(g^{-1}x)` iff `{g,gs}∈ω(x)`.

**Step 4 (the graphing Ψ̃).** For `y=(ω,u)∈X` write `u_y=u`. The shift satisfies
`u_{h^{-1}y}(e)=u_y(h)`. Consider the following partial Borel isomorphisms of `X̃`, each of the form
`z ↦ γ^{-1}·z` on a Borel domain.

- *Tree edges.* For `s∈S`, let `A_s={(y,D) : e∈D, {e,s}∈ω(y)}` and let `φ_s(z)=s^{-1}·z` on
  `A'_s = A_s ∩ {u_y(e)<u_y(s)}`. If `e∈D` and `{e,s}∈ω(y)`, then `s∈D`, so
  `s^{-1}·(y,D)=(s^{-1}y,s^{-1}D)` again has `e∈s^{-1}D`. The uniform labels orient each forest edge
  once. This avoids a double edge when `s=s^{-1}`. Ties `u_y(g)=u_y(h)` with `g≠h` form a null set, which
  we discard.
- *Hairs.* For `j≥2`, let `ψ_j(z)=γ_j^{-1}·z` on `B_j={(y,D) : e∉D, lead(D)=γ_j}`. Since
  `γ_j∈D`, the image `(γ_j^{-1}y, γ_j^{-1}D)` has `e∈γ_j^{-1}D`, so it is marked. The sets `B_j`
  partition `{e∉D}`.

Let `Ψ̃ = {φ_s}_{s∈S} ∪ {ψ_j}_{j≥2}`.

**Step 5 (Ψ̃ is a treeing of the orbit relation).** Put `g` in the orbit coordinates of Step 3.

- `φ_s` is defined at `g` iff `g∈C`, `{g,gs}∈ω(x)` and `u_x(g)<u_x(gs)`, since
  `u_{g^{-1}x}(e)=u_x(g)` and `u_{g^{-1}x}(s)=u_x(gs)`. It sends `g` to `gs`, because
  `s^{-1}g^{-1}·(x,C) = (gs)^{-1}·(x,C)`. An edge `{g,h}` of `ω(x)` inside `C` with `h=gs` is
  produced exactly once: by `φ_s` at `g` if `u_x(g)<u_x(h)`, and otherwise by `φ_{s^{-1}}` at `h`.
  So the maps `φ_s` put on the marked set `C` exactly the edges of `ω(x)` inside `C`, each once. Since `C` is a component of a
  forest, these edges form a tree spanning `C`.
- `ψ_j` is defined at `g` iff `g∉C` and `lead(g^{-1}C)=γ_j`. It sends `g` to `gγ_j`, and
  `gγ_j∈C` by Step 4. Each unmarked `g` lies in exactly one `B_j`. So `g` has exactly one hair
  edge, and it ends in `C`. No hair starts at a marked point.

The graph that `Ψ̃` induces on the orbit is therefore the tree `C` with one pendant edge attached at
every vertex of `Γ∖C`. That graph is a tree spanning the whole orbit. Every edge joins points of one
orbit, and every orbit is connected by `Ψ̃`, so `Ψ̃` generates the orbit equivalence relation `R̃` of
the lifted action. Hence `Ψ̃` is a treeing of `R̃`, and the lifted action is a free p.m.p. treeable
action of `Γ`.

**Step 6 (the cost of Ψ̃).** For every `x`, exactly one component of `ω(x)` contains `e`.

- *Tree edges.* `μ̃(A_s) = (1/k) μ({e,s}∈ω)`. The map `φ_s` carries `A_s∩{u(e)<u(s)}`
  measure-preservingly onto `A_{s^{-1}}∩{u(e)>u(s^{-1})}`, because
  `u_{s^{-1}y}(e)=u_y(s)` and `u_{s^{-1}y}(s^{-1})=u_y(e)`. So
  `μ̃(A'_s)+μ̃(A'_{s^{-1}}) = μ̃(A_s)`, and summing over `s∈S` gives
  `Σ_s μ̃(A'_s) = (1/2)Σ_s μ̃(A_s) = E deg_ω(e)/(2k)`.
- *Hairs.* `Σ_j μ̃(B_j) = μ̃(e∉D) = (1/k)(k−1) = 1−1/k`.

Hence `C(Ψ̃) = E deg_ω(e)/(2k) + 1 − 1/k = 1 + (E deg_ω(e)/2 − 1)/k`.

**Step 7 (conclusions).**

- *Part 1.* By item 1 of the import, `C(R̃)=C(Ψ̃)`. By item 2, a free p.m.p. treeable action of
  `Γ` has cost `C_*(Γ)`. So `C_*(Γ) = 1 + (E deg_ω(e)/2 − 1)/k`. A group with a free p.m.p. treeable
  action is treeable by definition.
- *Part 2.* Suppose `Γ` is nonamenable, `C_*(Γ)=1`, and `P(K<∞)>0`. Step 1 gives `k` with
  `μ(K=k)>0`, and Steps 2–6 applied to `X_k` give a free p.m.p. treeable action of `Γ`. By item 2 it
  has cost `C_*(Γ)=1`. So `Γ` is a nonamenable group with a free p.m.p. action of cost one. By item 3,
  `Γ` is non-treeable, which contradicts the treeable action just built. Hence `K=∞` almost surely.
- *Part 3.* The FMSF (edges that are not the label maximum on any cycle) and the WMSF (edges that
  are not the maximum on any cycle or bi-infinite path) are acyclic spanning subgraphs. They are
  `Γ`-equivariant functions of iid uniform edge labels, so their laws are invariant. The FUSF and
  WUSF are the weak limits along an exhaustion `(V_n)`, and the limit does not depend on the
  exhaustion. `(γV_n)` is again an exhaustion, so the limit laws are `Γ`-invariant. By
  `fpbs-non-fixed-price-one-has-nonuniqueness`, every group not settled by that node has fixed price
  1, hence `C_*(Γ)=1`. For a nonamenable such group, apply part 2.

**Remarks.**

- Step 5 is the only place where "finitely many components" is used. With infinitely many
  components the coset space `X̃` has infinite fibre measure. No normalisation gives a p.m.p.
  lift, and the hair construction degenerates. This is exactly where fixed-price-one groups escape.
- The formula is a restatement of the induction formula
  `C(R)−1 = μ(Y)(C(R↾Y)−1)` (Gaboriau's notes, Proposition 2.33) applied to the complete section
  `Y={e∈D}` of measure `1/k`. The route above avoids that import by building the treeing directly.
