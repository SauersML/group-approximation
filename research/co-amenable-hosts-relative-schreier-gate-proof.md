---
rg: 2
id: co-amenable-hosts-relative-schreier-gate-proof
kind: route
title: Restrict the coset mean to a subgroup, convert it to Folner sets by Day-Namioka, and bound the Cheeger constants of the stabilizer Schreier graphs from below
target: co-amenable-hosts-inherit-the-relative-schreier-gate
requires: []
---

Notation as in the claim: `G` countable, `H ≤ G` co-amenable with `G`-invariant mean `m` on
`ℓ^∞(G/H)`, `Λ ≤ G` with finite generating set `S`, and `L_g = Λ ∩ gHg^{-1}`.

Throughout, the *Schreier graph* `Sch(Λ, L, S)` of a left `Λ`-set `Λ/L` has vertex set `Λ/L` and,
for each `s ∈ S`, one undirected edge `{x, sx}` per vertex `x` (so a loop, when `sx = x`, counts
`2` towards the degree). Its degree is `2|S|` at every vertex. For a finite `A ⊆ Λ/L` we write
`∂A` for the set of edges with exactly one endpoint in `A`, `E(A)` for the set of edges with both
endpoints in `A`, and `h = inf_A |∂A|/|A|`. The identity

  `|∂A| = Σ_{v ∈ A} deg(v) − 2|E(A)|`   (†)

is the handshake count.

---

## Step 0. Restriction

`m` is `G`-invariant, hence `Λ`-invariant. So the `Λ`-set `X := G/H` carries a `Λ`-invariant mean.
The `Λ`-orbit of `gH` is `Λ·gH ≅ Λ/L_g` as a `Λ`-set, and `L_g = Λ ∩ gHg^{-1} ≤ gHg^{-1} ≅ H`, so
`L_g ∈ 𝒮_H(Λ)`. This proves item 0's first sentence and identifies the orbits. ∎

---

## Step 1. Følner's criterion for actions (Day's convexity trick and Namioka's layer cake)

**Lemma 1.** Let a group `Λ` act on a countable set `X`, let `S ⊆ Λ` be finite, and suppose
`ℓ^∞(X)` carries a `Λ`-invariant mean. Then for every `ε > 0` there is a finite nonempty `A ⊆ X`
with `Σ_{s ∈ S} |sA Δ A| < ε|A|`.

*Proof.* Let `P(X) ⊆ ℓ^1(X)` be the set of finitely supported probability vectors. A mean on
`ℓ^∞(X)` is a state on the commutative C\*-algebra `ℓ^∞(X) = C(βX)`, i.e. a Radon probability
measure on `βX`; `X` is dense in `βX`, so the weak\* closed convex hull of `{δ_x : x ∈ X}` is all
of the state space. Hence `P(X)` is weak\*-dense in the set of means, and there is a net
`q_i → m` weak\*.

For `s ∈ Λ` put `(s·q)(x) = q(s^{-1}x)`. Weak\* convergence in `ℓ^∞(X)^*` restricted to the
subspace `ℓ^1(X)` is exactly the weak topology `σ(ℓ^1, ℓ^∞)`. Since `m` is `Λ`-invariant,
`(s·q_i − q_i)_{s ∈ S} → 0` weakly in `⊕_{s ∈ S} ℓ^1(X)`. The set

  `V = { (s·q − q)_{s ∈ S} : q ∈ P(X) } ⊆ ⊕_{s ∈ S} ℓ^1(X)`

is convex, and `0` lies in its weak closure; by Mazur's theorem the weak and norm closures of a
convex set coincide, so `0` lies in the norm closure of `V`. (This is the same convexity step as
Step 2 of `co-amenable-hyperfinite-transfer-proof`.) Choose `q ∈ P(X)` with
`Σ_{s ∈ S} ‖s·q − q‖_1 < ε`.

Layer cake: for `t > 0` set `A_t = {x : q(x) > t}`, a finite set, empty for `t ≥ 1`. For
non-negative `u, v ∈ ℓ^1(X)`,
`‖u − v‖_1 = Σ_x ∫_0^∞ |1_{u(x) > t} − 1_{v(x) > t}| dt = ∫_0^∞ |{u > t} Δ {v > t}| dt`.
Since `{s·q > t} = s{q > t} = sA_t`, we get `‖s·q − q‖_1 = ∫_0^∞ |sA_t Δ A_t| dt`, and
`∫_0^∞ |A_t| dt = ‖q‖_1 = 1`. Therefore

  `∫_0^∞ ( Σ_{s ∈ S} |sA_t Δ A_t| ) dt < ε = ε ∫_0^∞ |A_t| dt`,

so for some `t ∈ (0,1)` the integrands satisfy `Σ_{s∈S} |sA_t Δ A_t| < ε |A_t|` with `A_t ≠ ∅`. ∎

**Lemma 1'.** In the situation of Lemma 1, `1_Λ ≺ ℓ^2(X)`: the unit vectors `|A|^{-1/2} 1_A`
obtained from Lemma 1 satisfy `‖s·1_A − 1_A‖_2^2 = |sA Δ A| < ε|A|` for `s ∈ S`, and `S`
generates. ∎

**Lemma 1''.** Let `S` be a finite generating set of `Λ` acting on a countable set `X`. Then
`ℓ^∞(X)` carries a `Λ`-invariant mean **iff** `h(Sch(Λ, X, S)) = 0`. Moreover `X` is the disjoint
union of its `Λ`-orbits, the Schreier graph has no edges between orbits, and hence
`h(Sch(Λ, X, S)) = inf_{orbits} h(Sch(Λ, Λ/L_g, S))`.

*Proof.* For each `s ∈ S` the edges of `Sch(Λ, X, S)` of type `s` that lie in `∂A` are exactly the
`{x, sx}` with `x ∈ A Δ s^{-1}A`, so their number is `|sA Δ A|`; summing,
`|∂A| = Σ_{s ∈ S} |sA Δ A|`. If there is an invariant mean, Lemma 1 gives `A` with
`|∂A| < ε|A|` for every `ε`, so `h = 0`. Conversely if `h = 0`, take `A_n` with
`|∂A_n| < |A_n|/n`; then `|sA_n Δ A_n| < |A_n|/n` for every `s ∈ S`, and for a general `λ ∈ Λ`,
writing `λ = s_k ⋯ s_1` in the letters of `S ∪ S^{-1}`, the triangle inequality
`|λA Δ A| ≤ Σ_j |s_j (s_{j-1} ⋯ s_1 A) Δ (s_{j-1} ⋯ s_1 A)|` and `|s^{-1}A Δ A| = |A Δ sA|` give
`|λA_n Δ A_n| ≤ k(λ)|A_n|/n → 0` relative to `|A_n|`. Any weak\* cluster point of the normalized
counting measures `|A_n|^{-1} 1_{A_n} ∈ ℓ^1(X) ⊆ ℓ^∞(X)^*` is then a `Λ`-invariant mean. The last
sentence holds because every edge `{x, sx}` joins two points of the same orbit. ∎

---

## Step 2. Item 1, the gate

By Step 0 and Lemma 1'' applied to `X = G/H`,

  `inf_{g ∈ G} h(Sch(Λ, L_g, S)) = h(Sch(Λ, G/H, S)) = 0`.

Every `L_g` lies in `𝒮_H(Λ)`, so `κ(Λ, S, 𝒮_H(Λ)) = 0`. Contrapositive: a group `Λ` with a finite
generating set `S` and `κ(Λ, S, 𝒮_H(Λ)) > 0` admits no embedding into `G`, since such an embedding
would make the displayed infimum positive.

Note that `𝒮_H(Λ)` is defined by *abstract* embeddability of subgroups of `Λ` into `H`, so
`κ(Λ, S, 𝒮_H(Λ))` depends only on the isomorphism types of `Λ` and `H`, not on any embedding. ∎

---

## Step 3. The free Schreier bound: `κ_H(F_2) ≥ 2` when `H` has no non-abelian free subgroup

**Lemma 2.** Let `Λ` be free with basis `{a, b}` and `S = {a, b}`, so `Sch(Λ, L, S)` is
`4`-regular. Let `L ≤ Λ` be trivial or infinite cyclic. Then `|∂A| ≥ 2|A|` for every finite
`A ⊆ Λ/L`; hence `h(Sch(Λ, L, S)) ≥ 2`.

*Proof.* `Cay(Λ, S)` is the `4`-regular tree `T` (vertices `Λ`, edges `{x, xs}` for `s ∈ S`). The
map `xL ↦ Lx^{-1}` sends `Λ/L` bijectively to `L\Λ` and sends the edge `{xL, sxL}` to
`{Lx^{-1}, Lx^{-1}s^{-1}}`; since `S^{-1}` spans the same undirected Cayley graph as `S`, it is an
isomorphism of graphs from `Sch(Λ, L, S)` onto the quotient graph `T/L`, where `L` acts on `T` by
left translation. That action is free on vertices (`wx = x` forces `w = 1`).

*Case `L = 1`.* Then `Sch = T` is a tree, so `|E(A)| ≤ |A| − 1`, and (†) gives
`|∂A| ≥ 4|A| − 2(|A| − 1) = 2|A| + 2`.

*Case `L = ⟨w⟩`, `w ≠ 1`.* Left translation by `w` on `T` is a hyperbolic isometry: it has no fixed
vertex (`wx = x` forces `w = 1`) and does not invert an edge (that would force `w^2` to fix a
vertex, so `w^2 = 1`, impossible in a free group). So `w` has an axis `𝔸 ⊆ T`, a bi-infinite
geodesic on which `w` translates by `ℓ ≥ 1`, and `⟨w⟩` acts freely on `T` preserving `𝔸`.

Let `C ⊆ Sch = T/⟨w⟩` be the image of `𝔸`: it has exactly `ℓ` vertices and `ℓ` edges (a cycle,
a single loop when `ℓ = 1`). Let `Y` be the spanning subgraph of `Sch` obtained by deleting those
`ℓ` edges. Then `Y = (T ∖ 𝔸\text{-edges})/⟨w⟩`. The components of `T` minus the axis edges are
trees, each containing exactly one axis vertex, and `⟨w⟩` permutes them freely (`w^k` fixes the
component of an axis vertex `v` only if `w^k v = v`, i.e. `k = 0`). Hence `Y` is a disjoint union
of `ℓ` trees `Y_1, …, Y_ℓ`, one per vertex of `C`, and in `Y` every vertex has degree `4` except
the `ℓ` vertices of `C`, which have degree `2` and are the roots, one per component.

Let `A ⊆ V(Sch) = V(Y)` be finite and `A_i = A ∩ Y_i`. For nonempty `A_i`, the component `Y_i` is
a tree, so `|E_Y(A_i)| ≤ |A_i| − 1`, and `Σ_{v ∈ A_i} deg_Y(v) ≥ 4|A_i| − 2`, since at most one
vertex of `A_i` (the root of `Y_i`) has degree `2`. By (†),

  `|∂_Y A_i| ≥ 4|A_i| − 2 − 2(|A_i| − 1) = 2|A_i|`.

`Y` has no edges between distinct components, so `|∂_Y A| = Σ_i |∂_Y A_i| ≥ 2|A|`. Finally `Y` is
a subgraph of `Sch` on the same vertex set, so every edge of `∂_Y A` is an edge of `∂_{Sch} A`, and
`|∂_{Sch} A| ≥ |∂_Y A| ≥ 2|A|`. ∎

**Lemma 3.** If `H` has no non-abelian free subgroup and `Λ` is free of rank `2`, then every
`L ∈ 𝒮_H(Λ)` is trivial or infinite cyclic.

*Proof.* `L ≤ Λ` is free by Nielsen-Schreier. A free group of rank `≥ 2` contains a non-abelian
free subgroup, and `L` is isomorphic to a subgroup of `H`, which has none. So `L` has rank `≤ 1`. ∎

**Item 2.** If `G` contained a non-abelian free subgroup it would contain one of rank `2`, say `Λ`.
By Lemmas 2 and 3, `κ(Λ, S, 𝒮_H(Λ)) ≥ 2 > 0`, contradicting Step 2. ∎

---

## Step 4. Item 3, trivially cut subgroups

Suppose `L_g = 1` for all `g ∈ G`. Then every `Λ`-orbit of `X = G/H` is free, so choosing one base
point per orbit gives a `Λ`-equivariant bijection `X ≅ I × Λ`, with `Λ` acting by left translation
on the second coordinate. For `f ∈ ℓ^∞(Λ)` put `f̃(i, λ) = f(λ)`; then `s·f̃ = (s·f)~` for all
`s ∈ Λ`, so `m'(f) := m(f̃)` is a `Λ`-invariant mean on `ℓ^∞(Λ)`. Hence `Λ` is amenable.

If `H` is torsion-free and `Λ ≤ G` is a torsion group, then each `L_g` is a torsion subgroup of a
group isomorphic to a subgroup of `H`, hence trivial; so `Λ` is amenable. ∎

---

## Step 5. Item 4, Kazhdan subgroups

Let `Λ ≤ G` have property (T). By Step 0 and Lemma 1', `1_Λ ≺ ℓ^2(X)` with `X = G/H`. Property (T)
upgrades weak containment of the trivial representation to containment, so there is a nonzero
`Λ`-invariant `f ∈ ℓ^2(X)`. Pick `t > 0` with `{|f| > t} ≠ ∅`; this set is finite (as `f ∈ ℓ^2`) and
`Λ`-invariant, so it is a finite union of finite `Λ`-orbits. A finite orbit `Λ/L_g` means
`[Λ : L_g] < ∞`.

If in addition `Λ` is infinite, then `L_g` is infinite, has property (T) (finite index in a (T)
group), and is isomorphic to a subgroup of `H`. So if no infinite subgroup of `H` has property (T),
no infinite subgroup of `G` does either. For `H` with the Haagerup property this hypothesis holds,
because the Haagerup property passes to subgroups and a countable group with both (T) and the
Haagerup property is finite (Cherix, Cowling, Jolissaint, Julg and Valette, *Groups with the
Haagerup property*, Progress in Mathematics 197, Birkhauser 2001). ∎

---

## Step 6. Item 5, the dichotomy

Let `Λ ≤ G` be non-amenable. Suppose every `L_g` is amenable. If some `L_g` were co-amenable in
`Λ`, then `Λ` would be amenable (compose the `Λ`-invariant mean on `Λ/L_g` with an invariant mean
on `L_g`), a contradiction; so no `L_g` is co-amenable in `Λ`, i.e. `h(Sch(Λ, L_g, S)) > 0` for
every `g` by Lemma 1'' applied to the transitive `Λ`-set `Λ/L_g`. By Step 2 the infimum over `g` is
`0`, so there is a sequence `g_n` with `h(Sch(Λ, L_{g_n}, S)) → 0`. The other branch is that some
`L_g` is non-amenable; since `L_g` is isomorphic to a subgroup of `H`, that makes `H`
non-amenable. ∎

---

## Step 7. Item 6, quotients

Let `π : G ↠ Q`. The surjection `G/H ↠ Q/π(H)` is `G`-equivariant for the `G`-action on `Q/π(H)`
through `π`, so the push-forward `m_*(f) := m(f ∘ π)` is a mean on `ℓ^∞(Q/π(H))` invariant under
`π(G) = Q`. Hence `π(H)` is co-amenable in `Q`. ∎

---

## Where each hypothesis is used

- Countability of `G` is used only to make `G/H` countable in Lemma 1; the argument is otherwise
  insensitive to cardinality.
- Amenability of `H` is never used, and neither is normality; the only structure used is that the
  point stabilizers of `Λ` on `G/H` are subgroups of conjugates of `H`.
- The uniformity in item 1 is essential: Lemma 1'' only gives that the *infimum* of the Cheeger
  constants over the orbits vanishes, never that any single orbit is amenable. Item 5 is the exact
  statement of that gap.
