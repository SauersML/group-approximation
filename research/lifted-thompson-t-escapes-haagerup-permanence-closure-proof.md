---
rg: 2
id: lifted-thompson-t-escapes-haagerup-permanence-closure-proof
kind: route
title: "Simplicity of T makes every normal subgroup of T-bar central or everything; with perfectness, no finite quotients and a divisible central z, each permanence operation pulls T-bar back into an input, and each building block rejects it"
target: lifted-thompson-t-escapes-haagerup-permanence-closure
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - divisible-elements-act-elliptically-on-trees
  - finitely-generated-linear-groups-are-residually-finite
---

Notation is as in the target. Imports:
- **(I1)** `T` is simple and infinite (Cannon–Floyd–Parry, *Introductory notes on Richard
  Thompson's groups*). This is standard, and the theorem number was not re-checked. It is the
  same import (I1) as in `lifted-thompson-t-perfect-centre-cubically-elliptic-proof`.
- **(I2)** For dyadic rationals `a < b` and `c < d` there is a PL homeomorphism `[a,b] → [c,d]`
  with finitely many dyadic breakpoints and slopes in `2^Z`. This is also standard, and is
  import (I2) of the same route.
- **(I3)** Bass–Serre theory (Serre, *Trees*). The fundamental group of a graph of groups acts
  on its Bass–Serre tree without inversions. Vertex stabilizers are the conjugates of the vertex
  groups, and edge stabilizers are the conjugates of the edge groups. Standard.
- **(I4)** Amenability passes to subgroups and quotients. Standard.

Inputs from the graph:
- **(Q1)** From `lifted-thompson-t-perfect-centre-cubically-elliptic`:
  - item 1: `z` has an `n`-th root in `T̄` for every `n`;
  - item 2: `T̄ = [T̄, T̄]`;
  - item 3: `T̄` has no proper finite-index subgroup;
  - item 4: `z` has bounded wall count in every commensurating action of every `G ⊇ T̄`.
- **(Q2)** From `divisible-elements-act-elliptically-on-trees`, item 1: an element with roots of
  infinitely many orders fixes a vertex of the barycentric subdivision.
- **(Q3)** From `finitely-generated-linear-groups-are-residually-finite` (Malcev).

**(L0) Consequence of (Q1), item 3.** Every quotient of `T̄` has no proper finite-index subgroup,
since a finite-index subgroup of a quotient pulls back to one of `T̄`. So every homomorphism from
`T̄` to a residually finite group is trivial. Indeed, its image `H` is residually finite; if
`H ≠ 1`, some finite quotient of `H` is nontrivial, and its kernel is a proper finite-index
subgroup of `H`.

## Step 1. Item 1 (normal subgroups)

Let `N ⊴ T̄`, and let `p : T̄ → T` be the projection, with `ker p = ⟨z⟩`.
- `p(N)` is normal in `T`, so by (I1) it is `1` or `T`.
- If `p(N) = 1`, then `N ≤ ⟨z⟩ ≅ Z`, so `N = ⟨z^j⟩` for some `j ≥ 0`.
- If `p(N) = T`, then `N⟨z⟩ = T̄`. Since `z` is central, `[n z^a, n' z^b] = [n, n']`. So
  `T̄ = [T̄, T̄] = [N⟨z⟩, N⟨z⟩] = [N, N] ≤ N` by (Q1), item 2. Hence `N = T̄`.

**Corollary (C1).** If two normal subgroups `N_1, N_2` of `T̄` satisfy `N_1 ∩ N_2 = 1`, then one
of them is trivial. Otherwise either one equals `T̄`, forcing the other to be `1`, or
`N_1 = ⟨z^a⟩` and `N_2 = ⟨z^b⟩` with `a, b ≥ 1`, and then `z^{ab} ∈ N_1 ∩ N_2`. By induction the
same holds for any finite family of normal subgroups with trivial intersection.

## Step 2. Item 2 (nonamenability)

An *arc* is a half-open arc `[a, b)` of `S^1 = R/Z`, read counterclockwise from `a` to `b`, with
dyadic endpoints and length in `(0, 1)`.

**`T` is transitive on arcs.** Take arcs `[a, b)` and `[c, d)`, and lift them so that
`a < b < a + 1` and `c < d < c + 1`.
- By (I2) choose dyadic PL homeomorphisms `φ : [a, b] → [c, d]` and
  `ψ : [b, a + 1] → [d, c + 1]`.
- Their union is a homeomorphism `[a, a+1] → [c, c+1]` that sends `a ↦ c` and `a+1 ↦ c+1`.
  So it descends to an orientation-preserving PL homeomorphism `g` of `S^1`, with finitely many
  dyadic breakpoints and slopes in `2^Z`. So `g ∈ T`.
- `g` maps `[a, b)` onto `[c, d)`.

**No invariant measure.** Suppose `μ` is a `T`-invariant Borel probability measure on `S^1`.
- By transitivity every arc has the same measure `m`.
- `[0, 1/2)` is the disjoint union of `[0, 1/4)` and `[1/4, 1/2)`, so `m = 2m` and `m = 0`.
- `S^1 = [0, 1/2) ⊔ [1/2, 1)`, so `μ(S^1) = 0`. This is a contradiction.

An amenable group acting continuously on a compact space has an invariant probability measure.
So `T` is not amenable. `T` is a quotient of `T̄`, so by (I4) `T̄` is not amenable. By (I4) again,
no quotient `T̄/⟨z^j⟩` is amenable: each surjects onto `T` (for `j ≥ 1`) or equals `T̄`.

## Step 3. Item 3 (escape trichotomy)

Let `T̄ ≤ G` and `π : G → Q` be onto with kernel `N`. Then `T̄ ∩ N = ker(π|_T̄)` is normal in `T̄`.
By Step 1 it is `T̄`, or `1`, or `⟨z^m⟩` with `m ≥ 1`. These give the three cases:
- `T̄ ≤ N`;
- `π|_T̄` is injective, so `T̄ ↪ Q`;
- `π(T̄) ≅ T̄/⟨z^m⟩` embeds in `Q`.

The cases are mutually exclusive.

If `Q` is amenable, then `π(T̄)` is amenable by (I4). By Step 2 this is impossible in the second
and third cases. So `T̄ ≤ N`.

## Step 4. Finite products, finite index, unions

- **(P2) Finite direct products.** Let `T̄ ≤ A × B`. The kernels of the two projections restricted
  to `T̄` are `T̄ ∩ B` and `T̄ ∩ A`. They are normal in `T̄` and meet trivially. By (C1) one is
  trivial, so `T̄` embeds in `A` or in `B`. Induct for finitely many factors.
- **(P7) Finite-index overgroups.** Let `H ≤ G` have finite index and `T̄ ≤ G`. Then `T̄ ∩ H` has
  finite index in `T̄`. By (Q1), item 3, `T̄ ∩ H = T̄`, so `T̄ ≤ H`.
- **(P6) Directed unions.** If `T̄ ≤ ⋃_i G_i` for a directed family, the finitely many generators
  of `T̄` lie in a single `G_i`, so `T̄ ≤ G_i`.

## Step 5. Item 4 (wreath products)

Let `W = (⊕_X Γ) ⋊ G`, where `(h·f)(x) = f(h^{-1}x)`. Write elements as `(c, h)`, with
`(c, h)(c', h') = (c · (h·c'), hh')`. Let `π : W → G` be the projection, with kernel `⊕_X Γ`.
Suppose `T̄ ≤ W`. Apply Step 3 to `π`.

**Case `T̄ ≤ ⊕_X Γ`.**
- `T̄` is finitely generated, so it lies in `⊕_{x ∈ F} Γ = Γ^F` for a finite set `F ⊆ X`.
- By (P2), `T̄ ↪ Γ`.

**Case `T̄ ↪ G`.** Nothing to prove.

**Case `T̄ ∩ ⊕_X Γ = ⟨z^m⟩` with `m ≥ 1`.**
- Write each `g ∈ T̄` as `g = (c_g, π(g))`, and put `f = c_{z^m}`. So `z^m = (f, 1)` and `f ≠ 1`.
- **Support is invariant.** `z^m` is central in `T̄`. So for `g ∈ T̄`,
  `(f, 1) = g (f, 1) g^{-1} = (c_g · (π(g)·f) · c_g^{-1}, 1)`.
  Pointwise conjugation by `c_g` does not change supports, and `supp(π(g)·f) = π(g)·supp(f)`.
  So `π(g)` maps the finite nonempty set `S = supp(f)` to itself.
- **Every point of the support is fixed.** `H = π(T̄)` permutes `S`. Each point stabilizer in `H`
  has finite index. By (L0) the quotient `H ≅ T̄/⟨z^m⟩` has no proper finite-index subgroup. So
  `H` fixes `S` pointwise.
- **A coordinate homomorphism.** Fix `p ∈ S` and put `ρ_p(g) = c_g(p)`. For `g, g' ∈ T̄`,
  `c_{gg'} = c_g · (π(g)·c_{g'})`. Evaluating at `p` and using `π(g)^{-1} p = p`:
  `ρ_p(gg') = c_g(p) · c_{g'}(p) = ρ_p(g) ρ_p(g')`. So `ρ_p : T̄ → Γ` is a homomorphism, and
  `ρ_p(z^m) = f(p)`.
- **Choice of `p`.** `z^m` has infinite order, so `f` has infinite order in `⊕_X Γ`. If every
  `f(p)` with `p ∈ S` had finite order, then `f` would have finite order, since `S` is finite.
  So choose `p ∈ S` with `f(p)` of infinite order.
- **Injectivity.** `ker ρ_p` is normal in `T̄`, so by Step 1 it is `T̄` or `⟨z^j⟩`.
  - It is not `T̄`, since `ρ_p(z^m) ≠ 1`.
  - If `j ≥ 1`, then `z^{jm} ∈ ker ρ_p`, so `f(p)^j = ρ_p(z^{jm}) = 1`. This contradicts the
    choice of `p`.
  - So `j = 0` and `ρ_p` is injective: `T̄ ↪ Γ`.

**Abelian lamps.** If `Γ` is abelian, then `T̄ ↪ Γ` is impossible, because `T̄` is perfect and
nontrivial by (Q1), item 2. So `T̄ ↪ G`.

## Step 6. Item 5 (graphs of groups with finite edge groups)

Let `𝔾` have finite edge groups, and let `Y` be its Bass–Serre tree. Let `Y'` be the barycentric
subdivision, whose vertices are the vertices of `Y` together with one midpoint `e°` for each
geometric edge `e`. Suppose `T̄ ≤ π_1(𝔾)`.
- **`z` is elliptic.** By (Q1), item 1, `z` has roots of every order in `T̄`. So by (Q2), `z`
  fixes a vertex of `Y'`.
- **Midpoint stabilizers are finite.** The stabilizer of a midpoint `e°` is the setwise
  stabilizer of `e`. It contains the pointwise stabilizer of `e` with index at most 2, and by (I3)
  that is a conjugate of an edge group, hence finite. `z` has infinite order, so `z` fixes no
  midpoint.
- **`z` fixes exactly one vertex.** The fixed set `Fix_{Y'}(z)` is a nonempty subtree of `Y'`:
  the geodesic between two fixed vertices is fixed. Every edge of `Y'` has a midpoint as one
  endpoint. So a subtree with two or more vertices contains a midpoint, which `z` does not fix.
  Hence `Fix_{Y'}(z) = {v}` for a single vertex `v` of `Y`.
- **All of `T̄` fixes it.** `z` is central in `T̄`, so for `g ∈ T̄`,
  `g·Fix(z) = Fix(g z g^{-1}) = Fix(z)`, and `gv = v`.
- **Conclusion.** `T̄ ≤ Stab(v)`, which by (I3) is a conjugate of a vertex group.

## Step 7. The building blocks contain no T-bar

Suppose `T̄ ≤ G`.
- **(B1) Amenable `G`.** Then `T̄` would be amenable by (I4), contradicting Step 2.
- **(B2) `G` has a commensurating action with proper wall count `ℓ(g) = |gA Δ A|`.**
  - By (Q1), item 4, `sup_N ℓ(z^N) = C < ∞`.
  - The powers `z^N` are pairwise distinct, so infinitely many elements `g` have `ℓ(g) ≤ C`.
  - This contradicts properness.
- **(B3) `φ : G → R` with amenable kernel, where `R` is residually finite or linear.**
  - If `R` is residually finite, then so is `φ(T̄)`.
  - If `R ≤ GL_n(k)`, then `φ(T̄)` is a finitely generated linear group, hence residually finite
    by (Q3).
  - Either way `φ(T̄) = 1` by (L0). So `T̄ ≤ ker φ`, which is amenable. This contradicts (B1).

## Step 8. Item 6 (main theorem)

Let `𝒫` be the class of groups that contain no subgroup isomorphic to `T̄`.
- By Step 7, `𝒫` contains (B1), (B2) and (B3).
- `𝒫` is closed under the seven operations.
  - (P1) is clear.
  - (P2), (P6) and (P7) are Step 4.
  - (P3) is Step 5, applied with `Γ, G ∈ 𝒫`.
  - (P4) is Step 6, applied with all vertex groups in `𝒫`.
  - (P5) is Step 3: if `T̄ ≤ G` with `Q` amenable, then `T̄ ≤ N`, so `N ∉ 𝒫`.
- `𝒦` is the smallest class containing the blocks and closed under the operations, so `𝒦 ⊆ 𝒫`.
- By (P1), a group containing `T̄` is not in `𝒦` either. ∎

## Scope

The sharpness section of the target and the remark on `V` use
`lifted-thompson-t-quotients-are-rotation-centralizers` and
`hall-quotient-avoids-v-circle-groups-and-periodic-ends`, respectively. They are commentary, not
part of items 1–6, and this route does not require them.
