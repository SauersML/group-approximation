---
rg: 2
id: rank-one-cone-hosts-fw-local-map-proof
kind: route
title: Cone markings are commensurated because deep cones map to cones, and a transfixed copy gives finitely many marked pieces whose stabilizers are local maps
target: rank-one-cone-hosts-put-fw-groups-in-local-map-groups
requires: []
---

Notation is as in the target. The argument follows `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf-proof` step by step, with the self-similar group `H` replaced by the groupoid `Λ`. The only new input is (SS) where the original used `h(zX) = h(z)X`.

## 0. Deep cones go to cones

Let `λ : X_v -> X_w` be in `Λ`, and let `Z_λ` be the finite set of exceptional paths in (SS).

The cones `zX_{t(z)}` shrink to points as `|z| -> ∞`. `λ` is uniformly continuous, and `X_w` has a basis of cones. So for every `L` there is a depth `D(λ, L)` beyond which every path `z` has these properties:
- `z ∉ Z_λ`;
- `λ(zX) = z'X`;
- `|z'| >= L`.

## 1. The marking set and the action

Let `φ` be a Λ-piece map with code `{w_j}`, `φ(w_j ζ) = y_j λ_j(ζ)`, and let `f in F(Λ)` have code `{u_i}`, `f(u_i ζ) = y'_i μ_i(ζ)`.

Let `B` bound the lengths of the paths in the finite sets `Z_{μ_i}`. Put `L = max_i |u_i| + B + 1`, and choose `D >= D(λ_j, L)` for every `j`.

Refine each `w_j` to the finite family `w_j z` with `|z| = D`. For every such `z`:
- **Step one.** `φ(w_j z ζ) = y_j z' λ_j|_z(ζ)` with `|y_j z'| >= |z'| >= L`, so `y_j z' = u_i t` for some `i`.
- **Step two.** Then `|t| >= L - |u_i| > B`, so `t ∉ Z_{μ_i}` and `μ_i(tζ) = t' μ_i|_t(ζ)`.
- **Composite.** Therefore `f∘φ(w_j z ζ) = y'_i t' (μ_i|_t ∘ λ_j|_z)(ζ)`, and `μ_i|_t ∘ λ_j|_z` lies in `Λ`.

So `f∘φ` is a Λ-piece map. It is injective as a composite of injective maps. The class `[f∘φ]` depends only on `[φ]`, since `f∘(φ∘λ) = (f∘φ)∘λ`. This is an action of `F(Λ)` on `S`, with `im(f·[φ]) = f(im[φ])`.

## 2. M is commensurated

Distinct paths give distinct classes `[β_u]`, since their images `uX` differ.

Fix `f` with code `{u_i}`. For a path `u`:
- **Long paths stay in `M`.** If `u = u_i w` with `w ∉ Z_{μ_i}`, then `f∘β_u = β_{y'_i w'} ∘ μ_i|_w`, so `f·[β_u] = [β_{y'_i w'}]` lies in `M`.
- **Only finitely many exceptions.** The remaining paths are the proper prefixes of code words, together with the paths `u_i w` with `w in Z_{μ_i}`. There are finitely many of each.

So `fM \ M` is finite. Applying this to `f^{-1}` shows that `M \ fM = f(f^{-1}M \ M)` is finite as well. Hence `M` is commensurated by `F(Λ)`, and so by every subgroup.

## 3. FW transfixes M

For the definition, see `almost-v-fw-subgroups-act-through-finitely-many-germs`. Property FW says every commensurated subset of a `G`-set is transfixed. So there is a `G`-invariant `M' ⊆ S` with `M Δ M'` finite. For groups with property (T), the Delorme–Guichardet step of the cited Röver–Nekrashevych proof produces `M'` explicitly.

## 4. A finite invariant cover

- **Choice of `N`.** Since `M \ M'` is finite, some `N` has `[β_u] in M'` for every `|u| >= N`.
- **The set `P`.** Let `I` be the set of images of classes in `M'`, and let `P` be the set of classes in `M'` whose image is maximal in `I` under inclusion.
- **`G` permutes `P`.** `G` preserves `M'` and carries images to images, preserving inclusion.
- **`P` is finite.**
  - A cone `uX` with `|u| > N` lies strictly inside the cone of its length-`N` prefix, which is in `I`.
  - So every class in `P` is either `[β_u]` with `|u| <= N` or a class of the finite set `M' \ M`.
  - Several classes may share one image; that does not matter.
- **The images of `P` cover `X`.**
  - Every point lies in a cone `uX` with `|u| = N`, which is in `I`.
  - Only finitely many members of `I` contain that cone: its prefix cones, and images of classes of `M' \ M`.
  - A maximal one among them is maximal in `I`.

## 5. The embedding

Let `G_0` be the kernel of the action of `G` on the finite set `P`; it has finite index in `G`. Fix a representative `φ : X_{v(φ)} -> X` of each class in `P`.

- **The coordinate maps.** For `g in G_0`, `g·[φ] = [φ]` means `g∘φ = φ∘ρ_φ(g)` for some `ρ_φ(g) in Λ(v(φ))`. It is unique because `φ` is injective.
- **Each coordinate is a homomorphism.** `(gg')∘φ = g∘φ∘ρ_φ(g') = φ∘ρ_φ(g)ρ_φ(g')`.
- **The product map is injective.** If every coordinate of `g` is trivial, then `g` is the identity on every `im φ`. These images cover `X`, so `g = 1`.

So `g -> (ρ_φ(g))_{[φ] in P}` embeds `G_0` in `∏_{[φ] in P} Λ(v(φ))`. This is item 2.

## 6. Simple inputs

Let `G` be infinite and simple.
- **`G_0 = G`.** The normal core of `G_0` has finite index and is normal, so it is `G` or `1`. It cannot be `1`, because `G` is infinite.
- **One coordinate suffices.** The kernels of the coordinate projections are normal in `G`, so each is `1` or `G`. Their intersection is trivial and `G ≠ 1`, so some coordinate is injective.

This is item 3.

## 7. The consequences

- **Identities.** If `Λ` consists of identities, every `Λ(v)` is trivial, so `G_0 = 1` and `G` is finite.
- **Synchronous `Λ`.** If `Λ` consists of tree automorphisms, then every `Λ(v)` is a subgroup of `Aut` of a locally finite rooted tree, hence residually finite. So `G_0` and `G` are residually finite, by step 6 of the cited proof.
- **Katsura odometers.** For Katsura's one-vertex odometer groupoids, `Λ(v)` is `Z` acting by the odometer. An FW group that is virtually a subgroup of `Z^m` is finite, since `Z` does not have FW.

**Where the argument stops.** Only step 2 uses that the cones form a tree: every cone either lies inside a code piece or is one of finitely many proper prefixes of code words. With product or building cone structures, a cone can straddle two pieces without lying in either, and infinitely many cones do. There `M` is not commensurated, and nothing is claimed.
