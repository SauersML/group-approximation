---
rg: 2
id: cantor-wreath-distortion-descends-to-fibre-or-base
kind: claim
title: Distortion in a continuous wreath C(X,Γ) ⋊ W over a compact space descends to the base W or to a finitely generated subgroup of the fibre Γ, so distortion-free groups are closed under continuous wreaths
distinct_from:
  u3-q-not-in-q-free-cantor-wreaths: that excludes the divisible group U_3(Q) from continuous wreaths through unbounded denominators; this is a metric transfer for single elements of finitely generated subgroups, and it excludes finitely generated groups such as H_3(Z) and BS(1,k).
  thompson-v-has-no-heisenberg-subgroup: that uses undistortion of V itself; this carries undistortion from Γ and W up to C(X,Γ) ⋊ W, for any compact W-space X.
  heisenberg-in-nv-forces-drift-free-central-element: that is a drift (measure) constraint on distorted elements of nV; this is a word-length constraint on elements of continuous wreaths, with no measure.
  full-group-label-length-bounds-distortion: that asks for undistortion inside full groups via label length; this concerns continuous wreaths, which are not full groups.
---

**ESTABLISHED** by `cantor-wreath-distortion-descends-proof`. The proof is an elementary lane proof,
not independently reviewed (2026-09-19, swarm-0917-w17-w17-z-break). No priority is claimed.

**Setting.**
- `Γ` is a discrete group.
- `W` acts on a compact space `X` by homeomorphisms.
- `C(X,Γ)` is the group of continuous, so locally constant, maps `X → Γ` under pointwise product.
- `G = C(X,Γ) ⋊ W`, with `(f,w)(f',w') = (f·(w·f'), ww')` and `(w·f')(x) = f'(w^{-1}x)`.
- `π : G → W` is the projection.

**Definition.** A group is *distortion-free* if, for every finitely generated subgroup `Λ = ⟨S⟩`
and every `g ∈ Λ` of infinite order, there are `κ > 0` and `C` with `|g^N|_S ≥ κN − C` for all
`N ≥ 1`. For a finitely generated group it is enough to check `Λ` equal to the whole group,
because `|·|_Γ ≤ const·|·|_Λ`.

**Theorem.** Let `H = ⟨S⟩ ≤ G` with `S = S^{-1}` finite, and write `s = (f_s, w_s)`. Put
`F = ⋃_{s∈S} f_s(X)`. It is a finite symmetric subset of `Γ`. Let `g ∈ H` have infinite order,
and write `D(N) = |g^N|_S`. Then one of the following holds.
- **(i) Base.** `π(g)` has infinite order and `|π(g)^N|_{π(S)} ≤ D(N)` for all `N`.
- **(ii) Fibre.** `π(g)` has finite order `p`, and there is `γ ∈ ⟨F⟩` of infinite order with
  `|γ^N|_F ≤ D(pN)` for all `N`.

**Corollaries.**
1. **Closure.** If `Γ` and `W` are distortion-free, so is `C(X,Γ) ⋊ W`. This holds for every
   compact `W`-space `X`. With `X` a point, it gives closure under direct products `Γ × W`.
2. **Heisenberg transfer.** Suppose `H_3(Z) ≤ C(X,Γ) ⋊ W`. Then `W` or `Γ` has a finitely
   generated subgroup `⟨T⟩` containing an infinite-order `δ` with `|δ^{N^2}|_T ≤ K N` for all
   `N`, for some constant `K`.
3. **Baumslag–Solitar transfer.** Suppose `BS(1,k) ≤ C(X,Γ) ⋊ W` with `|k| ≥ 2`. Then `W` or `Γ`
   has a finitely generated subgroup containing an infinite-order `δ` with
   `|δ^{k^n}| ≤ 2n + K` for all `n`.

The invariant is the linear growth of powers. It dies at a single step. A power of `g` whose base
image is torsion is a pure fibre element `(h,1)`. Evaluating it at one point `x_0`, where `h(x_0)`
has infinite order, is a word of the same length in the finitely many fibre values `F`.
