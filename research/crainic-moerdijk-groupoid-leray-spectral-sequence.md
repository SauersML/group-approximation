---
rg: 2
id: crainic-moerdijk-groupoid-leray-spectral-sequence
kind: claim
title: "Crainic–Moerdijk: a homomorphism of étale groupoids has a Leray spectral sequence whose coefficient stalks are the homology of comma groupoids"
---

**Import.** M. Crainic and I. Moerdijk, *A homology theory for étale groupoids*,
J. reine angew. Math. 521 (2000), 25–46, arXiv:math/9905011. The spaces involved
satisfy their standing assumptions (1.8): locally paracompact, Hausdorff, locally
compact, of bounded cohomological dimension. This holds for second countable, totally
disconnected, locally compact Hausdorff spaces, with dimension 0.

Let `φ : K → G` be a homomorphism of étale groupoids and `A` a `K`-sheaf.

1. **Bar complex (3.1).** If a `G`-sheaf `A` is c-soft, `H_n(G; A)` is the homology of
   the simplicial abelian group `Γ_c(G^(n); τ_n^*A)`. Its faces are summation along the
   fibres of the face maps.
2. **Discrete groupoids (3.5(2)).** If `G` is a discrete groupoid, `H_n(G; A)` is the
   simplicial homology of the nerve of `G` with twisted coefficients.
3. **Comma groupoid (4.1).** For `x ∈ G^(0)`, the comma groupoid `x/φ` is defined as
   follows, with the fibred product topology.
   - Its objects are pairs `(y, g : x → φ(y))`.
   - An arrow `(y, g) → (y', g')` is an arrow `k : y → y'` of `K` with
     `φ(k) ∘ g = g'`.
4. **`L_nφ_!` (4.2, 4.5(2)).** `L_nφ_!A` is the homology of the simplicial `G`-sheaf
   `B_n(φ; A) = (β_n)_! α_n^* A` on `G^(0)`, for c-soft `A` or for étale `φ`. Here
   `φ` is étale when each `φ_n` is a local homeomorphism, and the maps involved are
   defined as follows.
   - `α_n` and `β_n` are defined on the nerve spaces `K^(n) ×_{G^(0)} G^(1)`.
   - A string there has the shape
     `φ(y_0) ← φ(k_1) ← ... ← φ(k_n) ← φ(y_n) ← g ← x`.
   - `α_n` sends such a string to `t(k_1)`, and `β_n` sends it to `s(g) = x`.
   - `G` acts through the maps `g^* : x'/φ → x/φ`.
5. **Stalks (Proposition 4.3).** `(L_nφ_!A)_x ≅ H_n(x/φ; π_x^*A)` for all
   `x ∈ G^(0)`.
6. **Spectral sequence (Theorem 4.4).** There is a natural spectral sequence
   `E²_{p,q} = H_p(G; L_qφ_!A) ⇒ H_{p+q}(K; A)`.

With constant coefficients `Z` on totally disconnected spaces, item 1 is Matui's
homology (Matui 2012, Definition 3.1). Matui introduces that homology as the
constant-coefficient case of this theory, and proves his Theorem 3.8 as "a special
case of [CM, Theorem 4.4]".

Route: `crainic-moerdijk-leray-spectral-sequence-citation`.
