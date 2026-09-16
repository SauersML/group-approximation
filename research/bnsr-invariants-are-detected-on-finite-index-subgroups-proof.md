---
rg: 2
id: bnsr-invariants-are-detected-on-finite-index-subgroups-proof
kind: route
title: "A classifying space of G covers one of H with the same universal cover, and a G-height function is an H-height function"
target: bnsr-invariants-are-detected-on-finite-index-subgroups
requires: []
---

**Sources**, read on 2026-09-16 from the arXiv LaTeX sources.

- M. Ershov and M. C. B. Zaremsky, "Dense and empty BNSR-invariants of the
  McCool groups", arXiv:2505.18826v2, §2.1.
  - Setup: "Let G be a group of type F_n, so by definition it has a
    classifying space with finite n-skeleton. Choose any such classifying
    space K, let K̃ be the universal cover of K, and let X be the n-skeleton
    of K̃, with the canonical G-action. It is not hard to show that for any
    non-trivial character χ of G there exists a map h_χ: X → R (called a
    height function) such that h_χ(g.x) = χ(g) + h_χ(x) for all g ∈ G and
    x ∈ X. For t ∈ R, define X^{h_χ≥t} to be the subcomplex of X consisting
    of all cells whose vertices lie in h_χ^{-1}([t,∞))."
  - Definition (BNSR-invariants): "For any 0 ≤ m ≤ n, the mth
    Bieri–Neumann–Strebel–Renz (BNSR) invariant Σ^m(G) is the subset of S(G)
    consisting of all [χ] for which the filtration X^{h_χ≥t} of X is
    essentially (m−1)-connected, meaning that for every t there exists u ≤ t
    such that the inclusion X^{h_χ≥t} → X^{h_χ≥u} induces the trivial map in
    all homotopy groups up to dimension m−1."
  - Independence: "This definition is independent of the choices of X and
    h_χ; see for example [bieri03, Theorem 12.1]." The cited theorem of
    Bieri–Geoghegan was not re-read.
  - Remark (a): "one can take X to be any (n−1)-connected CW-complex on which
    G acts properly, cocompactly, and cellularly (see, e.g. [zaremsky18,
    Definition 1.1])".
- M. C. B. Zaremsky, "Separation in the BNSR-invariants of the pure braid
  groups", arXiv:1507.08597v1.
  - Definition 1.1 is the same definition with a proper cocompact action on
    an `(n−1)`-connected complex `Y` and the full subcomplexes `Y_{χ≥t}`.
    Its well-definedness is stated as: "Σ^m(G) is well defined up to the
    various non-canonical aspects, e.g., the space Y and the height function
    h_χ".
  - §3 uses this very argument: "Since P_n has finite index in B_n, its action
    on X is cocompact, and hence can be used to “reveal” the BNSR-invariants
    of P_n."

**Proof.** For `n = ∞`, apply the finite case to every `n`. So let `n` be
finite and `k = [G:H]`.

*Step 1: `H` is of type `F_n`, and the complex `X` of `G` also serves `H`.*

1. Choose a `K(G,1)` complex `K` with finite `n`-skeleton. Let `K̃` be its
   universal cover, with `G` acting by deck transformations. This action is
   free and permutes cells, `K = K̃/G`, and `X = K̃^{(n)}`.
2. Put `K_H = K̃/H`. Since `H` acts freely and properly discontinuously,
   `K̃ → K_H` is a covering map. `K̃` is simply connected, so this is a
   universal covering with deck group `H`. `K̃` is contractible, so `K_H` is
   a `K(H,1)`.
3. `K_H` inherits a CW structure whose cells are the images of the cells of
   `K̃`.
   - The cells of `K̃` over a fixed cell of `K` form a single `G`-orbit, and
     `G` acts on it freely.
   - That orbit splits into exactly `k` `H`-orbits.
   - So `K_H` has `k` times as many cells as `K` in each dimension, and its
     `n`-skeleton is finite.
4. Hence `H` is of type `F_n`, which is item 1. With the restricted action,
   `X` is the `n`-skeleton of the universal cover of the `K(H,1)` complex
   `K_H`, with the canonical `H`-action. So `X` is an admissible choice in the
   definition of `Σ^m(H)`.
5. Remark (a) gives the same admissibility directly. `X` is `(n−1)`-connected,
   and `H` acts on it freely and cellularly with finitely many orbits of cells,
   at most `k` per `G`-orbit.

*Step 2: restriction (item 2).*

1. Let `g ∈ G`. The `k + 1` cosets `H, Hg, …, Hg^k` cannot all be distinct.
   So `Hg^i = Hg^j` for some `0 ≤ i < j ≤ k`, and then `g^{j−i} ∈ H` with
   `1 ≤ j − i ≤ k`.
2. **Non-trivial.** Let `χ ≠ 0` and choose `g` with `χ(g) ≠ 0`. Take
   `r = j − i` as in (1). Then `g^r ∈ H` and `χ(g^r) = rχ(g) ≠ 0`. So
   `χ|_H ≠ 0`.
3. **Well defined.** Restriction commutes with multiplication by positive
   scalars, so `res` is well defined on classes.
4. **Injective.** Suppose `χ|_H = c·ψ|_H` with `c > 0`. For `g ∈ G` choose
   `r ≥ 1` with `g^r ∈ H`. Then `rχ(g) = χ(g^r) = cψ(g^r) = crψ(g)`, so
   `χ(g) = cψ(g)`. Hence `χ = cψ` and `[χ] = [ψ]`.

*Step 3: the invariants agree (item 3).*

1. Fix `1 ≤ m ≤ n` and `χ ≠ 0`. Choose a height function `h: X → R` for `χ`,
   so `h(g.x) = χ(g) + h(x)` for all `g ∈ G` and `x ∈ X`.
2. For `h' ∈ H` this says `h(h'.x) = χ|_H(h') + h(x)`. So `h` is a height
   function for the non-trivial character `χ|_H` of `H` acting on `X`.
3. The subcomplexes `X^{h≥t}` and the inclusions between them are determined
   by `X` and `h` alone; no group enters. Let `P` be the statement "the
   filtration `(X^{h≥t})_{t∈R}` is essentially `(m−1)`-connected".
4. The definition with the choices `(K, X, h)` for `G` gives
   `[χ] ∈ Σ^m(G) ⇔ P`.
5. The definition with the choices `(K_H, X, h)` for `H` gives
   `[χ|_H] ∈ Σ^m(H) ⇔ P`.
6. By independence of the choices, both are the invariants themselves. So
   `[χ] ∈ Σ^m(G) ⇔ [χ|_H] ∈ Σ^m(H)`. ∎

Step 3 uses only that `Σ^m(H)` is well defined: the admissible choice
`(K_H, X, h)` computes it. Independence of `h` for a fixed `X` is also
elementary. Two height functions for the same character differ on vertices by
an `H`-invariant function. `X` has finitely many `H`-orbits of vertices, so
that difference is bounded. Shifting `t` by the bound compares the two
filtrations.

**The consequences stated in the claim.**

- **Nesting.** `Σ^m ⊆ Σ^k` for `m ≥ k`, since an inclusion that is trivial on
  `π_i` for `i ≤ m−1` is trivial for `i ≤ k−1`, with the same `u`.
- **A proper drop passes down.** Let `[χ] ∈ Σ^m(G) \ Σ^{m+1}(G)`. By item 3,
  `[χ|_H] ∈ Σ^m(H) \ Σ^{m+1}(H)`.
- **Stabilization passes up.** Suppose `Σ^m(H) = Σ^k(H)` for all `m ≥ k`, and
  let `m ≥ k`. If `[χ] ∈ Σ^k(G)`, then `[χ|_H] ∈ Σ^k(H) = Σ^m(H)`, so
  `[χ] ∈ Σ^m(G)`. With nesting, `Σ^m(G) = Σ^k(G)`.

**Consistency check.** `P_n ≤ B_n` has index `n!`.

- Zaremsky (arXiv:1507.08597v1) proves "Σ^∞(B_n)=S(B_n)" (the corollary
  labelled `cor:braid_sig` in the source), via the crossing character `cross`.
- The class `[cross|_{P_n}]` must then lie in `Σ^∞(P_n)`. It does, by his
  Corollary 1.6 ("Center survives"): "if χ(Z(G)) ≠ 0 then [χ] ∈ Σ^m(G)" for
  `G` of type `F_m`. The source notes that `Δ^2` generates the center of
  `P_n`, and `cross(Δ^2) ≠ 0`.
