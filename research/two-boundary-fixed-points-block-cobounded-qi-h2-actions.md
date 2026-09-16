---
rg: 2
id: two-boundary-fixed-points-block-cobounded-qi-h2-actions
kind: claim
title: A group of isometries of a space quasi-isometric to H^2 that fixes two boundary points has no coarsely dense orbit
---

Let `X` be a geodesic metric space quasi-isometric to `H^2`, satisfying the four-point inequality
`(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ`. Let `∂X` be its sequential boundary, as in
`busemann-null-isometries-have-no-boundary-contraction`. Suppose a group `G` acts on `X` by isometries,
and the induced action on `∂X` fixes two distinct points `ξ ≠ η`. Then no `G`-orbit in `X` is
coarsely dense.

For isometries of `H^2` itself, this is contained in the classification used in
`abelian-isometry-groups-of-h2-are-not-cobounded-proof`. It is the last step of
`thompson-f-no-cobounded-qi-h2-action-via-busemann`.

## Attempts

- **Sketch (2026-09-16, swarm lane zaremsky-2-18).** Ingredients are classical but were not re-read.
  - Let `φ: X → H^2` be a quasi-isometry with quasi-inverse `ψ`.
  - `φ` induces a bijection `∂φ: ∂X → ∂H^2`. This is a boundary-extension theorem for possibly
    non-proper geodesic hyperbolic spaces (Väisälä, Expo. Math. 23 (2005), Section 6; unverified).
  - Let `γ` be the geodesic of `H^2` from `∂φ(η)` to `∂φ(ξ)`, and put `ℓ := ψ∘γ`, a quasi-geodesic in
    `X` with ends at `η` and `ξ`.
  - For `h ∈ G`, `φ∘h∘ℓ` is a quasi-geodesic of `H^2` with constants independent of `h`, and with the
    same ends as `γ`.
  - By the Morse lemma for bi-infinite quasi-geodesics with common endpoints (Bridson–Haefliger
    III.H.1.7 plus a limiting argument; unverified), it lies within some `M` of `γ`, with `M`
    independent of `h`.
  - So `φ(G·ℓ(0)) ⊆ N_M(γ)`. If `G·ℓ(0)` were `r`-dense, then `H^2` would lie in a bounded
    neighbourhood of `γ`, which is false.
- **An elementary replacement for the last step, useful for an intrinsic proof.** Suppose `X` lies
  within bounded distance of a quasi-line. Then `X`, and hence `H^2`, is quasi-isometric to `R`.
  - A `(K,C)`-quasi-isometry `f: H^2 → R` fails on equilateral triangles `p_1p_2p_3` with large
    side `L`.
  - One image, say `f(p_2)`, lies between the other two. The image of the geodesic `[p_1,p_3]` is a
    `(K + C)`-chain from `f(p_1)` to `f(p_3)`, so some `q ∈ [p_1,p_3]` has `d(f(q), f(p_2)) ≤ K + C`.
    Hence `d(q, p_2) ≤ K(2C + K)`.
  - But for `q ∈ [p_1,p_3]`, `2d(p_2,q) ≥ 2L − d(p_1,q) − d(q,p_3) = L`.
- **Intrinsic attempt (first pass unfinished; completed the same day).**
  - Put `f := b_ξ + b_η`, the sum of the Busemann functions of `busemann-null-isometries-have-no-boundary-contraction-proof`,
    Step 3. It is quasi-equivariant: `f(hy) = f(y) + c_ξ(h) + c_η(h) + O(8δ)`.
  - A coarsely dense orbit would make `f` bounded on `X` if `c_ξ + c_η` were bounded on `G`.
  - The first pass was missing two things:
    - boundedness of `c_ξ + c_η`, which would follow from Manning's theorem, arXiv:2406.12982
      Citation 1.12 (unread);
    - the coarse statement that `f ≤ B` forces `X` into a neighbourhood of a quasi-line.
  - Both were supplied in the direct route `two-boundary-fixed-points-block-via-busemann-projection`.
    - `f ≥ −2Q` by the triangle inequality, and `f(ho) + f(h^{-1}o) ≤ 4δ`, so `f` is bounded above on
      the orbit.
    - The four-point inequality at base points `z'_j → η` gives
      `d(u,v) ≤ (f(u) + f(v))/2 + |π(u) − π(v)| + 2Q + 2δ`, where `π := (b_ξ − b_η)/2`. So `π` is a
      quasi-isometric embedding `X → R`, and the equilateral-triangle argument above finishes.
    - Neither the Morse lemma nor Manning's theorem is used.
