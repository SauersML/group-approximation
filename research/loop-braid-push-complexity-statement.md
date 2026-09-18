---
rg: 2
id: loop-braid-push-complexity-statement
kind: claim
title: "Push complexity statement CX(N): for free count N ≥ 11, X_n(F∪{v,w}) carries a complexity lowered by pair-twist pushes whose mutual links contain the K-neighbours, with zero set in lk([(v,w)])"
distinct_from:
  loop-braid-forbidden-ring-coning-statement: that asks for connectivity of the coned-off subcomplex Y and reduces via a nerve to multiple intersections of links; this is a combinatorial statement about one base vertex and pairwise pair-twist pushes, with no connectivity content, and implies the target directly without passing through Y
  loop-braid-descending-links-are-increasingly-connected: that is the target (connectivity of X_n); this is a purely combinatorial complexity statement that implies it via BFMWZ Lemma 3.9 and the pair-twist mutual link
artifacts:
  - research/artifacts/zp-loop-braid-bfmwz-push-decomposition-2026-09-17.md
---

Notation is from the artifact §§1–2, 4.
- `X_n(F)` is the forbidden-ring family, with free count `N = n − |F|`.
- For distinct free rings v, w: `X^0 := X_n(F ∪ {v, w})` and `b_0 := [(v, w)]`.
- For a vertex `u = p[(a,b)]` of `X^0`, a ring `r ∉ {a, b}` and an order `e ∈ {(f, r), (r, f)}`:
  `g_e ∈ {τ_br, τ_ra}` is the pair twist and `L_e = T · Q_abr` is the mutual link of
  `loop-braid-pair-twist-push-mutual-link`. The **push** of u is `p g_e p^{-1} u`.

**Claim CX(N).** For every `N ≥ 11`, and all n, F, v, w with free count N, there is
`c : V(X^0) → Z_{≥0}` such that:
- **(CX0)** the full subcomplex of `X^0` on `c^{-1}(0)` lies in `lk_{X_n(F)}(b_0)`;
- **(CX1)** every finite subcomplex `K ⊆ X^0` with a vertex of positive complexity has a vertex
  `u = p[(a,b)]` with `c(u) > 0`, and r, e, such that `c(p g_e p^{-1} u) < c(u)` and
  `K ∩ lk(u) ⊆ p L_e`.

Only spheres of dimension `η(N) = ⌊(N−5)/3⌋` with `N ≡ 0, 2 (mod 3)` matter for the route
`loop-braid-desc-links-connected-via-bfmwz-push` (artifact §4.2, Remark 1). The first instances
are `N = 11, 12` with 2-spheres.

(CX1) is equivalent to: all K-neighbours of u lie in the link of one vertex of type `(f, r)` or
`(r, f)` in `lk(u) ≅ X_{n−1}(F' ∪ {f})`, and the push through that vertex lowers c.

## Attempts

- 2026-09-17 (swarm-0917-w9-w9-z-last1): stated; the reduction is route
  `loop-braid-desc-links-connected-via-bfmwz-push`. Artifact §5:
  - **Clasp proxy.** `c = |χ_{(a,b),(v,w)}|` is well defined on vertices. It vanishes on
    `lk(b_0)`, and a push with `r ∈ {v, w}` changes it by ±1, so the lowering half of (CX1) holds
    for it. It fails (CX0): commutators and the Whitehead-type clasp of the model artifact §3 have
    χ = 0 but are not adjacent to `b_0`. It also says nothing about the K-condition.
  - **Geometric heuristic.** Take the intersection arc of a K-band with the band of `b_0` that is
    closest to w, as in BFMWZ Thm 3.10. This needs two unproved facts:
    - (G1) disjoint bands with unlinked fusion form a simplex;
    - (G2) a band disjoint from the region around the triple lies in the triple-cable picture
      `pT P_σ`.
  - **Also open.** Whether `lk(b_0)` is a full subcomplex of `X_n(F)`, which a complexity with zero
    set exactly `V(lk b_0) ∩ V(X^0)` would need.
