---
rg: 2
id: ordered-matching-complex-kn-simply-connected-n-ge-8-proof
kind: route
title: "Diameter two for connectivity, and Quillen's fiber theorem over the unordered matching complex for simple connectivity"
target: ordered-matching-complex-kn-simply-connected-n-ge-8
requires: []
artifacts:
  - research/artifacts/zp-loop-braid-descending-links-simply-connected-2026-09-16.md
---

Complete proof, artifact §4, Proposition 4.1. Refereed 2026-09-16; see the referee section of
`notes/zaremsky-2-12-loop-braided-v-type-f-infi-swarm-2026-09-16.md`.

1. **Connected, `n ≥ 5`.**
   - Disjoint pairs are adjacent.
   - Two pairs that meet use at most 3 elements, so there is a pair `(e, f)` disjoint from both.
   - So the diameter is at most 2.
2. **Simply connected, `n ≥ 8`.** Forget the order: `f: OM(K_n) → M(K_n)`, `(a, b) ↦ {a, b}`. Apply
   Quillen's Theorem 9.1 with `d = 1`, in the form used by Bux–Fluch–Marschler–Witzel–Zaremsky
   (arXiv:1210.2931, TeX l. 3654) and Witzel–Zaremsky (arXiv:1405.5491v3, TeX l. 2375). It needs:
   - **Base.** `M(K_n)` is 1-connected. This follows from BFMWZ `prop:matching_cpx_conn`: `M(K_n)`
     is `(ν(n) − 1)`-connected with `ν(n) = ⌊(n+1)/3⌋ − 1`, and `ν(n) ≥ 2` for `n ≥ 8`.
   - **Links.** The link of a k-simplex is `M(K_{n−2k−2})`, which must be `(−k)`-connected:
     - `k = 0`: `M(K_{n−2})` is connected, since `ν(n−2) ≥ 1` for `n ≥ 7`;
     - `k = 1`: `M(K_{n−4})` is non-empty.
   - **Fibers.** The fiber over a closed k-simplex is the join of `k+1` copies of `S^0` (the two
     orientations of each edge, never adjacent to each other). That is `S^k`, which is
     `(k−1)`-connected.
   - **Same step from a verified source (referee, 2026-09-16).** Quillen's original was not fetched,
     so the step is also derived from Hatcher–Wahl (arXiv:0709.2173v4; TeX source checked
     2026-09-16).
     - `f` is a *complete join complex* over `M(K_n)` (HW Definition 3.2, TeX label `joincpx`):
       - f is surjective;
       - f is injective on each simplex;
       - over a p-simplex σ, every choice of one orientation per edge spans a simplex. So `Y(σ)` is
         the join of the full fibers `f^{-1}(x)`.
     - HW Proposition 3.5, verbatim: "If Y is a complete join complex over a CM (resp. wCM) complex
       X of dimension n, then Y is also CM (resp. wCM) of dimension n."
     - HW define wCM of dimension n, verbatim: "X is (n−1)-connected and the link of each p-simplex
       of X is (n−p−2)-connected".
     - The **Base** and **Links** items above say exactly that `M(K_n)` is wCM of dimension 2 for
       `n ≥ 8`: it is 1-connected, and the link of a p-simplex is `(−p)`-connected (vacuous for
       `p ≥ 2`).
     - Hence `OM(K_n)` is wCM of dimension 2, and in particular 1-connected, using only (B) and HW.
3. **Machine check.** `experiments/zaremsky-2-12-loop-braided-v-type-f-infi-2026-09-16/matching_pi1.py`
   certifies `π_1(OM(K_n)) = 1` for `n = 8, 9` directly, without the two citations.
   - It also finds `H_1(OM(K_n); F_2) ≠ 0` for `n = 5, 6`.
