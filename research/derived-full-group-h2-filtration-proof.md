---
rg: 2
id: derived-full-group-h2-filtration-proof
kind: route
title: Hurewicz on the universal cover plus the Atiyah-Hirzebruch spectral sequence in total degree two
target: derived-full-group-h2-filtered-by-mod-two-groupoid-homology
requires:
  - li-derived-full-group-homology-is-k-theory-cover
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

Notation and hypotheses are those of the target. The item numbers cite
`li-derived-full-group-homology-is-k-theory-cover`. The artifact, Sections 1–3, gives the same
argument with source lines.

**Universal coefficients.**
- The groupoid homology complex `C_c(G^(n), Z)` consists of free abelian groups. Each is a union,
  along split injections, of the free groups `Z^P` for clopen partitions `P`.
- So `H_n(G; A) ≅ H_n(G) ⊗ A ⊕ Tor(H_{n-1}(G), A)`.

**Theorem 1.**
1. **Homology equals homotopy.** By item 2 with `C = Z`, `H_2(D(G)) ≅ H_2(Y)`, where `Y` is the
   universal cover of `Ω^∞_0 K`.
   - `Y` is simply connected, so Hurewicz gives `H_2(Y) ≅ π_2(Y)`.
   - Covering maps are isomorphisms on `π_k` for `k >= 2`, and `π_k(Ω^∞_0 K) = π_k(K)` for
     `k >= 1`.
   - Hence `H_2(D(G)) ≅ π_2(K)`.
2. **The `E^2` page.** Items 1 and 3 give a first-quadrant spectral sequence with
   `E^2_{p,q} ≅ H_p(G; π_q(S))` converging to `π_*(K)`. Here `π_0(S) = Z` and
   `π_1(S) = π_2(S) = Z/2`.
3. **Differentials.** They are `d^r : E^r_{p,q} -> E^r_{p-r, q+r-1}`.
   - Into `(0,2)`: `d^2` from `(2,1) = H_2(G; Z/2)`, and `d^3` from `(3,0) ⊆ H_3(G)`. Longer
     differentials start at `q < 0`, and outgoing ones land at `p < 0`.
   - Into `(1,1)`: only `d^2` from `(3,0)`. Out of `(1,1)`: nothing.
   - Out of `(2,0)`: `d^2` to `(0,1) = H_0(G; Z/2)`. Into `(2,0)`: nothing.
4. **Convergence.** `F_p/F_{p-1} = E^∞_{p,2-p}` gives the three pieces. ∎

**Corollary 2.**
- **(a)** A finitely presented group has a `K(π,1)` with finite 2-skeleton, hence finitely
  generated `H_2`.
  - `F_0` is the `F_2`-vector space `H_0(G; Z/2)` modulo the images of the finite
    `H_2(G; Z/2)` and of a finitely generated subgroup. It is infinite when `H_0(G; Z/2)` is.
  - Likewise `F_1/F_0` is infinite when `H_1(G; Z/2)` is.
  - An infinite subquotient forbids finite generation of `π_2(K) ≅ H_2(D(G))`.
- **(b)** Every graded piece is a subquotient of a finitely generated group.
- **(c)** By universal coefficients, each `H_p(G; π_q(S))` with `p <= k` is finitely generated.
  - So `π_j(Y) = π_j(K)` is finitely generated for `2 <= j <= k`, and `π_1(Y) = 0`.
  - Serre's mod-`C` Hurewicz theorem, for the Serre class of finitely generated abelian groups
    and simply connected `Y`, gives `H_j(Y)` finitely generated for `j <= k`.
  - Item 2 transfers this to `D(G)`. ∎

**Model tests.**
- **`G_2`.** All groupoid homology vanishes, so all pieces vanish, and `H_2(V) = 0`, as known.
- **`Z ⋉ X`.**
  - `H_0 = K^0(X)` is torsion-free, `H_1 = Z`, and `H_k = 0` for `k >= 2`.
  - So `F_2/F_1 = 0`, `F_1/F_0 = H_1(G; Z/2) = Z/2`, and `F_0 = K^0 ⊗ Z/2`.
