---
rg: 2
id: ghb7-flexibly-hs-stable
kind: claim
title: The Kazhdan triangle of finite groups GHB_2(7) is flexibly Hilbert--Schmidt stable
distinct_from:
  ghb7-congruence-kernel-flexibly-hs-stable: that is flexible HS stability of the torsion-free congruence kernel H, with b_2(H;Q) >= 1380; this is stability of the ambient group G = GHB_2(7), which has torsion and b_2(G;Q) = 0, and which implies stability of H by descent to finite-index subgroups of a Kazhdan group
  triangle-of-finite-groups-hs-stability-is-edge-matching: that is the general equivalence between flexible HS stability of the colimit of a triangle of finite groups and an edge-matching property of genuine vertex representations; this is the open instance of that property for the vertex groups U_3(7), U_4(7), U_4(7)
---

**OPEN.** Let `G = G_{HB_2}(7)` (`cckw-ghb2-kms-group-structure`). The claim is that `G` is
flexibly Hilbert--Schmidt stable in Dogon's sense (arXiv:2211.10492v3, Definition 1.2). For every
asymptotic representation `σ_n : G → U(d_n)` in normalized HS norm, there are genuine
representations `π_n : G → U(D_n)` with `D_n ≥ d_n`, `D_n/d_n → 1` and
`||σ_n(g) − P_n π_n(g) P_n*||_2 → 0` for every `g`.

## If true

- `G` is a finitely generated Kazhdan group and the congruence kernel `H` has finite index. So `H`
  is flexibly HS stable by `flexible-hs-stability-descends-to-retracts-finite-index`; this is route
  `ghb7-kernel-stability-via-ghb7-stability`.
- `H` is hyperbolic and Kazhdan with `b_2(H;Q) ≥ 1380`. So
  `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` gives a non-hyperlinear hyperbolic finite
  central extension of `H`.

## Equivalent finite-group form

By `triangle-of-finite-groups-hs-stability-is-edge-matching`, the claim is equivalent to an
edge-matching property (EM). The data are:
- vertex groups `X_0 = <a,b> ≅ U_3(7)`, `X_1 = <c,b> ≅ U_4(7)`, `X_2 = <c,a> ≅ U_4(7)`;
- edge groups `<a>`, `<b>`, `<c>`, each cyclic of order 7.

**(EM).** Take any dimensions `d_n` and genuine representations `ρ_{i,n} : X_i → U(d_n)` with

```text
||ρ_{0,n}(b) − ρ_{1,n}(b)||_2 → 0,  ||ρ_{0,n}(a) − ρ_{2,n}(a)||_2 → 0,  ||ρ_{1,n}(c) − ρ_{2,n}(c)||_2 → 0.
```

Then there are genuine representations `π_n : G → U(D_n)`, `D_n/d_n → 1`, with
`||ρ_{i,n}(x) − P_n π_n(x) P_n*||_2 → 0` for every `i` and every `x ∈ X_i`.

The inputs to (EM) are genuine representations of three finite 7-groups, of orders 343, 2401 and
2401, whose restrictions to three cyclic groups of order 7 almost agree. No infinite group is left.

## Calibration (from established nodes)

- If `G` is hyperlinear, stability of `G` makes `G` residually finite
  (`hyperlinear-flexibly-hs-stable-group-is-residually-finite`). Through `H` it also forces a
  persistent prime degree-two class (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`).
- If `G` is not hyperlinear, `G` already answers `non-hyperlinear-group`.

## Attempts

- **Where the degree-two block sits for `G` (2026-09-13, lane `hl-nh-flexible-stability`).**
  - **The complex.** `G` acts on the contractible CAT(−1) complex `Y` with finite stabilizers:
    one orbit of triangles (trivial stabilizer), three orbits of edges (stabilizers of order 7),
    three orbits of vertices (stabilizers `X_0, X_1, X_2`).
  - **Standard fact, not re-read at source.** For a complex vector space `W` with a unitary
    `G`-action, the equivariant cochain complex `⊕_i W^{X_i} → ⊕_e W^{A_e} → W` computes
    `H^*(G; W)`, because finite stabilizers have no higher cohomology over `C`.
  - **The count.** Property (T) gives `H^1(G;W) = 0`, so for finite-dimensional `W`:

    ```text
    dim H^2(G;W) = dim W − Σ_e dim W^{A_e} + Σ_i dim W^{X_i} − dim W^G.
    ```

  - **Trivial module.** `1 − 3 + 3 − 1 = 0`. So the trivial-summand block that stops the Newton
    scheme for `H` (item 1 of `ghb7-kernel-blocks-degree-two-newton-stability`) is absent for `G`.
  - **Regular-type modules.** If every `X_i` acts on `W` by a multiple of its regular
    representation, then `dim H^2(G;W) = (1381/2401)·dim W − dim W^G`. This is the orbifold Euler
    characteristic density; compare `ghb7-l2-betti-two-is-orbifold-euler-characteristic`.
  - **So:** a Newton-type existence scheme for `G` still meets nonzero degree-two classes on
    properly non-amenable limits (`kazhdan-hs-instability-lives-on-properly-nonamenable-limits`).
    Removing `b_2` on the trivial summand does not remove the obstruction.
- **Exact gap.** (EM) for `U_3(7), U_4(7), U_4(7)`: a gluing statement for almost-matching genuine
  representations, uniform in the dimension.
