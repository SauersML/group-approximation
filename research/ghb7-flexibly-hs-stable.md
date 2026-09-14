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
- **Invariant-fraction counts cannot refute (EM) (2026-09-13, same lane).**
  - **The candidate obstruction.** For a genuine finite-dimensional `π`, the count above gives
    `1 − Σ_e f_e + Σ_i f_i ≥ 0`, where `f_X` is the fraction of `X`-invariant vectors. The fractions
    `f_X` are continuous under normalized-HS closeness and `o(d_n)` padding. So data with
    `Σ_e f_e − Σ_i f_i > 1 + c` would be an instability witness.
  - **Genuine vertex data can violate the count.** Take sums of linear characters of the
    abelianizations `Z_7²`, placing half the mass on characters trivial on `a` and half on
    characters trivial on `b`. This gives `f_a = f_b = 1/2` and `f_{X_0} = 0`. Exact edge agreement
    rules the violation out.
  - **Every asymptotic representation satisfies the count in the limit.**
    - Let `σ^ω : G → U(M)` be the limit in the tracial ultraproduct, and let `G` act on `W = L²(M)`
      on the left.
    - The equivariant cochain complex `⊕_i W^{X_i} → ⊕_e W^{A_e} → W` consists of Hilbert right
      `M`-modules and computes `H^*(G;W)`.
    - Property (T) makes `H^1(G;W) = 0`.
    - Additivity of von Neumann dimension (Lück) then gives
      `1 − Σ_e τ(E_{A_e}) + Σ_i τ(E_{X_i}) = τ(E_G) + dim_M H̄^2 ≥ 0`, with `E_X` the averaging
      projections.
    - Standard facts, not re-read at source: Delorme–Guichardet and Lück additivity.
  - **So** no linear count of invariant fractions separates (EM) from its failure. An instability
    witness must be detected by finer data than the traces of the averaging projections.
- **One-edge reduction (2026-09-13, lane `hl-ghb7-edge-matching`).**
  - **Vertex data** (`ghb7-triangle-vertex-groups-split-abelianizations`, exact computation through
    `ψ`): `X_0` has order 343 with derived subgroup of order 7; `X_1, X_2` have order 2401 with
    derived subgroups of order 49. Every abelianization is `(Z/7)^2` with the two edge generators as
    a basis. Edge centralizers have order 49, except `c` in `X_1` and `X_2` (order 343).
  - **Reduction** (`triangle-edge-matching-reduces-to-one-edge-holonomy`). Padding with `O(εd)`
    linear characters equalizes the edge eigenvalue counts, and near-identity intertwiners then make
    `b` and `a` agree exactly. So (EM) is equivalent to (HA): only the mismatch on `c` must be
    absorbed. Recorded as OPEN `ghb7-one-edge-holonomy-absorption`, with route
    `ghb7-stability-via-one-edge-holonomy` into this claim.
  - **Direct-sum padding absorbs no first-order obstruction (heuristic, not landed as a claim).** The
    equivariant cochain complex of a direct sum of `G`-modules is block diagonal. So a defect class
    that is nonzero in `H^2(G; End ρ)` stays nonzero after adding a genuine summand. Absorption in
    (HA), if it happens, must use the mixing that flexible compression allows, at scale
    `((D−d)/d)^{1/2}`, rather than direct summands.
  - **Twisted counts do not help either (standard facts, not re-read at source).** `G^ab = (Z/7)^3`,
    the colimit of the vertex abelianizations. The invariant-fraction fence above applies verbatim to
    `W ⊗ λ` for each of the 343 linear characters `λ`. So no linear count of isotypic fractions of
    vertex and edge groups separates (EM) from its failure.
  - **A refutation route (sharpened 2026-09-13, same lane).** The earlier wording named the
    Ioana–Spaas–Wiersma mechanism. The criterion that applies to a hyperbolic group, with no `Z^2`
    subgroup, is `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` with a central kernel. It is
    recorded as OPEN premise `ghb7-finite-index-z-extension-center-survives` (some finite-index
    subgroup has a Kazhdan central `Z`-extension whose centre survives at unbounded orders in finite
    quotients), with route `ghb7-instability-via-visible-central-extension` into OPEN
    `ghb7-is-not-flexibly-hs-stable`. Real classes exist at `H`; survival of the centre is open.
- **Exact gap.** (HA) for `GHB_2(7)` (`ghb7-one-edge-holonomy-absorption`): after `b` and `a` agree
  exactly, remove the `c`-mismatch using the commutants of `ρ_0(b)` and `ρ_0(a)` plus `o(d)` flexible
  padding, uniformly in the dimension.
