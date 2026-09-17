---
rg: 2
id: brin-thompson-groups-nv-are-a-t-menable
kind: claim
title: "Every Brin-Thompson group nV (n >= 2) has the Haagerup property"
---

For every `n >= 2`, the Brin–Thompson group `nV` admits a proper conditionally
negative definite function, equivalently a metrically proper affine isometric
action on a Hilbert space. Since `nV <= mV` for `n <= m`, the claim for all `n`
is equivalent to the claim for arbitrarily large `n`.

This is the "yes" answer to the Haagerup part of Zaremsky Problem 2.7
(`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`).

## Attempts

- **Farley-type charts (dies for n >= 2).** For `V`, let `X` be the set of
  pairs `(U, φ)` with `U ⊆ C` clopen and `φ: C → U` a homeomorphism in the
  Thompson groupoid, `V` acting by `g·(U, φ) = (gU, g∘φ)`, and `A ⊆ X` the
  standard cylinder charts `ι_w(u) = wu`. Then `g∘ι_w` is standard exactly
  when `[w]` lies inside a leaf of the reduced domain tree of `g`, so
  `|gA Δ A|` is the number of internal nodes of the reduced domain and range
  trees: finite, and proper in `g`. This gives a-T-menability of `V`.
  The same construction for `nV` with standard brick charts is not
  commensurated: `g(x, y) = (x, y)` on `[0] x C` and `(x, s(y))` on `[1] x C`,
  with `s` swapping the first letter, is not canonical on any brick
  `C x [v]`, and there are infinitely many such bricks. Breaks in dimension
  `>= 2` are codimension-one, so every brick-like family is broken infinitely
  often.
- **Stein–Farley complex (dies).** The cube complex of expansions of `nV`
  (Fluch–Marschler–Witzel–Zaremsky) is not CAT(0) for `n >= 2`: splitting a
  piece in direction 1 and then both halves in direction 2 gives the same
  vertex as the other order, a 6-cycle in the 1-skeleton that no cube corner
  or pair of squares fills. So its 1-skeleton is not a median graph.
- **No cubical proof at all.** `2V` has a distortion element with
  `|f^n| = O(log^4 n)` and admits no proper action on any CAT(0) cube complex
  (Callard–Salo, arXiv:2208.00685). This supersedes the two route-specific
  obstructions above. A Haagerup proof must be non-cubical: measured walls with
  an invariant measure, or a direct proper cocycle. Any proper conditionally
  negative definite `ψ` grows at most like `O(log^8 n)` along `⟨f⟩`, since
  `√ψ` is subadditive.
- **Coupled objects fail too.** Diagonal-type curve charts
  `u ↦ (αu, βu)` couple the tails, so breaks happen only when both prefixes
  are short. But canonical maps shift the imbalance `|α| - |β|` by the
  piecewise cocycle `δ_x - δ_y`, so balanced curves are not commensurated. Every
  object tried breaks by codimension-one faces (uncoupled objects) or by
  anisotropic scaling (coupled objects).
- **Local similarities.** Hughes (arXiv:0804.0610) proves a-T-menability for
  locally finitely determined groups of local similarities of compact
  ultrametric spaces. Brick maps scale the coordinates by independent powers of
  2, so they are not similarities of the max ultrametric on `C^n`. The theorem
  does not apply as stated (paper not read in full).
- **Groupoid-generic proofs (dies; class-kill).** `nV ≤ [[G_2^n]]`, and `G_2^n` is
  ample, topologically amenable, minimal, essentially principal and purely infinite.
  `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` builds another groupoid
  with all these properties, `(M ⋊ Γ) × G_2` with `Γ = Z^3 ⋊ SL_3(Z)` acting freely,
  minimally and amenably on a Cantor set `M`. Its full group contains `Γ`.
  - **Invariant:** property (T) of `Γ`.
  - **Where every member dies:** the passage from groupoid hypotheses to a proper
    conditionally negative definite function on `[[𝒢]]`, which would restrict to a
    proper one on `Γ`.
  - **Consequence:** a Haagerup proof, or even a proof that Kazhdan subgroups are finite,
    must use structure beyond this class, such as the zipper, product-of-trees or
    local-similarity combinatorics of `G_2^n`, or expansivity. Matui's SFT theorem
    (`sft-topological-full-groups-have-the-haagerup-property`) uses such structure.
  - **Not ruled out:** proofs that use compact generation or expansivity of the
    groupoid. It is not known whether `(M ⋊ Γ) × G_2` is compactly generated.
- **Split along the triangular subgroup (2026-09-17, swarm-0917-w4-nv-cocycle; route tree
  plus class-kill).**
  - `haagerup-splits-as-coset-plus-subgroup-properness` (established): for any subgroup `H`,
    the Haagerup property is equivalent to a cnd function proper modulo `H` plus a cnd function
    proper on `H`. No normality is needed, so it applies to the simple group `nV`.
  - Route `brin-thompson-nv-a-t-menable-via-triangular-split` with `H = T_n`, the elements
    preserving the coordinate tower `C^n → ... → C`. R1: a cnd function proper modulo `T_n`. R2: a
    cnd function on `nV` proper on `T_n`, which implies Problem B for `Γ = V, Z`. Both are
    necessary, so this route is an equivalence.
  - `brin-thompson-triangular-subgroup-is-undistorted` (established): every infinite-order
    element of `T_n` grows linearly in the exponent cocycle, so it is undistorted in `nV`.
  - **Class-kill.** `brin-thompson-nv-no-cubical-action-proper-mod-triangular` (established)
    rules out "Farley-type walls for the cosets, plus Problem B for the fibres". No
    commensurating action, CAT(0) cube complex or wall space is proper modulo `T_n`, or modulo
    any undistorted subgroup.
    - **Invariant:** growth along the distorted Callard–Salo cyclic subgroup `⟨f⟩`.
    - **Where every member dies:** the bounded-or-linear dichotomy makes the wall count bounded
      on `⟨f⟩`. The pigeonhole into finitely many cosets then forces a power of `f` into `H`,
      where it would be undistorted
      (`cubical-coset-proper-actions-capture-distorted-elements`).
    - R1 must therefore be non-cubical, with `ψ_1(f^N) → ∞` and `ψ_1(f^N) = O(log^8 N)`.
