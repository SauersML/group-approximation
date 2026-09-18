---
rg: 2
id: ct-p-z-is-not-a-product-shift-full-group
kind: claim
title: Kohl's CT(Z) and every CT_P(Z) have nontrivial isotropy only at rational points, so none is isomorphic to Brin's nV (n >= 2) or to any full group of a product of shifts of finite type; and only the identity commutes with a canonical Cuntz family
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
  - conway-amusical-permutation-is-the-full-three-shift
distinct_from:
  conway-amusical-permutation-is-the-full-three-shift: that proves diagonal rigidity in the p-adic coordinates; this proves the coordinate-free statements (isomorphism type, commutants) that rigidity alone cannot give.
  ct-p-z-groups-are-pairwise-nonisomorphic: that separates the groups CT_P(Z) from each other; this separates all of them from the Brin–Thompson and product-SFT family.
---

**ESTABLISHED** for items 1–3 (lane proof, not independently reviewed; the only inputs are the cited
identification of `CT_P(Z)` and the Rubin–Matui isomorphism theorem). **No priority claimed.**
Item 4 is **OPEN** and gives a reduction only.

**Kourovka 17.58**, printed text (21st issue, 2026, `gq/src/kourovka/21tkt.tex` l. 9550–9551):
"Does CT(ℤ) have subgroups of intermediate (word-) growth?" (S. Kohl). It is **not** settled here.
This node answers the "writer" sub-question of `conway-amusical-permutation-is-the-full-three-shift`
at the level of isomorphism and of canonical trees.

## Setting

As in that node, `F_P = [[G_P]]` is the full group of the one-vertex `|P'|`-graph groupoid `G_P` on
`Ẑ_P = ∏_{q∈P'} Z_q` (`P' = P ∪ {2}`). Every germ of `G_P` is the germ of a canonical map
`y ↦ cy + d`, with `c ∈ Q_{>0}` a ratio of `P'`-smooth integers and `d ∈ Q`.

By `ct-p-z-is-a-one-vertex-k-graph-full-group`:
- `G_P` is minimal and effective, and `F_P = CT_P(Z)` for finite `P`;
- `CT(Z) = ∪_P CT_P(Z) = [[G_all]]` for the groupoid on the full profinite completion, since each
  element uses finitely many moduli.

## Statement

1. **Countable isotropy.** A point `x ∈ Ẑ_P` has nontrivial isotropy in `G_P` only if `x` is a
   rational number (a `P'`-integral rational).
2. **No product structure.** Let `G = G_1 × … × G_n`, with `n ≥ 2`, be a product of groupoids of
   one-sided irreducible non-periodic shifts of finite type, or the restriction of such a product to
   a nonempty clopen set. Let `A(G) ≤ H ≤ F(G)`. Then `H` is not isomorphic to `CT_P(Z)` for any set
   `P` of odd primes, nor to `CT(Z)`.
   - This covers Brin's `nV` (`n ≥ 2`), the mixed-arity products `[[G_{E_2} × G_{E_3}]]`, Matui's
     product groups, and, through restrictions to clopen sets, the Brin–Higman–Thompson variants.
3. **Canonical trees have trivial commutant.** Let `Z` be a box, and let `s_1, …, s_k` (`k ≥ 2`) be
   canonical maps of `Z` onto pairwise disjoint sub-boxes. Let `c : Z → Z` be any map that is
   canonical on each piece of a finite box partition and satisfies `c ∘ s_i = s_i ∘ c` for all `i`.
   Then `c = id`.
4. **Reduction for embeddings (OPEN).** Let `ρ : 2V → CT_P(Z)` be an embedding (`P` finite).
   - By Matte Bon's Extension Theorem (arXiv:1801.10133v2, Thm `t-intro-main`, read at source, TeX in
     `gq/src/bh-free-57/`), either:
     - (i) some point `y` of the support has an injective germ map `g ↦ [ρ(g)]_y`; or
     - (ii) the support `Z` is clopen, and `ρ` extends to a continuous pseudogroup morphism
       `G̃_{2V}^{[r]} → G̃_P|Z` for some `r ≥ 1`.
   - In case (ii), the images `s_i`, `t_j` of the two stacks' push maps are injections defined on all
     of `Z`, with pairwise disjoint ranges within each family, and every `s_i` commutes with every
     `t_j`. The spatial component `q : Z → X^{[r]}` intertwines them.
   - By item 3, the family `{s_i}` cannot consist of single canonical maps on a box. So a writer
     inside `CT_P(Z)` must be built on a genuinely piecewise tree.
   - Case (i) is excluded by Matte Bon's Cor. `c-intro-asdim` once the leaves of `G_P` are known to
     have finite asymptotic dimension. That is expected, since the degree map to `Z^{P'}` has
     ultrametric fibres, but it is not proved here.

## Proof

**Item 1.** Let `γ` be a nontrivial isotropy element at `x`. It is the germ at `x` of a canonical map
`κ(y) = cy + d` with `κ(x) = x` and `κ ≠ id` near `x`.
- If `c = 1`, then `κ(x) = x` forces `d = 0`, so `κ = id` on its box, which is a contradiction.
- Hence `c ≠ 1`, and in every coordinate `x_q = d/(1−c)`. So `x` is this rational number.

**Item 2.**
- **Isomorphism gives a groupoid isomorphism.** Rubin–Matui (Matte Bon 1801.10133v2, Cor. `c-isom`,
  read at source): for minimal effective étale groupoids `G_1, G_2` over Cantor spaces and groups
  `A(G_i) ≤ H_i ≤ F(G_i)`, an isomorphism `H_1 ≅ H_2` forces `G_1 ≅ G_2`.
  - `G_P` is minimal and effective (setting).
  - `G` is minimal, because its factors are irreducible and non-periodic.
  - `G` is effective, because the points whose coordinates all have trivial isotropy form a dense
    `G_δ`.
- **Isomorphisms preserve the isotropy set.** A groupoid isomorphism restricts to a homeomorphism of
  unit spaces and carries isotropy groups to isotropy groups. So it maps the set of points with
  nontrivial isotropy bijectively onto the corresponding set.
- **Countable against uncountable.** In `G_P` that set is countable (item 1). In `G` it is
  uncountable.
  - If `a = u v^∞` is eventually periodic in the first factor, then `(a, |v|, a)` is a nontrivial
    isotropy element there, so `(a, b)` has nontrivial isotropy for every `b`.
  - Eventually periodic points are dense, so every nonempty clopen set contains some `{a} × B`,
    with `B` a Cantor set.
- **CT(Z).** For `CT(Z)` use `G_all`. Its isotropy points are again rational by the same computation,
  hence countable.

**Item 3.** Identify `Z` with `Ẑ_P` by a canonical map; conjugating by it preserves canonical maps.
Then `s_i(y) = ρ_i + m_i y` with `m_i ≥ 2`, since each range is a proper sub-box. For a word `w`,
write `s_w(y) = ρ_w + m_w y`. The boxes `s_w(Ẑ)` with `|w| = n` are pairwise disjoint.

Fix `x`, and let `c(y) = ay + b` near `x`.
- **Transport of coefficients.** Near `s_w(x)`, `c(z) = a_w z + b_w`, where `(a_w, b_w)` lies in the
  finite set of coefficient pairs of `c`. The identity `c(s_w y) = s_w(c y)` holds on an open set, so
  the coefficients agree. This gives `a_w = a` and `b_w = m_w b + ρ_w (1−a)`.
- **If `a ≠ 1`.** Put `y_0 = b/(1−a) ∈ Q`, so `b_w = (1−a)(ρ_w + m_w y_0)`.
  - Words of length `n` with a common modulus `m_w = M` have distinct `ρ_w`, so their `b_w` are
    distinct.
  - There are `k^n ≥ 2^n` words but at most `(n+1)^k` moduli, so some modulus class is unbounded as
    `n → ∞`. That contradicts finiteness.
- **If `a = 1`.** Then `b_{i^n} = m_i^n b` is bounded, so `b = 0`. Hence `c = id` near every `x`.
  `∎`

## What this decides and what it leaves

- **Decided.** No isomorphism identifies `CT(Z)` or `CT_P(Z)` with a Brin–Thompson or product-SFT
  full group, in any coordinates. The obvious writers, which commute with a canonical tree, do not
  exist.
- **Not decided.** Whether `2V` (or `RTM`, or `[[X]]` for some minimal subshift `X`) embeds in
  `CT(Z)`. An embedding must blow up fixed points into fibres, as `V` does inside `CT_{3}(Z)`.
  - Take the image `h` of a one-stack element of `2V`, and the fibres of `q` over its fixed slice.
  - For all but countably many of those fibres, every point fixed by some power `h^n` is fixed by
    `h^n` on a whole neighbourhood. The reason: for `h ∈ F_P`, the set `Fix(h) ∖ int Fix(h)` is
    finite, since a piece with slope `1` is the identity or has no fixed point, and a piece with slope
    `≠ 1` has at most one fixed point.
  - So away from countably many fibres, the images act either locally trivially or without periodic
    points.
- **Kourovka 17.58** stays OPEN. Its full-group route needs exactly the embedding question above.

**Lesson for general BH.**
- **Isotropy is an isomorphism invariant.** Rubin–Matui turns "where does isotropy live" into a group
  invariant.
- **Two kinds of hosts, separated for good.** Arithmetic hosts (`CT_P(Z)`, isotropy on rational
  points only) are never product hosts (`nV`, isotropy along whole slices). This splits the finitely
  presented simple Cantor hosts used for BH into two provably different families.
- **For embeddings, look for fibres, not coordinates.** An embedding of a product host into an
  arithmetic one must turn fixed slices into aperiodic fibres, and cannot commute with a canonical
  tree. A construction that needs a writing head inside `CT(Z)` must therefore supply a
  non-canonical tree whose commutant contains a second stack.
