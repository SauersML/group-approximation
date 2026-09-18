---
rg: 2
id: abht-path-folds-accept-exactly-expansive-rational-half-planes
kind: claim
title: The ABHT path-fold over F_n x Z (n >= 2) is faithful exactly when the fibre has a determining rational half-plane; one side suffices, horizontal expansivity is not needed, corner determinism is enough, and then the fold is free and minimal when the fibre is, and quantum rigid exactly when the fibre is
requires:
  - path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
distinct_from:
  path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid: that proves the rigidity transfer under ABHT's two-sided hypothesis (one row determines everything); this shows that only one side is used, and that one side is also necessary for the fold to be the fold.
  sfts-without-two-sided-faults-are-quantum-rigid: that asks for a determining side on every line and gets rigidity; this needs one determining rational side and gets foldability, which says nothing about rigidity.
  four-way-deterministic-sft-rigidity-lives-on-axis-faults: that shows four-way determinism makes every non-axis line expansive; this needs only one corner rule and uses it for folding.
  a2-busemann-transplants-preserve-quantum-rigidity: that transplants cone-deterministic fibres to Ã2 lattices; the same corner-deterministic fibres fold to F_n x Z by this node.
---

**ESTABLISHED** through `one-sided-path-fold-acceptance-proof` (lane proof by bh-g2-abh, 2026-09-18). The
proof is elementary and has not been reviewed. The ABHT statements used were re-read at source (arXiv:2204.11492v3,
§5, TeX ll. 559–786). No priority is claimed.

## Setting

- **The fibre.** `X ⊆ A^(Z^2)` is a nearest-neighbour SFT.
- **Determining normals.** Following `sfts-without-two-sided-faults-are-quantum-rigid`, a normal `ν` is
  *determining* if two points of `X` that agree on `{z : ⟨z, ν⟩ < t}` are equal. It is *rational* if
  `ν ∈ Q^2`.
- **Upper half-plane determines.** `ν = −e_2` is determining exactly when
  `x|_(Z × [c, ∞)) = x'|_(Z × [c, ∞))` implies `x = x'`.
- **The fold.** `Z_X ⊆ (A × S)^(F_n × Z)` is the SFT defined by ABHT's local rules:
  - the flow shift;
  - horizontal `X`-dominoes on `{g, gt}`;
  - vertical `X`-dominoes on each flow edge `g → gs`, with bottom at `g` and top at `gs`.
- **Faithful.** The fold is *faithful* if `Z_X = {x ⊗ y}`, the configurations of ABHT Prop. `configsJuntas`.

## Theorem

1. **Exact acceptance.** For `n >= 2`, `Z_X` is faithful iff `−e_2` is determining for `X`. For `n = 1`
   it is always faithful, since `F_1 × Z = Z^2` and the fold is a recoding. `x ⊗ y ∈ Z_X` holds for every
   `x ∈ X`, with no hypothesis.
2. **Normal form.** `−e_2` is determining iff, after a vertical higher-block recoding (still
   nearest-neighbour), row `j` determines row `j − 1` by a sliding block code.
3. **Transfer.** Suppose `Z_X` is faithful. Then:
   - `Z_X` is free if `X` is (ABHT's argument); the converse is sketched in the proof;
   - `Z_X` is minimal if `X` is;
   - `Z_X` is quantum rigid over `k`, at some scale, iff `X` is.

   For rigidity, the up direction is `path-fold-rigidity-transfer-proof`, which only ever uses the downward
   rule and faithfulness. The down direction is `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`,
   which needs no expansivity at all.
4. **Up to recoding.** Some `GL_2(Z)`-image of some recoding of `X` has a faithful fold iff `X` has a
   **rational determining normal**. Horizontal expansivity, ABHT's hypothesis, is both normals of one
   rational line determining. It is sufficient but not necessary.
   - *Example.* Ledrappier's shift `x(i, j−1) = x(i, j) + x(i+1, j)` over `F_2` folds faithfully after a
     horizontal 2-block recoding to nearest-neighbour form, with no change of direction.
   - Its horizontal line is not expansive: `−e_2` determines, `+e_2` does not.
   - It is not a separating example up to `GL_2(Z)`, since it has expansive non-axis lines.
5. **Corner determinism suffices.** Suppose `x(z) = G(x(z+e_1), x(z+e_2))` for all `x ∈ X` and all `z`,
   i.e. `X` is NE-deterministic. Examples are Wang tiles determined by their north and east colours
   (Kari–Papasoglu, Lukkarila). Then `−(1,1)` is determining, and `(a, b) ↦ (a, a + b)` followed by a `2×2`
   recoding puts `X` in the normal form of item 2, with radius 2. The same holds for any corner after a
   rotation.

## Corollary

Suppose some `Z^2` SFT is free, minimal and quantum rigid over `F_2`, and has a rational determining normal (for
example, it is corner-deterministic). Then for every `n >= 1`, `F_n × Z` has a free, minimal, quantum rigid
SFT. That SFT is finitely presented over `F_2` in the crossed-product sense and central simple.

This is the target `foldable-free-minimal-quantum-rigid-z2-sft-exists`. It has no dependence on
`J_2(Ω_U)`.

## The crossing-wire minimal shift (49939b957a), assessed

- **As landed** (`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`):
  - Bits enter each macrotile from all four sides. The zone may run a two-way head, and margins are
    side-local.
  - So it is not corner-deterministic as specified. Its foldability is exactly the existence of a rational
    determining normal, which is **not decided here**.
  - *Heuristic against the axis normals, unproved.* Take a point whose level-`(k−1)` macrotile lies in the
    first non-margin child row below the top margin, at every level. The upper half-plane then sees only
    the top macro-colours of its ancestors, because side-local margins transmit nothing else. Two ancestor
    chains with equal top colours would make `−e_2` non-determining. Whether DR's layout has such chains
    was not checked.
  - So horizontal expansivity, the target bh-g2-fixedpoint-a is currently building, is more than the fold
    needs, and is plausibly blocked for side-local layouts.
- **Variant A4 of its proof** (SW-deterministic macrotiles, one-way zone):
  - If the macro tile set `τ_k` of **one** level is SW-deterministic (top and right macro-colours are
    functions of bottom and left), the variant is foldable, and the Corollary applies.
  - The ground tiles need not be SW-deterministic: see check 4 of
    `fold-transfer-theorem-for-fibres-with-a-determining-half-plane`, which corrects an earlier ground-level
    wording here.
  - This is a design constraint for bh-g2-fixedpoint-a, not a claim that the variant exists.
- **Kakutani models.** Determining normals are conjugacy and `GL_2(Z)` invariants, but not Kakutani
  invariants. The Jeandel–Rao `X_0` has an expansive rational line, while Labbé's `Ω_U` has fault lines
  on both axes.
  - Rigidity is a Kakutani invariant (`recognizable-morphisms-give-kakutani-equivalent-z2-groupoids`).
  - Freeness and minimality are too, by the standard fact that restricting a groupoid to a full clopen set
    keeps it principal and minimal.
  - So any SFT model in the crossing-wire shift's Kakutani class with a rational determining normal would
    also do. None is exhibited.

## Lesson for general BH

- **Folds need one-sided determinism, not expansivity.** The tree branches in one direction only, so a
  fibre must determine its past from its future on **one** rational side. The same condition makes the
  fold equal to the fold (item 1), so the criterion is exact.
- **Corner determinism is the common interface of the non-amenable transfers.** One corner rule
  `x(z) = G(x(z+e_1), x(z+e_2))` serves both:
  - the tree fold to `F_n × Z` (this node);
  - the Busemann transplant to Kazhdan Ã2 lattices (`a2-busemann-transplants-preserve-quantum-rigidity`,
    cone-deterministic fibres).
- **Design target.** Build the amenable crux object corner-deterministic from the start: free, minimal,
  rigid and SW-deterministic. That single `Z^2` object then transports to both non-amenable families.
