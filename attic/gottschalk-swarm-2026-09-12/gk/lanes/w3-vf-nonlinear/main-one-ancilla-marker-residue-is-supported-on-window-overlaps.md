---
rg: 2
id: one-ancilla-marker-residue-is-supported-on-window-overlaps
kind: claim
title: The one-ancilla Bennett word for the integer marker clears the ancilla at zero input up to a Boolean-vanishing formal residue, and is not a realization of the marker times identity
distinct_from:
  injective-binary-automata-are-stably-formalizable: that is the open stable hub over every group and alphabet, whose First-test Attempts entry names this residue; this computes its lowest-degree part, shows why the Bennett word is not a candidate, and poses the integer decision.
  marker-flip-cells-avoid-all-marker-control-windows: that is the Boolean disjointness fact; this is the free-ring behaviour of the Bennett word, where that fact does not hold formally.
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
---

**OPEN.** Work over the free ring `F_2[X]`, with data variables `x_g` and ancilla variables `y_g`. The
gates `A: y_g <- y_g + m_g(x)`, `B: x_g <- x_g + y_g`, and `A'`, which is `A` reading the updated data,
are `Z`-equivariant track shears, each a formal involution. The word `W = A' B A` is structurally
reversible, so it forms a formal pair with its reverse
(`structurally-reversible-automata-are-formalizable`).

**The residue.** This is the residue of the hub's First-test entry. Formally `W(x, 0) = (x + m(x), r(x))`
with `r_g = m_g(x) + m_g(x + m(x))`.
- `r` vanishes on every Boolean point by `marker-flip-cells-avoid-all-marker-control-windows`, so it lies
  in the Boolean ideal `(x_h^2 + x_h)`.
- `m_g` is multilinear in the cells of `C_g`, so `r_g = Σ_(∅ ≠ S ⊆ C_g) (Π_(k ∈ S) m_k) ∂_S m_g`. Every
  `j ∈ C_g` contributes a first-order term `m_j ∂_j m_g`.
- The lowest-degree part of `r_g` is `x_(g-2) x_g x_(g+1) + x_(g-1) x_g x_(g+2)`, from `j = g - 1` and
  `j = g + 1` (computed by w3-vf-nonlinear). The first-order terms with `|j - g| = 2, 3` and all terms
  with `|S| >= 2` have degree `>= 4`. So `r != 0` formally. Its lowest-degree part comes from adjacent
  cells, not from the distance-5 window overlaps that the id names.

**Not a realization.** For Boolean `y` the data output of `W` is `x + y + m(x)`. So `W` has shadow
`tau x id` only on the slice `y = 0`, and clearing `r` with further ancilla gates would still not give
`tau x id`. A realization must also change the data gates. Its data output must be `y`-free on points
(hub).

**Claim to decide.** Is `tau` stably formalizable? That is, for some `m`, is `tau x id` on `1 + m` tracks
the shadow of a `Z`-equivariant finite-memory formal pair? A finite word of track shears,
sitewise-linear maps, sitewise permutations and constant translations with shadow `tau x id` would be
one.
- (positive) Then the integer instance of `injective-binary-automata-are-stably-formalizable` holds for
  this test object, and with it the dihedral and V markers (hub, w4-dihedral-marker entry).
- (negative) No such pair exists, for any `m`. Every graded layer is onto
  (`binary-left-inverse-pairs-are-boolean-adically-formalizable`), so this is a failure of termination.
  It would need an invariant of multi-track formal pairs extending the one-track rigidity of
  `formalizable-binary-pairs-over-biorderable-groups-are-affine`.

## Attempts

- **Clearing the ancilla residue is not enough.** An earlier entry here argued that one extra gate
  `y += f(data)` cannot clear `r`. It rested on a false degree bound (`>= 8`, across the overlaps), so
  it is withdrawn. The expansion above has degree-3 terms. And since `W` is wrong on the data track for
  `y != 0`, no ancilla-only repair of `W` realizes `tau x id` anyway.
- **The data track is written at least twice.** Consider words of data–ancilla track shears plus
  automorphisms of the ancilla tracks alone. If the data track is written by a single gate `x += f(z)`,
  then `z` runs over every ancilla configuration as `y` does, so `f(z) = m(x)` forces `f` to be constant.
  So between two data writes, the cells that marker windows read carry `y`-dependent values. The `4Z`
  word avoids this because the flip of one residue class reads only the other classes (artifact 2.4).
- **Regrouping escapes, but is not the target.** Along `4Z` the marker is a word of four track shears
  (`marker-involution-is-formalizable-after-regrouping`, `kari-words-give-virtual-formalizability-over-integers`).
  The open question is a `Z`-equivariant pair with ancillas and no blocking.
- **Where a proof must live.** Positive: a translation-invariant way to hold a marker's controls fixed
  while its target flips, without residue classes. Negative: an invariant of `Z`-equivariant formal
  pairs with identity ancilla tracks that `tau x id` violates and the `4Z` word does not.
- w3-vf-nonlinear (62f488374) failed the earlier support and degree statement; this node is corrected.
