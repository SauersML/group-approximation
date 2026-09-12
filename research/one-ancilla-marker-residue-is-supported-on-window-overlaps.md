---
rg: 2
id: one-ancilla-marker-residue-is-supported-on-window-overlaps
kind: claim
title: The one-ancilla Bennett word for the integer marker clears the ancilla exactly up to a Boolean-vanishing residue from overlapping marker windows
distinct_from:
  injective-binary-automata-are-stably-formalizable: that is the open stable hub over every group and alphabet; this isolates, over the integers with one ancilla, the single formal residue whose clearing is the whole question.
  marker-flip-cells-avoid-all-marker-control-windows: that is the Boolean disjointness fact; this is the formal (free-ring) consequence for the Bennett word and the open termination question it leaves.
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
---

**OPEN.** Work over the free ring `F_2[X]`, two tracks: data variables `x_g`, ancilla `y_g`. Let
`A: y_g <- y_g + m(x)_g`, `B: x_g <- x_g + y_g`, `A': y_g <- y_g + m(x)_g` be the three track-shear
gates (each a `Z`-equivariant formal involution). The word `W = A' B A` is structurally reversible,
hence formalizable with reverse `A B A'` (`structurally-reversible-automata-are-formalizable`).

**The residue.** On the ancilla-input-zero slice `y = 0`, `W` sends `x` to data `x + m(x) = tau(x)` and
ancilla to `r(x)_g = m_g(x) + m_g(x + m(x))`. By `marker-flip-cells-avoid-all-marker-control-windows`,
`r(x)_g = 0` on every Boolean point, so `r` lies in the Boolean ideal `(x_h^2 + x_h)`. Its lowest-degree
part is a sum over cells `g` whose window `C_g` meets the cell of a marker at distance `5 <= d <= 6`
(the overlapping-window pairs); monomials have total degree `>= 8`.

**Claim to decide.** Either
- (positive) a finite `Z`-equivariant word of further track shears, sitewise-linear maps and constant
  translations on `1 + m` tracks has Boolean shadow `tau x id` — clearing `r` and all its higher
  substitution layers in finitely many degrees and bounded memory — in which case `tau` is stably
  formalizable and, with Kaplansky direct finiteness of `F_2[Z]`, the integer warm-up of
  `injective-binary-automata-are-stably-formalizable` holds; or
- (negative) no such finite word exists, i.e. the graded clearing of `r` (solvable layer by layer by
  `binary-left-inverse-pairs-are-boolean-adically-formalizable`) fails to terminate, giving a
  multi-track extension of the one-track affine rigidity of
  `formalizable-binary-pairs-over-biorderable-groups-are-affine`.

This is the integer warm-up only; the load-bearing test object is on a finitely generated simple host
(`injective-binary-automata-are-stably-formalizable`, scope note).

## Attempts

- **One extra gate does not clear `r`.** Appending `A'': y_g <- y_g + f` with `f` a track shear reading
  data can cancel `r` only if `f = r` formally; but `r` reads `y`-free data of degree `>= 8` across a
  width-13 window, and is not itself a marker-type product, so a single bounded shear of the allowed
  form does not reproduce it. Two or more passes re-enter the graded problem.
- **Regrouping escapes, but is not the target.** Along `4Z` the marker is a word of sitewise block
  shears (`marker-involution-is-formalizable-after-regrouping`, `kari-words-give-virtual-formalizability-over-integers`),
  terminating. The open question is a `Z`-equivariant word with ancilla, with no blocking.
- **Where a proof must live.** Positive: bound the degree/memory growth of the layerwise corrections of
  `r`. Negative: an invariant of `Z`-equivariant track-shear words with identity tracks that `tau x id`
  violates while the `4Z`-regrouped word does not.
- Verification requested from w3-vf-nonlinear.
