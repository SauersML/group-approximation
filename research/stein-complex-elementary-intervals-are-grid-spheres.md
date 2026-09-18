---
rg: 2
id: stein-complex-elementary-intervals-are-grid-spheres
kind: claim
title: An elementary interval of the twisted Brin--Thompson poset is a homotopy sphere of dimension e − 2 when every tree is a full brick split in e colors in total, and is contractible otherwise
distinct_from:
  twisted-brin-thompson-type-fn-criterion: that is the finiteness characterization of SV_G; this is the local homotopy computation of open intervals that its proof consumes.
---

**ESTABLISHED** by `stein-interval-grid-sphere-proof` (lane proof). The computation is the
nerve argument in the proof of Belk--Zaremsky, arXiv:2001.04579, Lemma `lem:all_big`
("Descending split link, second case"). There it is applied to the descending links of the
Stein complex; here it is stated for an arbitrary elementary interval. No priority claimed.

## Setting

Belk--Zaremsky, §5 (TeX read on MSI, `gqsrc/bh-openq/2001.04579/twisted_Brin_Thompson.tex`):
- `G` acts faithfully on a countable set `S`.
- `P` is the poset of classes `[h]` of elements of the groupoid `SV_G` modulo twisted
  permutations, ordered by expansion; `P_1` is its corank-one part.
- `v ⪯ w` means `w` is an elementary expansion of `v`.
- An interval `[v, w]` is *elementary* if `v ⪯ w`.
- Up to the action, `v = [id_q]` and `w = [f]` with `f = f_1 ⊕ ... ⊕ f_q` an elementary
  multicolored forest, where `f_i` is the (possibly trivial) tree on root `i`.
- `Spec(f_i)` is the set of colors `s` such that `f_i` changes coordinate `s` at some
  point of the cube.
- `SSpec(f_i)` is the set of colors `s` such that `f_i` changes coordinate `s` at every
  point (BZ, before Lemma `lem:all_big`).

Call `f` a **grid forest** if `SSpec(f_i) = Spec(f_i)` for every `i`. Equivalently, each
nontrivial `f_i` is the full split of its cube into the `2^{|Spec(f_i)|}` elementary bricks
in the colors `Spec(f_i)`. Put `e(f) = Σ_i |Spec(f_i)|`.

## Statement

Let `[v, w] = [[id_q], [f]]` be an elementary interval with `v ≠ w`. Then the realization of
the open interval `(v, w)` is:
- homotopy equivalent to the sphere `S^{e(f)−2}` if `f` is a grid forest, with `S^{−1} = ∅`
  when `e(f) = 1`;
- contractible otherwise.

Consequently `H_k(|[v,w]|, |[v,w)| ∪ |(v,w]|) ≅ H̃_{k−2}(|(v,w)|)` is `Z` for `k = e(f)` and
`0` otherwise in the grid case, and vanishes for every `k` in the non-grid case.

## Examples

- One simple split: `(v, w) = ∅ = S^{−1}`, with `e = 1`.
- Splits at two different roots, in any colors: `(v, w)` is two points, `S^0`, with `e = 2`.
- The full split `(x_b ⊕ x_b) x_r` of one cube in two colors: `(v, w)` has six elements and
  two contractible components, so it is `≃ S^0`, with `e = 2`, although the interval has
  length 3.
- `(x_b ⊕ id) x_r`: `(v, w)` is one point, contractible (`SSpec = {r} ≠ {r, b} = Spec`).
