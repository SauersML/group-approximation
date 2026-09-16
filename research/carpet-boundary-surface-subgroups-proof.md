---
rg: 2
id: carpet-boundary-surface-subgroups-proof
kind: route
title: A peripheral circle stabilizer is quasiconvex and finite-by-cocompact-Fuchsian, so it is virtually a surface group
target: carpet-boundary-hyperbolic-groups-have-surface-subgroups
requires:
  - kapovich-kleiner-one-dimensional-boundary-classification
  - finite-by-cocompact-fuchsian-groups-are-virtually-surface
---

Fix a homeomorphism from `∂G` to the Sierpinski carpet.

## Step 1: the carpet has a peripheral circle

In Kapovich--Kleiner, Section 2, property (2), the peripheral circles of a Sierpinski carpet `S`
are "precisely the nonseparating topological circles in `S`". This was read in the same PDF as
the import, 2026-09-16. So it suffices to exhibit one nonseparating circle.

**Model.** In the standard construction, the unit square is repeatedly subdivided into nine and
the open middle squares are removed. On `S^2 = R^2 ∪ {∞}` the result is

`S = S^2 minus (int D_0 ∪ ⋃_{i >= 1} int D_i)`,

where:
- `D_0 = S^2 minus (0,1)^2`;
- the `D_i` for `i >= 1` are the closures of the removed middle squares.

These are pairwise disjoint closed disks, with diameters tending to `0`. Each removed closed square
lies in the interior of the kept square it is the middle of, which is why they are disjoint.

**Claim.** `C_0 = ∂D_0`, the boundary of the unit square, is a circle in `S` that does not
separate `S`.

- `C_0` lies in `S`, because it meets no `int D_i`.
- Put `V = S^2 minus D_0 = (0,1)^2`, which is connected, and `T = S minus C_0 = V minus ⋃_{i>=1} int D_i`.
- Suppose `T = A ⊔ B`, with `A` and `B` nonempty and closed in `T`.
- Each circle `∂D_i` (`i >= 1`) lies in `T` and is connected, so it lies in `A` or in `B`.
- Put `A* = A ∪ ⋃{D_i : ∂D_i ⊂ A}`, and define `B*` likewise. Then `V = A* ⊔ B*`, since a
  point of `V` not in `T` lies in some `int D_i`.

`A*` is closed in `V`. Let `x ∈ V` be a limit of points `x_k ∈ A*`. After passing to a
subsequence, one of three cases holds.

1. **All `x_k` lie in one `D_i` with `∂D_i ⊂ A`.** Then `x ∈ D_i ⊂ A*`, since `D_i` is closed.
2. **All `x_k` lie in `A`.**
   - If `x ∈ T`, then `x ∈ A`, since `A` is closed in `T`.
   - If `x ∉ T`, then `x` lies in some open `int D_j`, which is disjoint from `T` and hence from
     `A`. That contradicts `x_k -> x`.
3. **`x_k ∈ D_{i_k}` with the `i_k` pairwise distinct and `∂D_{i_k} ⊂ A`.** Then
   `diam D_{i_k} -> 0`. Choosing `y_k ∈ ∂D_{i_k} ⊂ A` gives `y_k -> x`, and case 2 applies.

By symmetry `B*` is closed too. So `V` is a disjoint union of two nonempty closed sets, which
contradicts connectedness. Hence `T` is connected, and `C_0` is a peripheral circle.

Peripheral circles are defined topologically, so the chosen homeomorphism carries `C_0` to a
peripheral circle `C` of `∂G`.

## Step 2: its stabilizer

- By Kapovich--Kleiner Theorem 8(2), `P := Stab_G(C)` is a quasiconvex subgroup of `G` with
  `∂P = C`.
- By the sentence ending their Section 4, `P` is, modulo a finite normal subgroup, a cocompact
  Fuchsian group in `Isom(H^2)`. That is, there is a finite normal `K ⊴ P` with `P/K` isomorphic
  to a cocompact discrete subgroup of `Isom(H^2)`.

## Step 3: conclusion

By `finite-by-cocompact-fuchsian-groups-are-virtually-surface`, `P` has a finite-index subgroup
`Sigma ≅ pi_1(S)`, with `S` closed orientable of genus at least `2`.

Since `P` is quasiconvex in `G`, the same claim gives that `Sigma` is quasiconvex in `G`.
