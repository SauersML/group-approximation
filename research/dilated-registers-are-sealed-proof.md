---
rg: 2
id: dilated-registers-are-sealed-proof
kind: route
title: The copy-invariant twist is independent of the register; a split point of the coding forbids small twists of either sign, so the twist is locally constant and the register output ignores the other coordinates; then run the cylinder chains of the one-coordinate proof
target: dilated-registers-are-sealed
requires:
  - one-coordinate-registers-admit-no-dilation
---

Lane proof (bh-free-16, 2026-09-18). Notation as in the claim. Write `F(z, w) = t(z, w)_r` and `f = π∘t − dπ`.
All arcs are short, and `R/Z`-values near a point are compared through small real lifts.

## Step 0. The fibres of π_0

Call `v ∈ R/Z` *split* if `π_0^-1(v)` has at least two points, and let `Σ` be the set of split values. We use four facts.
- **`Σ` is countable**, since `π_0` is injective off a countable set.
- **`Σ` is dense.** Every endpoint of the shadow of a proper cylinder is split: the fibre meets the cylinder and its
  complement.
- **Split fibres are pairs.** Let `v ∈ Σ`.
  - For any fibre point `y` and any small cylinder `N ∋ y`, the shadow `π_0(N)` is a finite union of arcs containing
    `v`.
  - If `v` were interior to one such arc, a second fibre point with a disjoint neighbourhood would give two disjoint
    clopen sets whose shadows overlap in an arc. That contradicts injectivity off a countable set.
  - So every fibre point is one-sided. `π_0` is onto near `v` on both sides, so the fibre is exactly `{y^L, y^R}`,
    where small neighbourhoods of `y^L` map into `[v − ε, v]` and those of `y^R` into `[v, v + ε]`.
- **Unsplit points are two-sided.** If `v' ∉ Σ` and `π_0^-1(v') = {z}`, then `v'` is interior to the shadow of every
  cylinder around `z`. Otherwise values just beyond `v'` would come from outside the cylinder, and a limit point
  would give a second fibre point.

## Step 1. f is locally independent of the register

This is the first part of Step 1 of `one-coordinate-registers-admit-no-dilation-proof`, which uses only (R), the
invariance `f(q_a k) = f(k)` and continuity. On a neighbourhood `Z × W_0` of any point we therefore have
`f(z, w) = f(w)`, and
```
π_0(F(z, w)) = d·π_0(z) + f(w).                                   (1)
```

## Step 2. Both kinds of image point occur

Fix `Z × W_0` as in Step 1, with `Z` a small cylinder, and fix `w_0 ∈ W_0`. Put `c = f(w_0)` and `F_0 = F(·, w_0)`.
`J = interior(d·π_0(Z) + c)` is a nonempty open set.

**(i) Unsplit points go to unsplit values.**
- Let `v' ∈ π_0(Z)` be unsplit, with fibre `{z}`, and suppose `v = dv' + c ∈ Σ`.
- By Step 0 there are `z_k → z` with `π_0(z_k) ↓ v'`, and `z'_k → z` with `π_0(z'_k) ↑ v'`.
- By (1), `π_0(F_0(z_k)) ↓ v` strictly and `π_0(F_0(z'_k)) ↑ v` strictly, and both sequences converge to
  `F_0(z) ∈ {y^L, y^R}`.
- `y^L` has no nearby points with values `> v`, and `y^R` none with values `< v`. This is a contradiction.

**(ii) Split points go to both kinds of fibre point.**
- **Choosing `v'`.** Take `v ∈ Σ ∩ J`, which exists since `Σ` is dense, and `v' ∈ π_0(Z)` with `dv' + c = v`. By (i),
  `v'` is split, with fibre `{z^L, z^R}`.
- **Both points lie in `Z`.** `v'` is interior to `π_0(Z)`. If `z^R ∉ Z`, points of `Z` with values slightly above
  `v'` would accumulate on `z^L`, which is left-sided. So `z^R ∈ Z`, and likewise `z^L ∈ Z`.
- **`F_0(z^L) = y^L`.** Approach `z^L` through points with values `< v'`. Their images have values `< v`, so the limit
  `F_0(z^L)` cannot be `y^R`.
- **`F_0(z^R) = y^R`** by the symmetric argument.

## Step 3. f is locally constant

- Let `w_n → w_0` in `W_0` and put `c_n = f(w_n) − c`, a small real number.
- **`c_n <= 0` eventually.** By continuity of `t`, `F(z^L, w_n) → y^L`, so for large `n` these points lie in a
  neighbourhood of `y^L` whose values are `<= v`. By (1) their values are `v + c_n`.
- **`c_n >= 0` eventually**, from `F(z^R, w_n) → y^R` in the same way.
- So `f(w_n) = f(w_0)` for all large `n`, and `f` is constant near `w_0`.

## Step 4. The register output ignores the other coordinates

- For `w` near `w_0`, both `F(·, w)` and `F_0` satisfy `π_0 ∘ F(·, w) = dπ_0 + c` on `Z`, by (1) and Step 3.
- **Agreement on a dense set.** At every `z` with `dπ_0(z) + c ∉ Σ` the fibre is a single point, so
  `F(z, w) = F_0(z)`. The excluded `z` form a countable set, since `Σ` is countable and fibres are countable. So the
  good `z` are dense in `Z`.
- **Agreement everywhere.** Both maps are continuous, so `F(·, w) = F_0`.
- **The partition.** By compactness, finitely many such boxes cover `K`. Refine them to a clopen box partition
  `B_i = Z_i × W_i` with `F = φ_i ∘ pr_r` on `B_i` and `f ≡ f_i`. This is item 1.
- **The rotations.** For `q_a` the twist is the constant `a`, so Steps 2 and 4 run with `d = 1` and `c = a`. They give
  the same sealed form, with `π_0 ∘ ψ = π_0 + a`.

## Step 5. Arithmetic under the cellular hypothesis

This is Steps 2–3 of `one-coordinate-registers-admit-no-dilation-proof`, run inside `C_r` alone.

**Constants.**
- Let `n_0` exceed the depths of the finitely many cylinders of the almost-automorphism pieces of the `φ_i`, and of
  the partition `{Z_i}`.
- Choose `n_0` also so large that every cylinder of depth `>= n_0` has a shadow of diameter `< 1/(2d)`.
- Let `E` be the finite set of shadow endpoints of cylinders of depth `< n_0`, and `F = {f_i}`.
- Let `L ⊆ R` be the subgroup generated by `1`, lifts of `E` and lifts of `F`. It is finitely generated, so
  `L ∩ Q = (1/M) Z`.

**Chains.**
- **The starting cylinder.** Let `Z` be a cylinder with `μ(Z) = Leb π_0(Z) > 0`, and `y ∈ ∂π_0(Z)`. If
  `depth(Z) < n_0`, then `y ∈ E`.
- **One step.** Otherwise `Z ⊆ Z_i` for some `i`, and `Z` lies inside one piece of `φ_i`. So `Z' = φ_i(Z)` is a
  cylinder with `π_0(Z') = D_d(π_0 Z) + f_i`. `D_d` is injective on arcs of length `< 1/(2d)`, so
  `∂π_0(Z') = d·∂π_0(Z) + f_i` and `μ(Z') = d·μ(Z)`.
- **The chain stops.** Masses grow by the factor `d`, and deep cylinders have mass `< 1/(2d)`. So after `k` steps the
  depth is `< n_0`.
- **Conclusion.** `d^k y + Σ d^(k−1−j) f_(i_j) ∈ E`, hence `d^k ỹ ∈ L`.

**Rotations.**
- For `a ∈ A`, take a deep cylinder `Z` inside one almost-automorphism piece of a register map `ψ` of `q_a`, with
  `0 < μ(Z) < 1`, and a boundary point `y` of its shadow.
- `ψ(Z)` is a cylinder with shadow `π_0(Z) + a`, so `y + a` is a boundary point of that shadow.
- The chains give `d^K ỹ ∈ L` and `d^K(ỹ + ã) ∈ L`, so `d^K a ∈ L ∩ Q = (1/M) Z`, and `a ∈ (1/M) Z[1/d]`. This is
  item 2. ∎

## Remarks

- **What item 1 uses.** Only continuity of `t`, the copy-invariance of `f`, (R), and the split-point structure of the
  coding. It never uses what `t` does to the other coordinates. The finiteness and cellularity of the host enter only
  in Step 5.
- **Blocks.** For a block `R` of coordinates carrying `π_0 : C_R → R/Z` with the same hypotheses, Steps 0–4 are
  unchanged. Step 5 fails in general, because block maps may shrink one side of a box while growing another.
- **Calibration.** Take the binary register of `Z[1/2]` in coordinate 2 of `2V`, dilated by the inverse baker map
  `u(x, y_0 y) = (y_0 x, y)`. Its register output `σ(y)` reads only `y`, with twist `0`, and it is almost-automorphic.
  Then `E ⊆ Z[1/2]/Z` and `M = 1`: `BS(1,2)` survives, as it must.
