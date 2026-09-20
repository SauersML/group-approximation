---
rg: 2
id: algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier
kind: claim
title: Every infinite Z^2-minimal subset of a power of Ledrappier's shift projects onto an infinite minimal subset of Ledrappier's shift itself; so if Ledrappier's shift has only finite minimal subsets (FL, a Furstenberg-type question in which no free group appears), algebraic T1 fails on every Ledrappier power for every F, and a T1 set forces an infinite minimal N ⊆ X_L with a minimal self-joining J obeying a Zariski-dense family of linear equations {a z_1 + b z_2 : (z_1, z_2) ∈ J} = c_0 N
distinct_from:
  char-2-benoist-quint-needs-the-homogeneous-form: that reduces the measure crux (BQ_2') to an infinite translation stabilizer; this finds a sufficient condition for killing algebraic T1 that involves neither the free group nor measures, namely that Ledrappier's shift itself has only finite minimal subsets.
  free-minimal-triangle-permutive-sft-exists: that conjectures every nonempty sub-SFT of Ledrappier's shift has a periodic point; (FL) is the stronger statement for all closed invariant subsets, and it is the one that controls T1.
  algebraic-t1-sets-carry-free-distal-commutator-actions: that constrains the free-group action on a T1 set; this shows every row projection of a T1 set is itself an infinite minimal subset of Ledrappier's shift, and turns the free group into linear equations on one self-joining.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - algebraic-t1-sets-carry-free-distal-commutator-actions
  - char-2-benoist-quint-needs-the-homogeneous-form
  - algebraic-rows-carry-rigid-free-commutants-but-never-minimality
```

**ESTABLISHED (lane bh-bq2, 2026-09-19; lane proof, elementary; not independently reviewed; no priority
claimed).** The question (FL) itself is **OPEN**.

## Setting

- `X_L = Hom(A, F_2)` with `x(v + e_2) = x(v) + x(v + e_1)`, so `σ_(e_2) = 1 + σ_(e_1)` on `X_L`.
- `A`, `X = X_L^2 = Hom(A^2, F_2)`, `F ≤ GL_2(A)` and `Γ = F × Z^2` are as in
  `char-2-benoist-quint-needs-the-homogeneous-form`.
- For `w ∈ A^2`, let `π_w : X → X_L` be `π_w(x)(c) = x(cw)`. It is the dual of `c ↦ cw` and commutes with the
  shifts.
- **(FL):** every `Z^2`-minimal subset of Ledrappier's shift `X_L` is finite. Equivalently:
  - every uniformly recurrent point of `X_L` is periodic;
  - every nonempty closed `Z^2`-invariant subset of `X_L` contains a periodic point.

## Statement

1. **Projection.** If `M ⊆ X_L^n` is closed, infinite and `Z^2`-minimal, some coordinate projection of `M` is an
   infinite minimal subset of `X_L`. Hence **(FL) implies that no power `X_L^n` has an infinite minimal subset,
   and algebraic T1 fails on every Ledrappier power, for every group `F`**, with no use of measures.
2. **What the free group adds.** Let `F` be torsion-free and not virtually solvable (for example free of rank 2), and let `M ⊆ X` be an infinite,
   `Z^2`-minimal, `F`-invariant set.
   - For every `w ≠ 0`, `N_w := π_w(M)` is an infinite minimal subset of `X_L`, and `N_(γ^T w) = N_w` for
     `γ ∈ F`.
   - Fix `w ≠ 0`, `γ_0 ∈ F` with `w' = γ_0^T w` independent of `w`, and `N = N_w`. Then
     `P = (π_w, π_(w')) : X → X_L^2` is onto with finite kernel, and `J = P(M) ⊆ N × N` is a minimal
     self-joining with both projections equal to `N`.
   - There is `c_0 ∈ A \ {0}` such that, writing `c_0 γ^T w = a_γ w + b_γ w'` with `a_γ, b_γ ∈ A`,
     `{a_γ z_1 + b_γ z_2 : (z_1, z_2) ∈ J} = c_0 N` for every `γ ∈ F`.
   - The points `[a_γ : b_γ]` form an infinite `F`-orbit in `P^1(k)`.
3. **(FL) is at least the sub-SFT conjecture.** (FL) implies the refutation form conjectured in
   `free-minimal-triangle-permutive-sft-exists`: every nonempty sub-SFT of `X_L` has a periodic point. It is
   consistent with that node's exhaustive search.
4. **Partial evidence: regular almost automorphic minimal sets.**
   - Let `N ⊆ X_L` be an infinite minimal set that is a regular almost 1-1 extension of its maximal
     equicontinuous factor `(K, ρ)`: the points of `K` with one-point fibre have full Haar measure.
   - Then every accumulation point `(c, d)` of `(2^k ρ(e_1), 2^k ρ(e_2))` in `K^2` satisfies
     `f(z + d) = f(z) + f(z + c)` almost everywhere, and `(0, 0)` is **not** an accumulation point.
   - So such `N` cannot live over a 2-adic odometer, nor over a rotation whose doubling orbit returns near `0`.
     Compare the Toeplitz rows with 2-power periods, already dead in `free-minimal-triangle-permutive-sft-exists`;
     they are killed by the same Frobenius identity.

## Proof

**1.** Each coordinate projection is continuous and commutes with the shifts, so it maps `M` onto a minimal
subset of `X_L`. If all `n` of them are finite, `M` lies in their finite product.

**2.**
- *Row projections are infinite.* `π_w(M)` is minimal. If it is finite, it is one periodic orbit, contained in
  the group of `mZ^2`-periodic points, which is dual to `A/I_m` with `I_m = (s^m − 1, t^m − 1) ≠ 0`. Then for
  `c ∈ I_m`, the character `cw` of `X` vanishes on `M`. By item 3 of
  `algebraic-t1-sets-carry-free-distal-commutator-actions`, `cw = 0`, so `w = 0`.
- *Invariance under `F`.* `π_w(γ·x)(c) = x(γ^T cw) = π_(γ^T w)(x)(c)`, so `π_w ∘ γ = π_(γ^T w)`, and
  `π_w(M) = π_w(γM) = π_(γ^T w)(M)`.
- *Choice of `w'`.* `F^T` fixes no line, so some `γ_0^T` moves the line of `w`.
- *The isogeny.* `P` is dual to `(c, c') ↦ cw + c'w'`. That map is injective, with image `L = Aw + Aw'` of
  finite index in `A^2`, so `P` is onto with finite kernel. `J = P(M)` is minimal, with projections `N_w` and
  `N_(w') = N_w`.
- *The linear equations.* Take `c_0 ≠ 0` with `c_0 A^2 ⊆ L`. Then
  `c_0 π_(γ^T w) = a_γ π_w + b_γ π_(w')`, and the left side maps `M` onto `c_0 N_(γ^T w) = c_0 N`.
- *Infinite orbit.* `[a_γ : b_γ]` is the line of `γ^T w` in the basis `(w, w')`. Its `F`-orbit is infinite,
  because a subgroup of `PGL_2(k)` that is not virtually solvable has no finite orbit on `P^1(k)`: the stabilizer of a finite
  orbit has finite index and fixes a point, so it is solvable, making `F` virtually solvable.

**3.** Every nonempty sub-SFT contains a minimal subset. Under (FL) that subset is a periodic orbit.

**4.**
- *The function `f`.* Let `Z ⊆ K` be the invariant, full-measure set of points with a one-point fibre `{x_z}`.
  `z ↦ x_z` is continuous on `Z`. Put `f(z) = x_z(0)`, so `x_z(v) = f(z + ρ(v))`, and the Ledrappier relation
  reads `τ_b f = f + τ_a f` almost everywhere, with `a = ρ(e_1)`, `b = ρ(e_2)`.
- *Frobenius.* Translations of `F_2`-valued functions commute, so in characteristic 2
  `(τ_b + 1 + τ_a)^(2^k) = τ_(2^k b) + 1 + τ_(2^k a)`. It also kills `f`.
- *Limits.* Translation is continuous in measure. So along `(2^(k_j) a, 2^(k_j) b) → (c, d)` we get
  `τ_d f = f + τ_c f`. If `(c, d) = (0, 0)`, this reads `f = f + f = 0` almost everywhere. Then `x_z = 0` for
  almost every `z`, so `0 ∈ N` and `N = {0}`: a contradiction. ∎

## Why the isometric-tower route does not apply directly

- **`M` is not distal.** Furstenberg's structure theorem needs a distal system, and an infinite subshift never
  is. Two points agreeing on a box of radius `n`, recentred at their nearest disagreement, converge to distinct
  `x', y'` agreeing on an open half-plane, and shifts deep into that half-plane make them close.
- **Nothing forces an isometric layer.**
  - The uniformly distal pairs `(x, gx)`, `g ∈ [F, F]`, lie in fibres over the maximal equicontinuous factor.
    Such pairs can come from an isometric layer, like the fibre flip of a minimal `Z/2` group extension.
  - But for a non-distal system the structure theory (proximal–isometric–weakly mixing towers) does not force
    fibre-preserving automorphisms to act through an isometric layer, and automorphisms need not lift to the
    towers.
  - Even an isometric layer would not produce translations: the translation stabilizer of a T1 measure is
    finite anyway (item 3 of the distal node).
- **The replacement.** The reduction above removes the free group entirely: the whole algebraic T1 question on
  Ledrappier powers sits over (FL).

## Why Furstenberg's ×2 ×3 argument does not transfer verbatim

- In the `S`-adic model `X_L = K_S/A`, differences of close points of an infinite minimal set can be blown up
  along the expanding place of a suitable `σ_v`, for example `v = (−2, 1)`, which expands the place `s = 0` and
  contracts the other two.
- That produces nonzero differences in the leaf `F_2((s))`. On the leaf the shifts act by `×s`, a contraction,
  and `×(1+s)`, an isometry whose orbit closures in the unit group `1 + sF_2[[s]]` are copies of `Z_2` inside an
  infinite-dimensional pro-2 group.
- So small differences are **not** spread densely. This is the same subfield/non-lacunarity failure that makes
  Berend's theorem false here (Einsiedler 2004, cited in `char-2-benoist-quint-needs-the-homogeneous-form`).
  But the known non-algebraic closed invariant sets are unions of Frobenius subgroups, which contain `0`; they
  are not counterexamples to (FL).

## Lesson for general BH

- **The free group is not the hard part.** On Ledrappier powers the algebraic face of (RA_free) reduces, with no
  free group and no measures, to a Furstenberg-type question for one explicit zero-entropy `Z^2`-SFT: does
  `X_L` have an infinite minimal subset?
- **If it does not,** algebraic T1 is dead outright.
- **If it does,** the free group then demands a self-joining of that minimal set closed under a Zariski-dense
  family of linear equations.
- **Where the question now lives.** It has moved from homogeneous dynamics over function fields into the
  topological dynamics of three-dot rules, where Kari–Moutot, Cyr–Kra and the triangle-permutive nodes already
  have tools.
