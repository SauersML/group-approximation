---
rg: 2
id: kazhdan-tarski-monster-trace-conjecture-free-products-kk-proof
kind: route
title: Replace scalar witnesses by matrix witnesses with a non-integer trace window, rerun the moment-norm compactness argument, and interleave the matrix radii into the Olshanskii--Osin--Sapir relator lengths
target: kazhdan-tarski-monster-trace-conjecture-free-products-kk
requires:
  - kk-witness-counterexample-locus-is-marked-closed
  - kazhdan-torsion-free-tarski-monster-satisfies-kk
  - hyperbolic-bcc-finite-wreath-products
  - assembly-image-traces-are-integral-for-torsion-free-groups
  - free-product-kk-iff-trace-conjecture-for-factors
---

Notation as in the claim. `Tr_N` is locally constant in `N`: for `x ∈ M_n(C[F])` it depends only on
`N ∩ ⋃_i supp(x_ii)`, a finite set of words. `B_r ⊆ F` is the ball of radius `r` and
`U_r(N) = { N' : N' ∩ B_r = N ∩ B_r }`.

The scalar proofs are items A.1--A.6 of `kk-witness-counterexample-locus-is-marked-closed-proof`.
Only the changes are written out.

## Theorem M

**1. Moment formula for matrices.** On `M_n(L(G_N))` the state `tr = Tr_N / n` is faithful, normal
and tracial. For `x ∈ M_n(C[F])` and `T = λ_N(x*x)`, the spectral measure of `T` for `tr` is a
probability measure with support `spec T`. As in A.1,

```text
‖λ_N(x)‖^2 = sup_k ( Tr_N((x*x)^k) / n )^(1/k),
```

so `N ↦ ‖λ_N(x)‖` is lower semicontinuous, and `{N : ‖λ_N(x)‖ > R}` is enumerated by the clopen
evidence `Tr_N((x*x)^k) > n R^(2k)`.

**2. `P_ω` is closed and `Π^0_1`.** Let `A ∈ Q` with `A ≥ Σ_{i,j} ‖a_ij‖_{ℓ^1(F)}`. Since
`a = Σ e_ij ⊗ a_ij` and `‖e_ij ⊗ z‖ = ‖z‖`, we get `‖λ_N(a)‖ ≤ A` for every `N`.

*Gap.* With `y = (a - c)^2 - ε^2` and `β = (A + |c|)^2 + ε^2 ∈ Q`, exactly as in A.2 the gap
condition is `‖λ_N(β - y)‖ ≤ β`. This set is closed by item 1, with complement enumerated by
`Tr_N((β - y)^(2k)) > n β^(2k)`.

*Trace window.* Pick `q_j ∈ Q[t]` with `|q_j - 1_{t<c}| ≤ 1/j` on `J = [-A, c-ε] ∪ [c+ε, A]`. On
the gap set, `spec λ_N(a) ⊆ J`, so `‖q_j(λ_N(a)) - χ‖ ≤ 1/j` with `χ = χ_(-∞,c)(λ_N(a))`. Since
`Tr_N` is `n` times a state,

```text
| Tr_N(q_j(a)) - Tr_N(χ) | ≤ n/j .
```

The number `Tr_N(q_j(a))` is rational, because `a` is self-adjoint with Gaussian-rational
entries and `q_j` has rational coefficients. Hence

```text
P_ω = Gap_ω ∩ ⋂_j { N : dist( Tr_N(q_j(a)), Z ) ≥ δ - n/j }.
```

- `⊆`: if `dist(Tr_N χ, Z) ≥ δ`, the estimate gives `dist(Tr_N q_j(a), Z) ≥ δ - n/j`.
- `⊇`: on `Gap_ω` the conditions give `dist(Tr_N χ, Z) ≥ δ - 2n/j` for every `j`, hence `≥ δ`.

Each set on the right is clopen or closed. Membership of a cylinder in the complement is decided
by a finite rational computation. So `P_ω` is closed and `Π^0_1`.

**3. Exhaustion.**
- *If `N ∈ P_ω`:* `χ_(-∞,c)(λ_N(a))` is a continuous function of `λ_N(a)` on its spectrum, so it
  is a projection of `M_n(C*_r G_N)`. Its trace is not an integer.
- *Conversely,* let `p ∈ M_n(C*_r G_N)` be a projection with `τ_*(p) ∉ Z`. Every class of
  `K_0` is a difference of classes of projections, so integrality fails on `K_0` iff it fails on
  some such `p`.
  1. `Q[i][G_N]` is dense in `C*_r(G_N)` (the reduced norm is at most the `ℓ^1` norm), so there is
     `x ∈ M_n(Q[i][G_N])` with `‖x - p‖ < 1/4`. Then `b = (x + x*)/2` is self-adjoint and
     `‖b - p‖ < 1/4`.
  2. For self-adjoint operators, `spec b` lies in the `‖b - p‖`-neighbourhood of `spec p ⊆ {0,1}`.
     So `spec b ⊆ (-1/4, 1/4) ∪ (3/4, 5/4)`, and `(1/4, 3/4)` is a gap.
  3. Put `e = χ_(1/2,∞)(b)`. Then `‖e - b‖ < 1/4`, so `‖e - p‖ < 1/2 < 1`. Two projections at
     distance `< 1` are unitarily equivalent, so `τ_*(e) = τ_*(p)`.
  4. `χ_(-∞,1/2)(b) = 1_n - e` has trace `n - τ_*(p)`, which is not an integer.
  5. Lift `b` entrywise to `ã ∈ M_n(Q[i][F])` and put `a = (ã + ã*)/2`, so `λ_N(a) = b`. Take
     `c = 1/2`, `ε = 1/4`, and a rational `δ ∈ (0, dist(τ_*(p), Z)]`. Then `N ∈ P_ω`.

So the TR locus is `M_d \ ∪_ω P_ω`, a countable intersection of open sets.

**4. Radius.** Let `G_N` be in the TR locus, so `N ∉ P_ω`.
- If the gap fails, then `Tr_N((β - y)^(2k)) > n β^(2k)` for some `k`.
- If the gap holds, `Tr_N(χ) ∈ Z`. For `j > 2n/δ` the estimate gives
  `dist(Tr_N q_j(a), Z) ≤ n/j < δ - n/j`.

Either evidence is a finite computation supported in some `B_r`, and it holds for every
`N' ∈ U_r(N)`. That `r` is `r(N, ω)`.

**5. Fast limits.** The proof of A.6 uses only the cylinder property of item 4 and the
exhaustion of item 3. So it applies verbatim: `N_∞ = ⋃ N_i` lies in `U_{r_i}(N_{i-1})` for every
`i`, hence outside `P_{ω_k}` for every `k`, hence in the TR locus.

## Theorem T

**Stages are in the TR locus.** Let `H` be a torsion-free hyperbolic group. By
`hyperbolic-bcc-finite-wreath-products`, `H` satisfies Baum--Connes with coefficients, so its
assembly map is surjective. By `assembly-image-traces-are-integral-for-torsion-free-groups`, the
trace of every class in the assembly image is an integer. Hence `τ_*(K_0(C*_r H)) ⊆ Z`. For
torsion-free `H` this is also `lueck-surjective-assembly-traces-lie-in-lambda-g` with
`Λ^H = Z`.

**Interleaving.** Run the construction of `kazhdan-torsion-free-tarski-monster-satisfies-kk-proof`,
§4, with one change. Enumerate the matrix witnesses `ω_1, ω_2, ...` instead of the scalar ones, and
use the matrix radii of item 4:

```text
r_i = max( r_{i-1},  max_{k ≤ i} r(N_{i-1}, ω_k) ),     r_0 = 0.
```

- Each radius is finite because `G(i-1)` is torsion-free hyperbolic, hence in the TR locus.
- Choose the relator length `ρ_i` last, so that `λ_i(1 - 23μ_i)ρ_i - 2c_i - 4ε_i ≥ r_i`.
  This is allowed by (I2) of that proof.
- By the Corollary of §3 there, `N_i ∩ B_{r_i} = N_{i-1} ∩ B_{r_i}`, which is exactly what item 5
  consumes.

So the limit `Q` is in the TR locus. Item 1 of Theorem T is unchanged from that proof: torsion-free,
proper subgroups cyclic, graded small cancellation. They depend only on the lower bounds on `ρ_i`
required by Olshanskii--Osin--Sapir, and one more lower bound is compatible with them. Trivial
projections follow from integer traces, because `τ` is faithful and a projection `e ≠ 0, 1` has
`τ(e) ∈ (0,1)`.

## Corollary

1. `Q` and `H` are nontrivial and torsion-free, so neither is `C_2`. By Corollary 1 of
   `free-product-kk-iff-trace-conjecture-for-factors`, `C*_r(Q * H)` has no projection other than
   `0, 1` iff `τ_*K_0(C*_r Q) ⊆ Z` and `τ_*K_0(C*_r H) ⊆ Z`. The first is Theorem T. The second
   is the hypothesis, and it holds for `Z` and for torsion-free hyperbolic groups by the stage
   argument above.
2. **Properties of `Q * Z` over an `Sp(n,1)` lattice.** `Q` is an infinite Kazhdan group without
   `F_2`, as in §5 of `kazhdan-torsion-free-tarski-monster-satisfies-kk-proof`.
   - A free product of torsion-free groups is torsion-free.
   - `Q * Z` maps onto `Z`, and an infinite Kazhdan group has finite abelianization, so `Q * Z` is
     not Kazhdan.
   - The Haagerup property passes to subgroups, and an infinite Kazhdan group does not have it.
   - `Q` is torsion-free, non-abelian and not `Z`, so it is not virtually cyclic: a torsion-free
     virtually cyclic group is trivial or `Z`. Every subgroup of a hyperbolic group is virtually
     cyclic or contains `F_2` (Gromov), so `Q * Z` is not hyperbolic. `Q` is finitely generated,
     and by Tits a finitely generated linear group is virtually solvable or contains `F_2`. `Q` is
     not virtually solvable, since it is an infinite Kazhdan group, hence non-amenable. So
     `Q * Z` is not linear.
   - A free product of two nontrivial groups other than `C_2 * C_2` is acylindrically
     hyperbolic. The last bullet of the claim then quotes Corollary B of
     `fractional-matrix-trace-gives-projection-in-g-star-z`.

## Calibration

- For `n = 1` the witnesses and the window `dist(·, Z) ≥ δ` reduce to the scalar window
  `[δ, 1-δ]`, because a trace of a `1 × 1` projection lies in `[0,1]`.
- The method proves nothing false for groups with torsion. For `Z/m`, `m ≥ 2`, the witness
  `a = (1/m) Σ_{j<m} s^j` is the averaging projection, `χ_(-∞,1/2)(a) = 1 - a` has trace
  `1 - 1/m`, and so `Z/m ∈ P_ω` with `c = 1/2`, `ε = 1/4`, `δ = 1/m`. Theorem M makes no claim
  there, because such groups are not in the TR locus.
- The monster stages must be torsion-free. The interleaving never uses torsion-freeness of the
  limit directly, only of the stages through integer traces.
