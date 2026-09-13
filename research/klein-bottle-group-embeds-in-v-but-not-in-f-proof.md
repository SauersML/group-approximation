---
rg: 2
id: klein-bottle-group-embeds-in-v-but-not-in-f-proof
kind: route
title: An explicit copy of the Klein bottle group in T, and bi-orderability of F
target: klein-bottle-group-embeds-in-v-but-not-in-f
requires: []
---

**Normal form.** In `K = <a, b | b a b^{-1} = a^{-1}>` the subgroup `<a>` is
normal, and `K` is the semidirect product `Z ⋊ Z` in which `b` acts on
`<a> ≅ Z` by inversion. So every element has a unique form `a^m b^n` with
`m, n` in `Z`.

**1. Torsion-free and solvable.** The homomorphism `K → Z` with `a ↦ 0` and
`b ↦ 1` sends `a^m b^n` to `n`, so an element with `n ≠ 0` has infinite
order, and `a^m` with `m ≠ 0` has infinite order in `<a> ≅ Z`. `K` is an
extension of `Z` by `Z`, hence solvable, and a solvable group has no
non-abelian free subgroup.

**2. An embedding into `T`.** View `T` as the group of orientation-preserving
homeomorphisms of the circle `[0,1]/(0 ~ 1)` that are piecewise linear with
finitely many breakpoints, all dyadic, and slopes powers of 2. Maps compose
right to left. Fix any nontrivial `t` in Thompson's group `F`, for instance
`x_0`. It has infinite order because `F` is torsion-free. Write `L = [0, 1/2]`
and `R = [1/2, 1]`, with the affine maps `λ(x) = x/2` from `[0,1]` onto `L`
and `ρ(x) = (1 + x)/2` from `[0,1]` onto `R`. Define:

- `A = λ t λ^{-1}` on `L` and `A = ρ t^{-1} ρ^{-1}` on `R`;
- `B = ρ λ^{-1}` from `L` onto `R`, and `B = λ t ρ^{-1}` from `R` onto `L`.

`A` fixes `0`, `1/2` and `1`, and it is PL with dyadic breakpoints and slopes
powers of 2, so `A` is in `F`. `B` sends `0 ↦ 1/2`, the right end of `L` to
`1 ≡ 0`, `1/2 ↦ λ(t(0)) = 0` and `1 ↦ λ(t(1)) = 1/2`, so it is a well-defined
orientation-preserving homeomorphism of the circle, PL with dyadic breakpoints
and slopes powers of 2: `B` is in `T`.

*Relation.* `B^{-1} = λ ρ^{-1}` on `R` and `B^{-1} = ρ t^{-1} λ^{-1}` on `L`.
On `L`, `B A B^{-1} = (λ t ρ^{-1})(ρ t^{-1} ρ^{-1})(ρ t^{-1} λ^{-1})
= λ t^{-1} λ^{-1}`, which is `A^{-1}` on `L`. On `R`,
`B A B^{-1} = (ρ λ^{-1})(λ t λ^{-1})(λ ρ^{-1}) = ρ t ρ^{-1}`, which is `A^{-1}`
on `R`. So `a ↦ A`, `b ↦ B` defines a homomorphism `K → T`.

*Injectivity.* `B^2 = λ t λ^{-1}` on `L` and `B^2 = ρ t ρ^{-1}` on `R`. When
`n` is odd, `A^m B^n` maps the interior of `L` into `R`, so it is nontrivial.
When `n = 2k`, `A^m B^{2k}` is `λ t^{m+k} λ^{-1}` on `L` and
`ρ t^{k-m} ρ^{-1}` on `R`. It is the identity only if `t^{m+k} = t^{k-m} = 1`,
that is `m + k = k − m = 0`, so `m = k = 0`. So the homomorphism is injective,
and `<A, B> ≤ T ≤ V` is a copy of `K`.

**3. Bi-orderability.** Under a bi-invariant order, `g > 1` implies
`h g h^{-1} > 1`. In `K`, `a ≠ 1` and `b a b^{-1} = a^{-1}`, so whichever of
`a`, `a^{-1}` is positive has a negative conjugate: `K` is not bi-orderable.

`F` is bi-orderable. For `f ≠ 1` in `F` let `p_f = inf { x : f(x) ≠ x }`, so
`p_f < 1`. Since `f` is PL and fixes `p_f`, on some `[p_f, p_f + ε)` it is
`x ↦ p_f + μ_f (x − p_f)`, and `μ_f ≠ 1` by the choice of `p_f`. Let `P` be the
set of `f ≠ 1` with `μ_f > 1`.

- `f^{-1}` has `p_{f^{-1}} = p_f` and `μ_{f^{-1}} = 1/μ_f`, so `F \ {1}` is the
  disjoint union of `P` and `P^{-1}`.
- `P` is closed under products. For `f, g` in `P` with `p_f < p_g`, `fg`
  agrees with `f` just right of `p_f` and fixes `[0, p_f]`. With `p_g < p_f`,
  `fg` agrees with `g` just right of `p_g`. With `p_f = p_g = p`, the germ of
  `fg` at `p` has slope `μ_f μ_g > 1`.
- `P` is invariant under conjugation. For `h` in `F`, `h f h^{-1}` fixes
  `[0, h(p_f)]` pointwise, and its right germ at `h(p_f)` has slope `μ_f`,
  because the right derivatives of `h` at `p_f` and of `h^{-1}` at `h(p_f)`
  are reciprocal.

So `P` is the positive cone of a bi-invariant order on `F`. A subgroup of a
bi-orderable group is bi-orderable, so no subgroup of `F` is isomorphic to `K`.
