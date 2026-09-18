---
rg: 2
id: leavitt-germ-traces-satisfy-frobenius
kind: claim
title: Over F_2 the isotropy-class traces of the binary Leavitt algebra satisfy a Frobenius identity, so a unit with 2^k-th roots for infinitely many k has every germ trace zero
distinct_from:
  unit-roots-divide-centralizer-rank: that forces divisibility of the centralizer rank by a root order in any algebra; this is a trace identity special to characteristic two and to the Cuntz groupoid, and it constrains the element itself, not its centralizer.
  leavitt-units-are-not-conjugate-to-diagonal-copies: its Attempts record Tr(phi(y)) = 2 Tr(y) = 0; this computes the trace of a square, Tr(x^2) = F(Tr(x)), and applies to roots rather than diagonal copies.
  thompson-units-have-few-roots-in-leavitt-unit-group: that bounds roots of Thompson units through centralizer rank; this gives a second, trace-based bound that holds for every unit.
---

**ESTABLISHED** (proof: `leavitt-germ-traces-satisfy-frobenius-proof`). Not independently reviewed.

## Setting

`R = L_(F_2)(1,2) = A_(F_2)(G)` is the Steinberg algebra of the Cuntz groupoid
`G = {(x, m−n, y) : σ^m x = σ^n y}` on `X = {0,1}^N`, with `s_α t_β = 1_(Z(α,β))` and
`Z(α,β) = {(αz, |α|−|β|, βz)}`. A nontrivial isotropy element is `(p, k, p)` with `k ≠ 0` and `p`
eventually periodic. Its conjugacy class `C` is determined by the sign of `k` and a **necklace** `ν`
(a nonempty binary word up to rotation, not necessarily primitive): `(βγ^∞, |γ|, βγ^∞)` has class `(+, [γ])`,
and its inverse has class `(−, [γ])`. The monomial `s_α t_β` meets the isotropy in at most one point:
`(βγ^∞, |γ|, βγ^∞)` if `α = βγ`, its inverse if `β = αγ`, and none otherwise.

For a nontrivial class `C` put `Φ_C(f) = Σ_(g ∈ C) f(g)`, a finite sum. Write `C^2` for the class of squares, so
`(±, [γ])^2 = (±, [γγ])`, and `Tr(f) = Σ_C Φ_C(f)·[C]` in the `F_2`-space with basis the nontrivial classes.

## Statement

1. **Traces.** Each `Φ_C` is a trace: `Φ_C(fh) = Φ_C(hf)`. The `Φ_C` separate `HH_0(R) = R/[R,R]`, so
   `[R,R] = ⋂_C ker Φ_C`. The class `[1]` is `0`.
2. **Frobenius identity.** For every `f in R` and every nontrivial class `C'`:
   `Φ_(C')(f^2) = Φ_C(f)` if `C' = C^2`, and `Φ_(C')(f^2) = 0` if `C'` is not a square class. So
   `Tr(f^2) = F(Tr f)` with `F[C] = [C^2]`, an injective linear map.
3. **Roots.** If `x = y^(2^k)` with `y in R`, then every class `(±, [ν])` with `Φ(x) ≠ 0` has `ν` a
   `2^k`-th power word. If `x` has `2^k`-th roots in `R` for infinitely many `k`, then `Tr(x) = 0`, i.e.
   `x in [R,R]`.
4. **Divisible subgroups.** If `Γ ≅ Z[1/2]` or `Γ ≅ (Q,+)` is a subgroup of `U = R^x`, then the `F_2`-span of `Γ`
   is a commutative subalgebra contained in `[R,R]`.
5. **Examples.** The north--south unit `c = s_00 t_0 + s_01 t_10 + s_1 t_11` has `Φ_((+,[0]))(c) = 1`, and `[0]` is
   not a square necklace. So `c` and all its conjugates are not squares in `R`. This is a second proof, by traces,
   of part 2 of `thompson-units-have-few-roots-in-leavitt-unit-group` for `k = 2`.

## Use

Part 4 is a necessary condition for `rationals-embed-in-binary-leavitt-unit-group`: every element of a copy of
`(Q,+)` in `U`, and every finite sum of such elements, has all germ traces zero. For a Thompson unit `u_g`,
`Φ_C(u_g)` counts mod 2 the isotropy germs of `g` in class `C`, a Lefschetz-type number of its periodic points.
