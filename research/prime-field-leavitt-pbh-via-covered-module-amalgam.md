---
rg: 2
id: prime-field-leavitt-pbh-via-covered-module-amalgam
kind: route
title: Amalgamate the finitely presented Cantor-module extension of V with a covered generating set of the F_p Leavitt unit group
target: prime-field-leavitt-unit-groups-satisfy-pbh
requires:
  - binary-leavitt-unit-group-satisfies-pbh
  - odd-prime-leavitt-unit-groups-are-fp-and-covered
  - higman-thompson-cantor-module-products-are-fp
  - amalgamated-module-extensions-are-fp
  - orbit-finite-affine-actions-are-type-a
  - leavitt-algebras-l-k-1-n-are-simple
---

For `p = 2` use `binary-leavitt-unit-group-satisfies-pbh`. Let `p` be odd, `R = L_(F_p)(1,2)`,
`U = R^x`, `C = {0,1}^N`, and `M = C(C, F_p)` with `(s_i f)(a w) = δ_(a,i) f(w)` and
`(t_i f)(w) = f(i w)`. Write `χ_B` for the indicator of a clopen set `B`, and `[w]` for a cone.

1. **Faithful action.** `M` is a nonzero unital `R`-module, and `R` is simple
   (`leavitt-algebras-l-k-1-n-are-simple`), so `R` acts faithfully. So `U <= Aut(M)`.
2. **The sub-extension.** The standard copy of Thompson's `V` in `U` acts by precomposition,
   so `M ⋊ V` is finitely presented by `higman-thompson-cantor-module-products-are-fp` with
   `n = 2`, `A = F_p`.
3. **Premise.** By `odd-prime-leavitt-unit-groups-are-fp-and-covered`, `U` is finitely
   presented and `U = <V, x_1, ..., x_r>`, where each `x_j` is an elementary transvection
   `1 + μ s_a t_b` (`a`, `b` incomparable, `μ ∈ F_p`) or a diagonal unit
   `λ s_a t_a + (1 - s_a t_a)` (`λ ∈ F_p^x`).
4. **Covering data.** Fix `x_j` and a complete prefix code `P` containing the words it uses.
   Put `c(h, k) = s_a h t_a + s_b h t_b + Σ_(p ∈ P ∖ {a,b}) s_p k_p t_p` for `h, k_p ∈ V`, or
   `s_a h t_a + Σ_(p ≠ a) s_p k_p t_p` in the diagonal case.
   - *These lie in `V`.* Each is the prefix replacement acting by `h` on the tails of `[a]`
     (and `[b]`) and by `k_p` on the tails of `[p]`.
   - *They commute with `x_j`.* Since `t_b s_a = t_a s_b = t_p s_a = t_p s_b = 0` and
     `t_a s_a = t_b s_b = 1`, both `c x_j` and `x_j c` equal `c + μ s_a h t_b` in the
     transvection case. In the diagonal case both equal
     `λ s_a h t_a + Σ_(p ≠ a) s_p k_p t_p`.
   - *Their translates generate `M`.* `M` is generated as a group by the elements `λ χ_([p]A)`
     with `λ ∈ F_p^x`, `p ∈ P`, and `A` a nonempty clopen. Also `c·χ_([p]A) = χ_([p] k_p(A))`,
     and similarly with `h` on `[a]`, `[b]`. `V` is transitive on proper nonempty clopen sets
     (item 4 of `leavitt-cantor-module-fp-via-thompson-amalgam`). So the finite set
     `{λ χ_([p]A') : λ ∈ F_p^x, p ∈ P, A' ∈ {C, [0]}}` has translates generating `M`.
5. **Finite presentation.** Steps 2–4 are the hypotheses of `amalgamated-module-extensions-are-fp`,
   so `M ⋊ U` is finitely presented.
6. **Finitely many orbits.** `f ∈ M` determines the ordered partition `(f^(-1)(λ))_(λ ∈ F_p)`.
   Two such partitions with the same set of nonempty labels are `V`-equivalent: split cones
   until corresponding pieces have equally many cones, then match cones. So `V`, hence `U`, has
   at most `2^p - 1` orbits on `M`.
7. **Type (A).** `U` is finitely generated. By `orbit-finite-affine-actions-are-type-a`, the
   affine action of `M ⋊ U` on `M` is of type (A), and `U <= M ⋊ U`. ∎
