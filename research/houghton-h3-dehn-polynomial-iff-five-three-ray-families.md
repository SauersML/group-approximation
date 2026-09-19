---
rg: 2
id: houghton-h3-dehn-polynomial-iff-five-three-ray-families
kind: claim
title: "The Dehn function of H_3 is polynomially equivalent to the areas of five explicit linear-length three-ray relation families"
artifacts:
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
distinct_from:
  houghton-group-h3-has-polynomial-dehn-function: that asserts a polynomial bound for H_3, which is open; this is an established two-sided reduction of that bound to five explicit families of words of linear length, with loss x^6.
  houghton-dehn-polynomially-equivalent-to-commutation-area: that reduces to commutators [z, α] over all centralizing words z; this reduces, for n = 3, to five fixed shapes (one far commutation, one reroute, three edge commutations), each a single word per scale.
  houghton-h3-five-three-ray-families-have-polynomial-area: that is the open statement that the five families have polynomial area; this is the equivalence.
---

Work in `H_3` with the finite presentation `P` of §0 of
`research/artifacts/zp-houghton-pours-2026-09-17.md` (for `n = 3`). Use its notation:

- `λ_xy`, `τ_x = ((x,1),(x,2))`, `D^u_x(k) = λ_xu^k τ_x λ_ux^k`;
- a fixed route function `c` on the rays `{1,2,3}`, and the edge words `Ed(e)` of §4.

Define five families of null-homotopic words:

| family | word | length |
|---|---|---|
| `F_3(k)` | `[τ_x, D^(c(x))_x(k)]` | `4k + 4` |
| `R_3(k)` | `D^u_x(k) · D^v_x(k)^(-1)`, with `{x,u,v} = {1,2,3}` | `4k + 2` |
| `B_3(i,j)` | `[Ed(t_x(i)), Ed(t_y(j))]`, with `x != y` | `4(i+j) - 4` |
| `C_3(j)` | `[Ed(σ_{x,y}), Ed(t_z(j))]`, with the two edges vertex-disjoint | `4j + 4` |
| `D_3(j)` | `λ_wz · Ed(t_x(j)) · λ_zw · Ed(t_x(j))^(-1)`, with `{x,z,w} = {1,2,3}` | `4j` |

Let `Φ(k)` be the largest area of a member with all indices `<= k`. Then there is a
constant `C` with

```text
Φ(L) <= δ_(H_3)(C L)        and        δ_(H_3)(L) <= C L^6 ( Φ(L + C) + L )
```

for all `L >= 1`. In particular `δ_(H_3)` is polynomially bounded if and only if `Φ`
is, and `Φ(k) ≼ k^d` with `d >= 1` gives `δ_(H_3)(x) ≼ x^(6+d)`.
