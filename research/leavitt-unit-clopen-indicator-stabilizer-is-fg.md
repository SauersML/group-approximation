---
rg: 2
id: leavitt-unit-clopen-indicator-stabilizer-is-fg
kind: claim
title: The stabilizer in the binary Leavitt unit group of the indicator of a cylinder is finitely generated
distinct_from:
  leavitt-unit-group-finitely-presented: that is finite presentation of the whole unit group; this is finite generation of one point stabilizer of its linear action on the Cantor module.
  leavitt-cantor-module-semidirect-product-is-fp: that is finite presentation of the module extension; this is the one finiteness input that, by `orbit-finite-quotient-module-extensions-are-fp`, suffices for it.
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `U = R^×`, and `M = C(C, F_2)` with `R` acting by
`(s_i f)(a w) = δ_(a,i) f(w)` and `(t_i f)(w) = f(i w)`. Let `χ = χ_[0]` be the
indicator of the cylinder `[0]`. Then `Stab_U(χ) = {u ∈ U : u·χ = χ}` is finitely
generated.

## Why it matters

- By `leavitt-cantor-module-fp-via-indicator-stabilizer` it gives finite presentation
  of `M ⋊ U`.
- By `leavitt-pbh-via-clopen-orbit-action` it gives permutational Boone--Higman for `U`
  directly, through the action of `U` on the orbit of `χ`, with no module needed.

## Attempts

1. **Calibration inside `V`.** For Thompson's `V <= U`
   (`leavitt-cylinder-swaps-generate-thompson-in-el`), `Stab_V(χ)` is the setwise
   stabilizer of `[0]`, which is `V_[0] × V_[1] ≅ V × V`, finitely generated. This says
   nothing about `U`: `U` acts linearly, not by homeomorphisms, so `Stab_U(χ)` contains
   non-geometric units, e.g. `1 + s_μ t_ν` with `[μ]`, `[ν]` disjoint from `[0]`, and
   finite generation does not follow from the geometric part. Not settled.
