---
rg: 2
id: prime-field-leavitt-chen-vector-action-type-a-proof
kind: route
title: Lift the line actions to vectors with the central scalars and count the finitely many orbits of pairs
target: prime-field-leavitt-units-act-with-type-a-on-chen-vectors
requires:
  - leavitt-units-act-two-transitively-on-chen-module-lines
  - leavitt-square-units-act-two-transitively-on-chen-lines
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - type-a-action-gives-boone-higman-for-subgroups
---

**Setup.** Let `K = F_p`, `U` and `W` as in the target, `δ` the base vector, `G = U / K^×`,
and `S = W ∖ {0}`. The four clauses of type (A) are those of
`type-a-action-gives-boone-higman-for-subgroups`. The line-action facts used below are
items 1–3 of `leavitt-units-act-two-transitively-on-chen-module-lines` (one factor) and of
`leavitt-square-units-act-two-transitively-on-chen-lines` (tensor square).

1. **Faithful.**
   - If `u ∈ U` fixes every vector, it fixes every line, so `u = λ ∈ K^×` by item 1.
   - Then `λ δ = δ` forces `λ = 1`.
2. **Finitely presented.**
   - `G` is finitely presented by `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, and
     `K^×` is a finite central subgroup of `U`.
   - An extension of a finite group by a finitely presented group is finitely presented.
     Present `U` by generators lifting those of `G`, plus the elements of `K^×`, with
     these relations:
     - the multiplication table of `K^×`;
     - the commutation of `K^×` with the lifted generators;
     - for each relator of `G`, the equation expressing its lift as an element of `K^×`.
3. **Stabilizers.**
   - *`U` is transitive on `S`.* Given `v, w ∈ S`, item 2 gives `u` with `u[v] = [w]`,
     so `uv = λw`. Then `λ^(-1) u`, with `λ^(-1) ∈ K^× ⊂ U`, sends `v` to `w`.
   - *Finitely generated.* By item 3, `Stab_U(δ)` is finitely generated. Every point
     stabilizer is conjugate to it.
4. **Pair orbits.** Let `{v, w} ⊂ S` with `v ≠ w`.
   - *Dependent pairs.* If `w = λ v` with `λ ∈ K^× ∖ {1}`, transitivity moves `v` to `δ`.
     So the orbit contains `{δ, λδ}`, and there are at most `p − 2` such orbits.
   - *Independent pairs.* Fix a second base vector `δ_2 = δ_x` with `x` a point other than
     the base point. By item 2, some `u` sends `([v], [w])` to `([δ], [δ_2])`. So `{v, w}`
     lies in the orbit of `{αδ, βδ_2}` for some `α, β ∈ K^×`, and there are at most
     `(p − 1)^2` such orbits.
   - *Total.* There are finitely many orbits of two-element subsets.

So the action is of type (A). `∎`
