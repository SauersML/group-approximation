---
rg: 2
id: leavitt-pbh-via-cantor-module-affine-actor
kind: route
title: Let the Leavitt unit group act affinely on the Cantor module and apply the affine type (A) criterion
target: binary-leavitt-unit-group-satisfies-pbh
requires:
  - leavitt-cantor-module-semidirect-product-is-fp
  - orbit-finite-affine-actions-are-type-a
  - leavitt-algebras-l-k-1-n-are-simple
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-unit-group-finitely-presented
---

Notation as in `leavitt-cantor-module-semidirect-product-is-fp`: `R = L_(F_2)(1,2)`,
`U = R^×`, `M = C(C, F_2)`.

1. **The representation.** The maps `(s_i f)(a w) = δ_(a,i) f(w)` and
   `(t_i f)(w) = f(i w)` are `F_2`-linear on `M` (a locally constant `f` stays locally
   constant). They satisfy `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = id_M`, since
   `(s_0 t_0 f + s_1 t_1 f)(a w) = f(a w)`. So they define a unital representation
   `R → End_(F_2)(M)`.
2. **Faithful on `U`.** `R` is simple (`leavitt-algebras-l-k-1-n-are-simple`) and the
   representation is nonzero, so its kernel is `0`. Hence `U` embeds in `Aut(M)`,
   the automorphisms of the additive group `M`.
3. **Finitely many orbits.** The copy of `V` in `U`
   (`leavitt-cylinder-swaps-generate-thompson-in-el`) consists of sums
   `Σ s_(a_i) t_(b_i)` over bijections of complete prefix codes. By step 1 it acts on `M`
   by `f ↦ f ∘ φ^(-1)`, where `φ` is the prefix replacement `b_i w ↦ a_i w`. `V` is
   transitive on proper nonempty clopen subsets of `C`, so the `V`-orbits on `M` are
   `{0}`, `{1}` and the indicators of proper nonempty clopen sets. `U`-orbits are unions
   of `V`-orbits, so there are at most three.
4. **Finite generation.** `U` is finitely presented
   (`leavitt-unit-group-finitely-presented`), in particular finitely generated.
5. **Type (A).** With `M ⋊ U` finitely presented
   (`leavitt-cantor-module-semidirect-product-is-fp`), steps 2–4 give the three
   conditions of `orbit-finite-affine-actions-are-type-a`, item 3. So the affine action
   of `M ⋊ U` on `M` is of type (A), and `U <= M ⋊ U` embeds in a group admitting an
   action of type (A).
