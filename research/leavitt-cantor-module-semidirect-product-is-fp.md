---
rg: 2
id: leavitt-cantor-module-semidirect-product-is-fp
kind: claim
title: The semidirect product of the Cantor module C(C, F_2) by the binary Leavitt unit group is finitely presented
distinct_from:
  leavitt-unit-group-finitely-presented: that is finite presentation of the unit group U alone; this is finite presentation of the extension of U by its infinitely generated Cantor module, which is strictly more.
  orbit-finite-affine-actions-are-type-a: that is the criterion turning such a finitely presented extension into a type (A) actor; this is the finiteness input the criterion needs for one module.
---

**OPEN.** Let `R = L_(F_2)(1,2)` with generators `s_0, s_1, t_0, t_1`
(`t_i s_j = δ_ij`, `s_0 t_0 + s_1 t_1 = 1`). Let `M = C(C, F_2)`, the locally constant
`F_2`-valued functions on `C = {0,1}^N`, with `R` acting by
`(s_i f)(a w) = δ_(a,i) f(w)` and `(t_i f)(w) = f(i w)`. Let `U = R^×` act on `M`
through this representation. Then `M ⋊ U` is finitely presented.

## What is known around it

- `U` is finitely presented (`leavitt-unit-group-finitely-presented`), so it is not the
  obstruction; it is a retract of `M ⋊ U`.
- `M` is generated as a `U`-group by one element `χ = χ_[0]`, because the copy of
  Thompson's `V` inside `U` (`leavitt-cylinder-swaps-generate-thompson-in-el`) acts on
  indicators of clopen sets by precomposition and is transitive on proper nonempty
  clopen sets, and indicators of clopens span `M`.
- **Candidate presentation.**
  - generators of `U` together with `χ`;
  - the relators of `U`;
  - `χ^2 = 1`;
  - commutation of `χ` with finitely many `U`-conjugates of itself (pair
    configurations of clopen sets);
  - one splitting relator `χ_[0] = χ_[00] + χ_[01]`, written with conjugates by
    prefix replacements in `V`;
  - commutation of `χ` with a finite generating set of `Stab_U(χ)`.
  This gives a finite presentation once `Stab_U(χ)` is finitely generated and these
  relators generate all others. Neither step is proved here.

**Calibration.** For `V` in place of `U`, `C(C,F_2) ⋊ V` is the centralizer in `V` of a
fixed-point-free involution (hand check), which Martínez-Pérez–Matucci–Nucinkis
(arXiv:1309.7858v2, abstract and introduction) show to be of type `F_∞`. The exact
theorem statement was not pinned; see Attempt 1 of
`decidable-groups-embed-in-orbit-finite-affine-actors`.
