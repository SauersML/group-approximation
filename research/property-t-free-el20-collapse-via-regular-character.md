---
rg: 2
id: property-t-free-el20-collapse-via-regular-character
kind: route
title: Reblock a surviving representation to a nontrivial MF character, Diracize it, and use simplicity to reach the regular character
target: property-t-free-el20-full-mf-radical
requires:
  - leavitt-regular-character-not-mf-without-property-t
  - torsion-normal-generator-mf-character-criterion
  - character-diracization-limit
  - binary-leavitt-elementary-group-is-simple
---

Let `H=EL_20(R)` and suppose `Rad_MF(H)!=H`.  The involution `z=x_13(q)`
normally generates `H` (simplicity, `binary-leavitt-elementary-group-is-simple`),
so `torsion-normal-generator-mf-character-criterion` yields a nontrivial MF
character `chi` of `H`: a pointwise limit of normalized traces of
operator-norm asymptotic unitary representations `V_k`.

For each `j`, the maps `V_k^(tensor j) tensor conj(V_k)^(tensor j)` are
again operator-norm asymptotic unitary representations, with normalized
trace `|tr V_k|^(2j)`.  Hence `|chi|^(2j)` is an MF character for every
`j`, and a diagonal choice of `j` and `k` shows the pointwise limit
`1_(K_chi)`, `K_chi={g:|chi(g)|=1}`, is an MF character
(`character-diracization-limit`).  The set `K_chi` is a normal subgroup.
If `K_chi=H` then `|chi|=1` everywhere, so `chi` is a one-dimensional
unitary character of the perfect group `H`, hence `chi=1`, contradicting
nontriviality.  Since `H` is simple, `K_chi=1` and `1_(K_chi)=delta_e`.

Thus `delta_e` is an MF character of `H`, contradicting
`leavitt-regular-character-not-mf-without-property-t`.  Hence
`Rad_MF(H)=H` by an argument with the required provenance.

Conversely, if `delta_e` were an MF character, the witnessing `V_k` would
satisfy `||V_k(g)-1||_2 -> sqrt 2` for `g!=1`, so they would be asymptotically
injective and `H` would be MF.  The two statements are therefore
equivalent, and neither direction uses Property `(T)`.
