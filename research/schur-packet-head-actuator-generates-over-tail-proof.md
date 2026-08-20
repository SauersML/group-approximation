---
rg: 2
id: schur-packet-head-actuator-generates-over-tail-proof
kind: route
title: Twist the missing packet coordinate by a disjoint Toeplitz head root
target: schur-packet-head-actuator-generates-over-tail
requires:
  - toeplitz-head-tail-unital-self-embedding
  - toeplitz-tail-plus-one-swap-generates
  - predicate-rank-gate-doubles-restriction-multiplicity
---

First embed `B_f` faithfully into a constant lower-unitriangular block
`rho_0(B_f)<=EL_r(F_2)<=EL_r(sigma(T))`.  The extra-generator exponent is a
homomorphism

```text
chi:B_f -> C_2,       chi(p_m)=1,                         (SAT3)
```

with every other packet generator, including the center, sent to zero.  This
is immediate from the class-two presentation: commutators lie in the center,
and the `p_m` exponent is additive in packet normal form.

On matrix coordinates disjoint from the constant packet block, put
`h=e_ij(s)`.  It is an involution because the coefficient ring has
characteristic two.  Define

```text
iota(g)=rho_0(g) h^(chi(g)).                               (SAT4)
```

The two blocks commute, so `(SAT3)` makes `(SAT4)` a homomorphism.  Projection
to the constant block recovers the faithful `rho_0`, hence `iota` is faithful.
The character vanishes on `B_f^Q`, proving
`iota(B_f^Q)<=alpha(Gamma)`.

Moreover `rho_0(p_m)` already belongs to `alpha(Gamma)`, so `(SAT4)` recovers
the isolated actuator exactly:

```text
h=rho_0(p_m)^(-1)iota(p_m).
```

Weyl elements over `1 in sigma(T)` move `h` to every root position.  Since

```text
T=<sigma(T),s>
```

by `(TSG3)`, the standard elementary commutator relation
`[e_ij(a),e_jk(b)]=e_ik(ab)` shows that these roots generate `EL_r(T)`.
This proves the second part of `(SAT2)`.

The accompanying MSI experiment independently checks the more economical
single-block realization obtained by scaling the missing packet coordinate by
`s` and all opposite/central coordinates by `e_2=sigma^2(f)`: it verifies all
`128^2` products, faithfulness, and the full matrix-algebra generation of
head/tail truncations of sizes three through ten.  The disjoint character
twist above is used in the proof because it makes actuator isolation literal.
