---
rg: 2
id: jnvwy-exact-weyl-support-proof
kind: route
title: Use the perfect Pair and Magic-Square checks to translate every Pauli-Z atom
target: jnvwy-perfect-introspection-forces-full-seed-support
requires: []
---

Reduce a perfect PCC strategy to its faithful finite tracial measurement
algebra: consistency makes the reduced density commute with every measurement,
sampled edge probabilities are `tau(A_a B_b)`, and self-loop equality identifies
the two players' PVMs.  The synchronous commuting and CE cases give the same
algebra directly.

For the Pauli PVMs on `H=F_q^M`, form their binary character observables
`X(v),Z(v)`.  Point--Pauli consistency identifies the tested characters
`v=r ind_m(u)` with Point answer parities.  When
`Tr(v dot w)=0`, the Pair checks identify the two parities with commuting
marginals of one PVM.  When `Tr(v dot w)=1`, the Magic-Square checks and exact
rigidity identify them with its anticommuting `Variable_1,Variable_5`
observables.  Hence the mixed Weyl relation holds on all tested vectors.

Those vectors span `H`: at a Boolean point `y`, `ind_m(y)` is the coordinate
vector `e_y`, and its field multiples span the whole coordinate over `F_2`.
The character multiplication laws extend the Weyl relation to all of `H`.
Fourier inversion then shows

```text
X(v) P_h^Z X(v)^*=P_(h+v)^Z,
```

so every Pauli-Z atom has trace `1/|H|`.  Pauli--Sample consistency coarsens
these atoms along the coordinate projection `H->V`, giving every Sample seed
trace `1/|V|`.  Finally Intro--Sample perfectness supplies, over each seed `z`,
one positive joint answer `((L(z),a_z),(z,a_z))`.  Three seeds witnessing
failure of the affine identity for `L` give a rejected odd xor of three
positive accepted answers.  These are precisely the assertions and equations
proved in `jnvwy-perfect-introspection-forces-full-seed-support`.
