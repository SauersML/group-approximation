---
rg: 2
id: full-v4-radical-crossed-product-proof
kind: route
title: Apply Clifford--Mackey theory to the transitive radical translation action
target: full-v4-radical-crossed-product-has-one-common-latent-coordinate
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - three-radical-twist-crossed-products-have-uniform-scale
---

The automorphisms `tau_1,tau_2` multiply packet generators by central signs,
so they commute and generate `V_4`.  On a forbidden selector sector they
translate the four radical characters by a basis of the dual radical plane.
The action is therefore free and transitive.  The crossed product of four
copies of `M_d` by this translation action is the full transformation-group
algebra `M_(4d)`, with `d=D_0/2`; this proves `(VRC3)`.

Restriction to `<s_i>` splits the four-point orbit into its two cosets modulo
the corresponding order-two translation.  Each coset produces one
`M_(2d)=M_(D_0)` simple, so the unique `M_(4d)` module restricts as one copy
of each chart simple.  The three orbit quotients are the three nonzero linear
functionals on `F_2^2`, giving `(VRC5)--(VRC6)`.

On a satisfying sector the packet algebra is one `M_(D_0)` block.  A finite
group acting on a full matrix algebra is inner.  Factoring chosen inner
implementers out of the crossed-product unitaries leaves the twisted group
algebra of `V_4` for the Mackey cocycle.  Its alternating commutator is either
trivial, giving `C^4`, or nontrivial, giving `M_2(C)`.  Tensoring with
`M_(D_0)` proves `(VRC7)`.

