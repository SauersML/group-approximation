---
rg: 2
id: stw82-stabilize-essential-counterexample-proof
kind: route
title: Stabilize the separable essential counterexample without changing dimensions
target: stw82-counterexamples-reduce-to-stable-essential-extensions
requires:
  - stw82-every-counterexample-reflects-to-a-separable-subextension
  - stw82-every-counterexample-essentializes
---

The two required reductions first give a separable counterexample

```text
0 -> L -> E -> Q -> 0
```

with `L` essential in `E`.  Tensor it minimally with the compact operators
`K` on a separable infinite-dimensional Hilbert space.  Nuclearity of `K`
preserves exactness, so

```text
0 -> L tensor K -> E tensor K -> Q tensor K -> 0             (1)
```

is an extension.  All three terms are separable and stable.

For every C*-algebra `C`,

```text
dim_nuc(C tensor K)=dim_nuc(C).                               (2)
```

One inequality follows by tensoring nuclear-dimension approximations with
the zero-dimensional AF algebra `K`.  The reverse inequality follows because
`C tensor e_11` is a hereditary corner of `C tensor K` isomorphic to `C`;
nuclear dimension does not increase on hereditary subalgebras.  This is also
the stable-invariance/full-hereditary-corner statement in
Winter--Zacharias, [Corollary 2.8](https://arxiv.org/abs/0903.4914).

Essentiality also survives.  Suppose `x in E tensor K` annihilates
`L tensor K`.  For matrix units `(e_ij)` of `K`, every matrix coefficient

```text
x_ij=(id tensor omega_ij)(x)
```

annihilates `L` on both sides: multiply `x` by elementary tensors
`l tensor e_jk` and slice.  Since `L` is essential, each `x_ij` is zero.
Matrix coefficient functionals separate `E tensor K`, hence `x=0`.
Therefore `L tensor K` is essential in `E tensor K`.

Equation (2) says that stabilization changes none of the three nuclear
dimensions.  Hence (1) remains a counterexample.  Conversely, the stable
essential extensions are a subclass of all extensions, proving the stated
equivalence.

