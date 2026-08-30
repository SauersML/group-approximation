---
rg: 2
id: stw12-diagonal-crossed-product-tensor-host-proof
kind: route
title: Embed the diagonal crossed product into the tensor product of its cyclic factor crossed products
target: stw12-periodic-factor-decomposable-actions-are-af-embeddable
requires:
  - brown-af-automorphism-crossed-product-equivalence
  - stw12-periodic-actions-over-af-embeddable-algebras
artifacts:
  - research/artifacts/stw12-periodic-factor-decomposition-audit-2026-08-30.md
---

Write

```text
D_B=B rtimes_beta Z,       D_C=C rtimes_gamma Z,
```

and denote their canonical implementing unitaries by `s` and `t`.  The
coefficient embedding `b |-> b tensor 1_C` and the implementing unitary of
`D` give a covariant homomorphism

```text
j:D_B -> D.                                                   (PF1)
```

It is faithful.  On finite Fourier sums the canonical coefficient
expectations satisfy `E_D j = j E_(D_B)`, and both reduced expectations are
faithful.  Thus stable finiteness of `D` implies stable finiteness of `D_B`.
Brown's theorem then makes `D_B` AF-embeddable.

There is also a diagonal covariant representation

```text
Delta:D -> D_B tensor_min D_C,
Delta(b tensor c)=b tensor c,
Delta(u)=s tensor t,                                      (PF2)
```

where `u` implements `beta tensor gamma`.  This map is faithful as well.
Indeed, for every finite Fourier sum,

```text
(E_(D_B) tensor E_(D_C)) Delta = Delta E_D.               (PF3)
```

Every nonzero Fourier mode is killed in `(PF3)`, while `Delta` is faithful
on `B tensor_min C`.  If `Delta(x)=0`, applying `(PF3)` to `x*x` gives
`Delta(E_D(x*x))=0`; coefficient faithfulness and faithfulness of `E_D`
then give `x=0`.  Thus no faithfulness assertion about the tensor product
expectation is needed.  Equivalently, `(PF2)` is the
subgroup crossed-product inclusion associated to the diagonal subgroup
`Z -> Z direct_sum Z`; no tensor-product surjectivity is asserted.

Since `C` is AF-embeddable and `gamma` is outer-periodic,
`stw12-periodic-actions-over-af-embeddable-algebras` makes `D_C`
AF-embeddable.  Choose embeddings

```text
D_B -> F_B,         D_C -> F_C
```

with `F_B,F_C` AF.  Minimal tensor products preserve injectivity, and
`F_B tensor_min F_C` is AF.  Composing `(PF2)` with these two embeddings
therefore embeds `D` into an AF algebra.  We have proved `1=>2=>3`.
The implications `3=>4=>1` are standard for unital C-star algebras, while
`3=>2` also follows from `(PF1)`.  This proves all four equivalences.

For the Problem XII specialization, write the AF algebra as an inductive
limit of finite-dimensional algebras.  Then

```text
B tensor_min C = lim_k (B_k tensor_min C),
```

and each stage is a finite direct sum of matrix algebras over `C`.  Hence
the tensor product is AH whenever `C` is AH.  If `C` has real rank zero, so
do all stages, and real rank zero passes to C-star inductive limits.  Thus
`B tensor_min C` has exactly the coefficient regularity required in Problem
XII.
