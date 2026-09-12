---
rg: 2
id: paired-frame-fixed-kernel-polynomial-clock-no-go
kind: claim
title: The paired-frame kernel admits no opposite polynomial shears
artifacts:
  - experiments/paired_frame_kernel_polynomial_stabilizer.py
distinct_from:
  alternating-free-ring-shears-have-strict-degree-drift: that constructs degree growth in the full two-dimensional coefficient module; this proves the opposite shear required for that growth does not preserve the paired edge group's relation kernel.
  paired-frame-hard-characters-form-forced-two-cycle: that classifies binary isomorphisms of the finite edge group; this computes which of them extend to polynomial one-parameter subgroups over F_2[x].
  one-sided-paired-frame-reverse-reservoir-collapse: that may still move the relation kernel from level to level; this rules out only a fixed scalar-extended kernel acted on by a polynomial stabilizer.
---

Let `K` be the three-dimensional relation kernel in
`wedge^2(F_2^4)` of the paired plus/minus edge group.  Among the twelve
polynomial transvections

```text
I+x E_(a,b) in GL_4(F_2[x]),   a!=b,
```

exactly four preserve `K tensor F_2[x]`:

```text
(a,b) in {(0,1),(0,3),(2,1),(2,3)}.                    (PKN1)
```

There is no opposite pair.  Moreover, every ordered product of two surviving
transvections has bounded polynomial degree under all powers; no such product
is a degree clock.

Indeed the surviving matrix units all map the odd coordinate subspace into
the even coordinate subspace.  Their pairwise products vanish, so the lifted
unipotent radical is square-zero and every element has order two in
characteristic two.  Thus the attractive product of forward and opposite
shears from `(ASD1)` cannot act on one fixed scalar-extended paired-frame edge
group.

The remaining free-root option must move the kernel itself:

```text
K_n = wedge^2(T^n) K_0,                                 (PKN2)
```

or enlarge the packet atlas.  Treating the finite frame kernel as stationary
silently recreates the order-two return.
