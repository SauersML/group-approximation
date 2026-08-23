---
rg: 2
id: exact-code-tuples-gauge-centralize-every-pvm
kind: claim
title: Every finite PVM is gauge-equivalent to a refinement of an exact code-character PVM
distinct_from:
  multicharacter-pvm-alignment-modulo-simultaneous-gauge: that is the quantitative approximate statement with raw pair energy and terminal rounded labels; this is the exact zero-defect rank-transport endpoint and permits a far gauge.
  pvm-overlap-polar-matches-large-labeled-carriers: that constructs a near-identity unitary from large diagonal overlap; this needs no overlap and uses only exact character multiplicities.
---

ESTABLISHED.  Let `R_1,...,R_L` be commuting reflections in `M_d(C)` and
let `(p_c)` be their joint character PVM, so

```text
R_i=sum_c (-1)^(c_i)p_c.
```

For every finite PVM `(f_a)` there are refinements

```text
f_a=sum_c q_(a,c)
```

(zero summands allowed) and one unitary `U` such that, with
`g_(a,c)=Uq_(a,c)U*`,

```text
g_(a,c)<=p_c,                                           (ECG1)
sum_(a,c)g_(a,c)=I.                                    (ECG2)
```

In particular the transported coarse PVM `(Uf_aU*)` commutes with every
`R_i`, and the refined leaves are scalar code-character blocks.  No
operator-smallness, overlap margin, bound on the number of characters, or
smallness of the original pinching displacement is required.  The gauge
may be far from the identity.

This exact theorem explains both sides of the terminal recycling example.
Fixed signing can turn a nonzero character into the trivial one, but a
coherent kernel labeling followed by a far simultaneous gauge restores the
original character multiplicities exactly.  The unresolved analytic
problem is to make this rank transport quantitative when the raw tuple and
the terminal character labels are only approximate, without first paying
the unknown pinching displacement.

