---
rg: 2
id: repeated-squaring-tau-firewall-proof
kind: route
title: Exhibit an exponentially ill-conditioned trivial presentation and locate the missing curvature estimate
target: repeated-squaring-and-tau-do-not-supply-the-moving-basin
requires: []
---

The relations of `(RST1)` and the terminal relation imply successively

```text
a_L=1, a_(L-1)=a_L^2=1, ..., a_0=1,
```

so the presented group is trivial.  For `(RST2)`,

```text
A_(i+1)^2=exp(i pi/2^i)=A_i,
```

so every squaring row has zero defect.  The elementary chord bound
`|exp(it)-1|<=|t|` gives `(RST3)`, while `A_0=-1` gives `(RST4)`.  Since the
trivial group has only the identity representation, this tuple is distance
two on the marked generator from every exact representation despite total
max-relator defect at most `pi 2^(-L)`.

The same construction can be adjoined to any presentation of any finite
group `H`; the exact group remains `H`, and the restriction to the original
generators has exactly the same Cayley graph and spectral gap.  Hence no
argument whose inputs are only that gap and `O(L)` bounded-length rows can
exclude the scalar tuple.

Finally, the Selberg averaging argument uses the exact identity

```text
beta(gh)=beta(g)beta(h).                               (RSF1)
```

For raw presentation tuples the failure of `(RSF1)` along a word is bounded
by the number of relator 2-cells needed to compare its paths, not by the
one-dimensional Cayley spectral gap.  The squaring chain is the elementary
model: all local transition rows vanish while the terminal curvature of
size `2^(-L)` transports backward to order-one marked displacement.  This
proves the claimed logical separation between expansion and the missing
presentation basin.

