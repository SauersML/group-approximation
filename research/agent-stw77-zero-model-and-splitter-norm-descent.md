---
rg: 2
id: agent-stw77-zero-model-and-splitter-norm-descent
kind: claim
title: Unit-ball and splitter near-inclusion descend proper-support models
distinct_from:
  agent-stw77-zero-near-witnesses-descend-properness: that repairs splitters once their support already lies in the represented C-star algebra; this first transports an entire finite-dimensional model into that algebra.
  agent-stw77-zero-packetwise-type-i-descent-fails: that proves finite-packet approximation does not imply the required unit-ball near-inclusion.
  agent-stw77-zero-type-i-properness-does-not-descend: that proves algebra descent alone does not reflect proper infiniteness; this adds exactly the missing norm control on its witnesses.
---

Let `C subset B(H)` be a unital C-star algebra and let `E subset B(H)` be a
unital finite-dimensional C-star algebra with the same unit.  Suppose

```text
E subset_epsilon C,
0<epsilon<min(10^(-4),1/14400),                        (1)
```

where the first relation is one-sided unit-ball near inclusion.  For one
minimal projection `e_j` in each simple summand of `E`, suppose there are
`s_(j,1),s_(j,2) in e_j B(H)e_j` satisfying

```text
s_(j,k)^*s_(j,l)=delta_(k,l)e_j
```

and

```text
max_(j,k) dist(s_(j,k),C) < delta,
delta+240 sqrt(epsilon)<1/4.                           (2)
```

Then there is a unitary `v in B(H)` such that

```text
E_0=vEv^* subset C,
||v-1||<120 sqrt(epsilon),                             (3)
```

and every minimal projection of `E_0` is properly infinite in `C`.

If contractions `x_1,...,x_m in E` approximate contractions
`c_1,...,c_m in C` within `eta`, then `v x_l v^* in E_0` approximate them
within

```text
eta+240 sqrt(epsilon).                                 (4)
```

Consequently `stw77-nucdim-zero-case` follows if its faithfully represented
type-I absorbed models can be selected so that both the unit-ball defect in
`(1)` and the splitter defects in `(2)` tend to zero.  The current
nuclear-dimension-zero and type-I theorems give only finite-packet closeness
and strong-star density, respectively, so they do not supply either norm
defect.
