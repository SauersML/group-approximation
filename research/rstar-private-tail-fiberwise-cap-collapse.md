---
rg: 2
id: rstar-private-tail-fiberwise-cap-collapse
kind: claim
title: Three occurrence-private R-star coordinates admit exact fiberwise cap collapse
distinct_from:
  isolated-rstar-context-determinizes-to-a-fano-cap: that is the local fibrewise operator construction with no compatibility assertion; this adds occurrence-privacy so the local replacements can be made simultaneously throughout an instance.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for the actual fixed hard family, whose target occurrences do not have three occurrence-private coordinates; this proves the selector only under that extra syntax.
  tracial-cap-menus-are-central-core-partitions: that rules out postselecting a supplied trace by noncentral compression; this changes occurrence-private generators inside the same algebra and performs no compression.
  rstar-cap-support-is-one-character-row: that characterizes cap support once obtained; this constructs cap support by retaining one binary observable and replacing three private ones.
---

**ESTABLISHED CONDITIONAL SELECTOR.**  Consider a finite `R_*` instance in
which every context is ordered as

```text
c=(x_1,x_2,x_3,x_4),                                    (PTC1)
```

where `x_1` may occur elsewhere but each of `x_2,x_3,x_4` occurs in no other
context.  Every perfect CE representation of this instance can be replaced,
inside the same ambient finite von Neumann algebra, by a perfect CE
representation whose support in every context has at most two points and is
therefore a Fano cap.

More explicitly, if `A_1,...,A_4` are the commuting context involutions and

```text
P_a=(1+(-1)^a A_1)/2,       a in F_2,                  (PTC2)
```

choose one allowed tuple

```text
r^a=(a,r^a_2,r^a_3,r^a_4) in R_*                     (PTC3)
```

for every nonzero `P_a`, and replace the private observables by

```text
Ahat_j=sum_(a:P_a!=0) (-1)^(r^a_j) P_a,   j=2,3,4.    (PTC4)
```

The new local support is contained in the one- or two-point set of selected
tuples.  Consequently there is a nonzero character `lambda_c` satisfying

```text
lambda_(c,2)x_2+lambda_(c,3)x_3+lambda_(c,4)x_4=1      (PTC5)
```

on that support, or equivalently the corresponding product of the three new
observables is `-I`.

The tempting annihilator calculation instead produces a nonzero `mu` with
`mu(r^a_2,r^a_3,r^a_4)=0`.  That homogeneous row has operator sign `+I` and
is not `(PTC5)`: its three nonzero solutions form a Fano line.  The correct
`-I` character follows from the at-most-two-point support, by choosing a
functional taking value one on the selected nonzero triples.

Because the replaced variables are occurrence-private, `(PTC4)` may be
performed simultaneously in every context without changing any shared
observable.  Every modified generator belongs to the original algebra, so
Connes embeddability passes to the generated subalgebra.

The local construction and the `-I` character calculation are isolated in
`isolated-rstar-context-determinizes-to-a-fano-cap`.  The only additional
content here is that occurrence-privacy makes those local replacements
simultaneously legal.
